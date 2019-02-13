%% -*- mode: erlang; erlang-indent-level: 4; indent-tabs-mode: nil -*-
%% -------------------------------------------------------------------
%%
%% Copyright (c) 2016 Basho Technologies, Inc.
%%
%% This file is provided to you under the Apache License,
%% Version 2.0 (the "License"); you may not use this file
%% except in compliance with the License.  You may obtain
%% a copy of the License at
%%
%%   http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing,
%% software distributed under the License is distributed on an
%% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
%% KIND, either express or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
%%
%% -------------------------------------------------------------------

-module(rebar_raw_resource).
%
% For efficiency in production use, we don't have a dependency on rebar
% itself, so the behaviors this module implements aren't always visible.
%
-ifdef(rrr_develop).
-behaviour(provider).
-behaviour(rebar_resource).
-endif.

% the dependency resource type identifier associated with this resource.
-define(RTYPE,  raw).

-export([
    % provider
    do/1,
    format_error/1,
    init/2,
    % rebar_resource_v2 callbacks
    download/4,
    lock/2,
    make_vsn/2,
    needs_update/2,
    % pre-rebar3 3.7.0 rebar_resource callbacks
    init/1,
    download/3,
    make_vsn/1
]).

% For development only - you *really* don't want this defined!
%-define(RRR_DEBUG,  true).

-define(else,   'true').
-define(is_min_tuple(Var, Min),
    erlang:is_tuple(Var) andalso erlang:tuple_size(Var) >= Min).
-define(is_rec_type(Var, Type, Min),
    ?is_min_tuple(Var, Min) andalso erlang:element(1, Var) =:= Type).
-define(is_rec_type(Var, Type), ?is_rec_type(Var, Type, 1)).
-define(mod_error(Error),   {'error', {?MODULE, Err}}).

-ifdef(RRR_DEBUG).
-define(RRR_STATE(Field),   debug_state(State, Field)).
-define(throw_error(Error), debug_call_stack(), erlang:error({?MODULE, Error})).
-else.
-define(RRR_STATE(Field),   'ok').
-define(throw_error(Error), erlang:error({?MODULE, Error})).
-endif.

%
% Implementation Notes:
%
% ALL functions are spec'd!
% Specs for exported functions MAY be more specialized than their specifying
% behaviors.
%
% We maintain mappings in the process dictionary between:
%
% - resource type => implementing module
% - dependency name => resource type and repository location
% - repository location => resource type and dependency name
%
% These mappings are updated whenever we have access to a rebar_state
% record, which isn't available during any of the resource operations other
% than download/3. Worse, if the dependency is already in place, the non-state
% needs_update/2 operation will be the first called on it, so we have to have
% set up our mapping before that. That leaves plugin initialization as the
% only chance to get the mappings set up before they're needed.
%
% At present, I don't discriminate between scopes, assuming a given dependency
% location always maps to the same name. Including the dependency's version
% selector and profile would allow complete uniqueness of mappings, but
% subsequent operations may alter the version selector, resulting in matches
% not being found. Overall, I think it's reasonable to have a constraint saying
% 'You MUST use the same name for a given dependency URL across profiles.'
%
% Because the nested resource specifiers (rightly) don't have a specified
% schema, we treat them as relatively opaque tuples where the first element is
% the type and the second element is the location.
% Old-style dependencies with a version regex immediately following the
% dependency name SHOULD be accommodated but ignored, though this aspect hasn't
% been, and isn't likely to be, rigorously tested as it's moot in rebar3.
%
% Currently, we satisfy rebar's need for an OTP application by scribbling a
% minimal app config file in <dep-path>/ebin/<dep-name>.app if there's not
% such a file already, or its equivalent source in the <dep-path>/src
% directory.
%
% It would be preferable to build the rebar_app_info record dynamically and
% insert it into the state so we didn't have to leave droppings in the
% dependency's filesystem, but some processing sequences in rebar access the
% actual file to check for changes, so it looks like the current behavior has
% to stay for the time being.
%

%% ===================================================================
%% Types - none exported
%% ===================================================================
%
% Type names have prefixes of 'rsrc_' indicating they apply to all dependency
% specs or 'this_' indicating they're specific to this resource type.
%
-ifdef(rrr_develop).
-type rebar_lock()  ::  rebar_resource:resource().
-type rebar_state() ::  rebar_state:t().
-type rsrc_loc()    ::  rebar_resource:location().
-type rsrc_ref()    ::  rebar_resource:ref().
-type rsrc_type()   ::  rebar_resource:type().
-else.
-type rebar_lock()  ::  {rsrc_type(), rsrc_loc(), rsrc_ref()}.
-type rebar_state() ::  tuple().
-type rsrc_loc()    ::  string().   % URL-ish
-type rsrc_ref()    ::  term().     % repo version specifier
-type rsrc_type()   ::  atom().
-endif.
-type keyable()     ::  atom() | binary() | list().

-type rebar_dep()   ::  {rsrc_name()} | {rsrc_name(), rsrc_spec() | rsrc_vsn()}.
-type rebar_dir()   ::  file:filename_all().
-type rebar_err()   ::  {'error', term()}.
-type rebar_rsrc()  ::  {rsrc_type(), rsrc_mod()} | rebar_resource_v2:resource().
-type rebar_vsn()   ::  {'plain', rsrc_vsn()}.

-type rsrc_dir()    ::  rebar_dir().
-type rsrc_mod()    ::  module().
-type rsrc_name()   ::  atom().
-type rsrc_spec()   ::  tuple().    % {rsrc_type(), rsrc_loc(), ...}
-type rsrc_vsn()    ::  string().

-type this_opt()    ::  atom() | {atom(), term()}.
-type this_opts()   ::  [this_opt()].
-type this_spec()   ::  {this_type(), rsrc_spec()}
                    |   {this_type(), rsrc_spec(), this_opts()}
                    |   {this_type(), rsrc_loc(), mod_ref()}.
-type this_type()   ::  ?RTYPE.

%-type map_key()    ::  name_key() | spec_key() | type_key().
%%-type name_key()    ::  {?MODULE, 'name', rsrc_name()}.    % => rsrc_type()
%%-type spec_key()    ::  {?MODULE, 'spec', rsrc_loc()}.     % => rsrc_name()
%%-type type_key()    ::  {?MODULE, 'type', rsrc_type()}.    % => module()

-record(mod_ref, {
    res     ::  rsrc_type(),
    ref     ::  rsrc_ref(),
    opt     ::  this_opts()
}).
-type mod_ref()     :: #mod_ref{}.

-record(mod_dep, {
    name    ::  rsrc_name(),
    res     ::  rsrc_type(),
    loc     ::  rsrc_loc()
}).
-type mod_dep()     :: #mod_dep{}.

-record(mod_res, {
    res     ::  rsrc_type(),
    mod     ::  rsrc_mod()
}).
-type mod_res()     :: #mod_res{}.

-record(mod_data, {
    rsrcs = []  ::  [mod_res()],
    deps  = []  ::  [mod_dep()]
}).
-type mod_data()    :: #mod_data{}.

%% ===================================================================
%% Provider API
%% ===================================================================

-spec init(State :: rebar_state()) -> {'ok', rebar_state()}.
%
% Installs the resource handler, the provider itself does nothing.
%
% This gets called repeatedly, for each profile, and in each case we want
% to prime the process environment with any info we may need later, as
% download/3 is NOT called first if the dependency is already present, and
% it's the only resource call that gets to see the rebar state.
%
% Note: This arity is the pre-rebar3 3.7.0 format of this function.
%
init(State) ->
    #mod_data{} = absorb_state(State),
    {'ok', rebar_state:add_resource(State, {?RTYPE, ?MODULE})}.

-spec init(Type :: rsrc_type(),
           State :: rebar_state()) -> {'ok', rebar_state()}.
%
% Installs the resource handler, the provider itself does nothing.
%
% This gets called repeatedly, for each profile, and in each case we want
% to prime the process environment with any info we may need later, as
% download/4 is NOT called first if the dependency is already present, and
% it's the only resource call that gets to see the rebar state.
%
% Note: This arity is the rebar_resource_v2 format of this function.
%
init(Type, State) ->
    #mod_data{} = absorb_state(State),
    {'ok', rebar_resource_v2:new(Type, ?MODULE, State)}.

-spec do(State :: rebar_state:t()) -> {'ok', rebar_state()}.
%
% Fulfills the `provider' contract, does nothing ... for now.
%
% IF there's a viable way to hook rebar's app_discovery provider, this will
% be the place to do it, but it looks like rebar really wants to see a physical
% file so there's not much we can do.
%
do(State) ->
    {'ok', State}.

-spec format_error(Error :: term()) -> iolist().
%
% Converts specified Error to a string.
% Most errors in this module are in the form {atom(), term()} and are handled
% down in the internal format_error/4 function.
%
format_error({Class, Data}) ->
    format_error('io_lib', 'format', Class, Data);

format_error(Error) ->
    io_lib:format("~p", [Error]).

%% ===================================================================
%% Resource API
%% ===================================================================

-spec download(Dest :: rsrc_dir(),
               From :: this_spec(),
               State :: rebar_state())
              -> {'ok', term()} | rebar_err().
%
% Download the specified resource using its underlying handler.
%
% Note: This arity is the pre-rebar3 3.7.0 format of this function.
%
download(Dest,
         {?RTYPE, Loc, #mod_ref{res = Res, ref = Ref, opt = Opts}},
         State) ->
    download(Dest, {?RTYPE, {Res, Loc, Ref}, Opts}, State);

download(Dest, {?RTYPE, Spec}, State) ->
    download(Dest, {?RTYPE, Spec, []}, State);

download(Dest, {?RTYPE, Spec, Opts}, State) ->
    ?RRR_STATE('state'),

    Data = absorb_state(State),
    {Res, Loc} = parse_ext_spec(Spec),
    % Do both lookups before calling the handler's download to get the
    % exception out of the way if it's coming.
    #mod_res{mod = Mod} = lookup_res(Data, Res),
    #mod_dep{name = Name} = lookup_loc(Data, Loc),
    case Mod:download(Dest, Spec, State) of
        {'ok', _} = Ret ->
            ensure_app(Dest, Mod, Name, Opts, Ret);
        Err ->
            Err
    end.

-spec download(Dest :: rsrc_dir(),
               AppInfo :: rebar_app_info:t(),
               ResourceState :: term(),
               State :: rebar_state())
              -> {'ok', term()} | rebar_err().
%
% Download the specified resource using its underlying handler.
%
% Note: This arity is the rebar_resource_v2 format of this function.
%
download(Dest, AppInfo0, ResourceState, RebarState) ->
    Name = term_to_atom(rebar_app_info:name(AppInfo0)),
    {Spec, Opts} = case rebar_app_info:source(AppInfo0) of
        {?RTYPE, Loc0, #mod_ref{res = Res0, ref = Ref, opt = Opts0}} ->
            {{Res0, Loc0, Ref}, Opts0};
        {?RTYPE, S, O} ->
            {S, O};
        {?RTYPE, S} ->
            {S, []}
    end,
    {Res, _Loc} = parse_ext_spec(Spec),
    #mod_res{mod = Mod} = lookup_res(mod_data(), Res),
    AppInfo = rebar_app_info:source(AppInfo0, Spec),
    case Mod:download(Dest, AppInfo, ResourceState, RebarState) of
        ok ->
            case lists:keytake(vsn, 1, Opts) of
                false ->
                    % because download has not put the downloaded app into
                    % its final location, configure the app dir to be the
                    % Dest provided.
                    TmpAppInfo = rebar_app_info:dir(AppInfo, Dest),
                    {plain, Vsn} = Mod:make_vsn(TmpAppInfo, []),
                    ensure_app(Dest, Mod, Name, [{vsn, Vsn} |Opts], ok);
                {value, _, _} ->
                    ensure_app(Dest, Mod, Name, Opts, ok)
            end;
        Err -> Err
    end.

-spec lock(Path :: rsrc_dir(),
           Spec :: this_spec())
          -> rebar_lock() | no_return();
          (AppInfo :: rebar_app_info:t(),
           ResourceState :: term())
          -> rebar_lock() | no_return().
%
% Pass through to the underlying resource handler.
% Note that the callback doesn't allow an error tuple to be returned, so an
% exception is our only option if we can't look up the mapping.
%
% Note: this function is common to the pre-rebar3 3.7.0 and rebar_resource_v2
% formats, and as such has heads for each.
%
%% pre-rebar3 3.7.0 format
lock(Path, {?RTYPE, Loc, #mod_ref{res = Res, ref = Prev} = Rec}) ->
    #mod_res{mod = Mod} = lookup_res(mod_data(), Res),
    {Res, Loc, Ref} = Mod:lock(Path, {Res, Loc, Prev}),
    {?RTYPE, Loc, Rec#mod_ref{ref = Ref}};

lock(Path, {?RTYPE, Spec}) ->
    lock(Path, {?RTYPE, Spec, []});

lock(Path, {?RTYPE, Spec, Opts}) ->
    {Res, _} = parse_ext_spec(Spec),
    #mod_res{mod = Mod} = lookup_res(mod_data(), Res),
    {Res, Loc, Ref} = Mod:lock(Path, Spec),
    {?RTYPE, Loc, #mod_ref{res = Res, ref = Ref, opt = Opts}};
%% rebar_resource_v2 format
lock(AppInfo, _ResourceState) ->
    {Spec, Opts} = case rebar_app_info:source(AppInfo) of
        {?RTYPE, Loc0, #mod_ref{res = Res0, ref = Ref0, opt = Opts0}} ->
            {{Res0, Loc0, Ref0}, Opts0};
        {?RTYPE, S, O} -> {S, O};
        {?RTYPE, S} -> {S, []}
    end,
    {Res, _Loc} = parse_ext_spec(Spec),
    #mod_res{mod = Mod} = lookup_res(mod_data(), Res),
    {Res, Loc, Ref} = Mod:lock(rebar_app_info:source(AppInfo, Spec), []),
    {?RTYPE, Loc, #mod_ref{res = Res, ref = Ref, opt = Opts}}.

-spec needs_update(Path :: rsrc_dir(),
                   SpecOrResourceState :: this_spec())
                  -> boolean() | no_return();
                  (AppInfo :: rebar_app_info:t(),
                   State :: rebar_state())
                  -> boolean() | no_return().
%
% Pass through to the underlying resource handler.
% Note that the callback doesn't allow an error tuple to be returned, so an
% exception is our only option if we can't look up the mapping.
%
% Note: this function is common to the pre-rebar3 3.7.0 and rebar_resource_v2
% formats, and as such has heads for each.
%
%% pre-rebar3 3.7.0 format
needs_update(Path, {?RTYPE, Loc, #mod_ref{res = Res, ref = Ref}}) ->
    #mod_res{mod = Mod} = lookup_res(mod_data(), Res),
    Mod:needs_update(Path, {Res, Loc, Ref});

needs_update(Path, {?RTYPE, Spec, _}) ->
    needs_update(Path, {?RTYPE, Spec});

needs_update(Path, {?RTYPE, Spec}) ->
    {Res, _} = parse_ext_spec(Spec),
    #mod_res{mod = Mod} = lookup_res(mod_data(), Res),
    Mod:needs_update(Path, Spec);
%% rebar_resource_v2 format
needs_update(AppInfo, State) ->
    {Mod, SourceSpec} = case rebar_app_info:source(AppInfo) of
        {?RTYPE, Loc, #mod_ref{res = Res, ref = Ref}} ->
            #mod_res{mod = M} = lookup_res(mod_data(), Res),
            {M, {Res, Loc, Ref}};
        {?RTYPE, Spec, _} ->
            {Res, _} = parse_ext_spec(Spec),
            #mod_res{mod = M} = lookup_res(mod_data(), Res),
            {M, Spec};
        {?RTYPE, Spec} ->
            {Res, _} = parse_ext_spec(Spec),
            #mod_res{mod = M} = lookup_res(mod_data(), Res),
            {M, Spec}
    end,
    Mod:needs_update(rebar_app_info:source(AppInfo, SourceSpec), State).

-spec make_vsn(Path :: rsrc_dir())
        -> rebar_vsn() | {'error', string()} | no_return().
%
% Pass through to the underlying resource handler.
% The weird error tuple spec comes from the rebar_resource behavior.
% Note: This arity is the pre-rebar3 3.7.0 format of this function.
%
make_vsn(Path) ->
    Data = mod_data(),
    #mod_dep{res = Res} = lookup_dep(Data, path_name(Path)),
    #mod_res{mod = Mod} = lookup_res(Data, Res),
    Mod:make_vsn(Path).

-spec make_vsn(Path :: rsrc_dir(),
               State :: rebar_state())
              -> rebar_vsn() | {'error', string()} | no_return().
%
% Pass through to the underlying resource handler.
% The weird error tuple spec comes from the rebar_resource behavior.
% Note: This arity is the rebar_resource_v2 format of this function.
%
make_vsn(AppInfo0, _ResourceState) ->
    Spec = case rebar_app_info:source(AppInfo0) of
        {?RTYPE, Loc0, #mod_ref{res = Res0, ref = Ref}} -> {Res0, Loc0, Ref};
        {?RTYPE, S, _} -> S;
        {?RTYPE, S} -> S
    end,
    {Res, _Loc} = parse_ext_spec(Spec),
    #mod_res{mod = Mod} = lookup_res(mod_data(), Res),
    Mod:make_vsn(rebar_app_info:source(AppInfo0, Spec), []).

%% ===================================================================
%% Internal
%% ===================================================================

-spec format_error(
    Mod :: module(), Func :: atom(), Class :: term(), Data :: term())
        -> term().
%
% Assume Mod:Func/2 accepts the same arguments as io_lib:format/2.
% The rebar_api:<loglevel>/2 functions meet this requirement, so we can define
% the error translations in one place (here) and use it throughout the module.
% Since we don't know what function is being called, we don't know what it
% returns, but the caller does.
%
format_error(Mod, Func, 'duplicate_dep_name', Name) ->
    Mod:Func("Conflicting definitions of dependency '~s'", [Name]);
format_error(Mod, Func, 'duplicate_dep_loc', Loc) ->
    Mod:Func("Conflicting dependencies at '~s'", [Loc]);
format_error(Mod, Func, 'duplicate_res_type', Res) ->
    Mod:Func("Conflicting '~s' resource definitions", [Res]);
format_error(Mod, Func, 'unmapped_dep_name', Name) ->
    Mod:Func("Unmapped dependency name '~s'", [Name]);
format_error(Mod, Func, 'unmapped_dep_loc', Loc) ->
    Mod:Func("Unmapped dependency location '~s'", [Loc]);
format_error(Mod, Func, 'unmapped_res_type', Res) ->
    Mod:Func("Unmapped resource type '~s'", [Res]);
format_error(Mod, Func, 'unrecognized_ext_spec', Spec) ->
    Mod:Func("Unrecognized dependency structure: ~p", [Spec]);
format_error(Mod, Func, Class, Data) ->
    Mod:Func("~p:~p", [Class, Data]).

% The absorb_... functions soak up whatever we care about from the state.
%
% There's a lot of code here that may be redundant and/or unused as I feel
% around trying to make sure all of the dependencies are found in each runtime
% scenario.
% Hopefully it'll all be cleaned up someday.

-spec absorb_state(State :: rebar_state()) -> mod_data() | no_return().
absorb_state(State) ->
    Data1 = mod_data(),
    Data2 = absorb_resources(Data1, rebar_state:resources(State)),
    Data3 = absorb_deps(Data2, rebar_state:get(State, 'deps', [])),
    Data4 = absorb_app_infos(Data3, rebar_state:lock(State)),
%   Data5 = absorb_profiles(Data4, rebar_state:current_profiles(State), State),
    mod_data(dump_mod_data(Data4)).

-spec absorb_app_infos(Data :: mod_data(), AppInfos :: [tuple()])
        -> mod_data() | no_return().
absorb_app_infos(Data, [AppInfo | AppInfos]) ->
    absorb_app_infos(
        absorb_dep(Data,
            rebar_app_info:name(AppInfo), rebar_app_info:source(AppInfo)),
        AppInfos);
absorb_app_infos(Data, []) ->
    Data.

-spec absorb_deps(Data :: mod_data(), Deps :: [rebar_dep()])
        -> mod_data() | no_return().
absorb_deps(Data, [Dep | Deps]) ->
    absorb_deps(absorb_dep(Data, Dep), Deps);
absorb_deps(Data, []) ->
    Data.

-ifdef(rrr_develop).
-compile({nowarn_unused_function, absorb_profiles/3}).
-spec absorb_profiles(
    Data :: mod_data(), Profiles :: [atom()], State :: rebar_state())
        -> mod_data() | no_return().
absorb_profiles(Data, [Profile | Profiles], State) ->
    absorb_profiles(
        absorb_app_infos(
            Data, rebar_state:get(State, {'parsed_deps', Profile}, [])),
        Profiles, State);
absorb_profiles(Data, [], _) ->
    Data.
-endif.

-spec absorb_resources(
    Data :: mod_data(), Resources :: [rebar_rsrc()])
        -> mod_data() | no_return().
%
% Allow for whatever may come through to handle future extensions.
%
% rebar_resource_v2 format
absorb_resources(Data, [Res | Resources]) when ?is_rec_type(Res, resource, 3) ->
    absorb_resources(
        map_res(Data, #mod_res{
            res = term_to_atom(erlang:element(2, Res)),
            mod = erlang:element(3, Res)}),
        Resources);
% pre-rebar3 3.7.0 format
absorb_resources(Data, [Res | Resources]) when ?is_min_tuple(Res, 2) ->
    absorb_resources(
        map_res(Data, #mod_res{
            res = term_to_atom(erlang:element(1, Res)),
            mod = erlang:element(2, Res)}),
        Resources);
absorb_resources(Data, [_ | Resources]) ->
    absorb_resources(Data, Resources);
absorb_resources(Data, []) ->
    Data.

-spec absorb_dep(Data :: mod_data(), Spec :: rsrc_spec())
        -> mod_data() | no_return().
%
% Accommodate dependencies with or without the rebar2 regex string.
% Be as lenient as we can about current and future structure.
%
absorb_dep(Data, Dep) when ?is_min_tuple(Dep, 2)
        andalso erlang:is_tuple(erlang:element(2, Dep)) ->
    absorb_dep(Data, erlang:element(1, Dep), erlang:element(2, Dep));
absorb_dep(Data, Dep) when ?is_min_tuple(Dep, 3)
        andalso erlang:is_tuple(erlang:element(3, Dep)) ->
    absorb_dep(Data, erlang:element(1, Dep), erlang:element(3, Dep));
absorb_dep(Data, _) ->
    Data.

-spec absorb_dep(Data :: mod_data(), Name :: keyable(), Spec :: rsrc_spec())
        -> mod_data() | no_return().
absorb_dep(Data, Name, {?RTYPE, Loc, #mod_ref{res = Res}}) ->
    map_dep(Data, #mod_dep{
        name = term_to_atom(Name), res = term_to_atom(Res), loc = Loc});
absorb_dep(Data, Name, Spec) when ?is_rec_type(Spec, ?RTYPE, 2) ->
    {Res, Loc} = parse_ext_spec(erlang:element(2, Spec)),
    map_dep(Data, #mod_dep{name = term_to_atom(Name), res = Res, loc = Loc});
absorb_dep(Data, _, _) ->
    Data.

-spec ensure_app(
    Path    :: rsrc_dir(),
    Mod     :: module(),
    Name    :: atom(),
    Opts    :: this_opts(),
    Result  :: {'ok', term()} )
        ->  {'ok', term()} | rebar_err().
%
% Make sure there's something rebar will consider to be an app in the
% directory specified by Path.
% The return value is as specified for download/3 - Result on success or an
% 'error' tuple otherwise.
%
ensure_app(Path, Mod, Name, Opts, Result) ->
    BApp = lists:flatten(filename:join(
            [Path, "ebin", io_lib:format("~s.app", [Name])])),
    SApp = lists:flatten(filename:join(
            [Path, "src", io_lib:format("~s.app.src", [Name])])),
    case filelib:is_file(BApp) orelse filelib:is_file(SApp) of
        'true' ->
            Result;
        _ ->
            Vsn = case proplists:get_value('vsn', Opts) of
                'undefined' ->
                    {'plain', Val} = Mod:make_vsn(Path),
                    Val;
                Val ->
                    Val
            end,
            Desc = proplists:get_value('description', Opts, Name),
            Data = io_lib:format(
                "%%\n"
                "%% Generated by ~s\n"
                "%%\n"
                % this is the minimum set of elements required to make rebar
                % happy when there are no sources for it to compile
                "{application,   ~s,\n"
                "[\n"
                "    {description,   \"~s\"},\n"
                "    {vsn,           \"~s\"},\n"
                "    {modules,       []},\n"
                "    {registered,    []},\n"
                "    {applications,  [kernel, stdlib]}\n"
                "]}.\n",
                [?MODULE, Name, Desc, Vsn]),
            case filelib:ensure_dir(SApp) of
                'ok' ->
                    case file:write_file(SApp, Data) of
                        'ok' ->
                            Result;
                        Err ->
                            Err
                    end;
                Err ->
                    Err
            end
    end.

-spec parse_ext_spec(Spec :: rsrc_spec())
        -> {rsrc_type(), rsrc_loc()} | no_return().
parse_ext_spec(Spec) when ?is_min_tuple(Spec, 2) ->
    {term_to_atom(erlang:element(1, Spec)), erlang:element(2, Spec)};
parse_ext_spec(Spec) ->
    Class = 'unrecognized_ext_spec',
    format_error('rebar_api', 'error', Class, Spec),
    ?throw_error({Class, Spec}).

-spec path_name(Path :: rsrc_dir()) -> rsrc_name() | rebar_err().
%
% Get the resource name from the specified dependency path.
%
path_name(Path) ->
    term_to_atom(lists:last(filename:split(Path))).

-spec term_to_atom(Term :: keyable()) -> atom() | no_return().
%
% make the specified term into an atom
%
term_to_atom(Term) when erlang:is_atom(Term) ->
    Term;
term_to_atom(Term) when erlang:is_binary(Term) ->
    erlang:binary_to_atom(Term, 'latin1');
term_to_atom(Term) when erlang:is_list(Term) ->
    erlang:list_to_atom(Term);
term_to_atom(Term) ->
    erlang:error('badarg', [Term]).

-ifdef(rrr_develop).
-compile({nowarn_unused_function, term_to_binary/1}).
-spec term_to_binary(Term :: keyable()) -> binary() | no_return().
%
% make the specified term into a binary
%
term_to_binary(Term) when erlang:is_atom(Term) ->
    erlang:atom_to_binary(Term, 'latin1');
term_to_binary(Term) when erlang:is_binary(Term) ->
    Term;
term_to_binary(Term) when erlang:is_list(Term) ->
    erlang:list_to_binary(Term);
term_to_binary(Term) ->
    erlang:error('badarg', [Term]).
-endif.

%
% Module state functions.
% Rebar doesn't give us consistent access to modifiable state, so we keep it
% in the process environment.
%
-define(MOD_DATA_KEY,   {?MODULE, 'data'}).

-spec mod_data() -> mod_data().
mod_data() ->
    case erlang:get(?MOD_DATA_KEY) of
        'undefined' ->
            #mod_data{};
        #mod_data{} = Data ->
            Data
    end.

-spec mod_data(Data :: mod_data()) -> mod_data().
mod_data(#mod_data{} = Data) ->
    erlang:put(?MOD_DATA_KEY, Data),
    Data.

-spec map_dep(Data :: mod_data(), Dep :: mod_dep()) -> mod_data() | no_return().
map_dep(#mod_data{deps = Deps} = Data,
        #mod_dep{name = Name, loc = Loc} = Dep) ->
    case lists:keyfind(Name, #mod_dep.name, Deps) of
        Dep ->
            Data;
        #mod_dep{} ->
            Class = 'duplicate_dep_name',
            format_error('rebar_api', 'error', Class, Name),
            _ = dump_mod_data(Data),
            ?throw_error({Class, Name});
        'false' ->
            case lists:keyfind(Loc, #mod_dep.loc, Deps) of
                #mod_dep{} ->
                    Class = 'duplicate_dep_loc',
                    format_error('rebar_api', 'error', Class, Loc),
                    _ = dump_mod_data(Data),
                    ?throw_error({Class, Loc});
                'false' ->
                    Data#mod_data{deps = [Dep | Deps]}
            end
    end.

-spec map_res(Data :: mod_data(), Res :: mod_res()) -> mod_data() | no_return().
map_res(#mod_data{rsrcs = Rsrcs} = Data, #mod_res{res = Type} = Res) ->
    case lists:keyfind(Type, #mod_res.res, Rsrcs) of
        Res ->
            Data;
        #mod_res{} ->
            Class = 'duplicate_res_type',
            format_error('rebar_api', 'error', Class, Type),
            _ = dump_mod_data(Data),
            ?throw_error({Class, Type});
        'false' ->
            Data#mod_data{rsrcs = [Res | Rsrcs]}
    end.

-spec lookup_dep(Data :: mod_data(), DepName :: keyable())
        -> mod_dep() | no_return().
%
% Accommodate DepName being something other than an atom, for example the
% 'name' field in an app_info record.
%
lookup_dep(#mod_data{deps = Deps} = Data, DepName) ->
    Name = term_to_atom(DepName),
    case lists:keyfind(Name, #mod_dep.name, Deps) of
        #mod_dep{} = Dep ->
            Dep;
        _ ->
            Class = 'unmapped_dep_name',
            format_error('rebar_api', 'error', Class, Name),
            _ = dump_mod_data(Data),
            ?throw_error({Class, Name})
    end.

-spec lookup_loc(Data :: mod_data(), Loc :: rsrc_loc())
        -> mod_dep() | no_return().
lookup_loc(#mod_data{deps = Deps} = Data, Loc) ->
    case lists:keyfind(Loc, #mod_dep.loc, Deps) of
        #mod_dep{} = Dep ->
            Dep;
        _ ->
            Class = 'unmapped_dep_loc',
            format_error('rebar_api', 'error', Class, Loc),
            _ = dump_mod_data(Data),
            ?throw_error({Class, Loc})
    end.

-spec lookup_res(Data :: mod_data(), Res :: rsrc_type())
        -> mod_res() | no_return().
lookup_res(#mod_data{rsrcs = Rsrcs} = Data, Res) ->
    case lists:keyfind(Res, #mod_res.res, Rsrcs) of
        #mod_res{} = Rec ->
            Rec;
        _ ->
            Class = 'unmapped_res_type',
            format_error('rebar_api', 'error', Class, Res),
            _ = dump_mod_data(Data),
            ?throw_error({Class, Res})
    end.

%
% To debug, or not to debug.
%
-spec dump_mod_data(Data :: mod_data()) -> mod_data().
-compile({nowarn_unused_function, debug_call_stack/0}).
-spec debug_call_stack() -> term().

-ifndef(RRR_DEBUG).

-compile({inline, debug_call_stack/0}).
debug_call_stack() ->
    'ok'.

-compile({inline, dump_mod_data/1}).
dump_mod_data(Data) ->
    Data.

-else.

debug_call_stack() ->
    {_, {_, [_ | Stack]}} = (catch erlang:error('ok')),
    rebar_api:debug("~s stack:~n~p", [?MODULE, Stack]).

dump_mod_data(#mod_data{} = Data) ->
    rebar_api:debug("~s state:~n~p", [?MODULE, Data]),
    Data.

% If the ?RRR_STATE(Field) macro isn't used, these functions won't be called.
% The compiler will leave them out, but we need to disable the unused function
% warning to get through compilation.
-compile({nowarn_unused_function, [
    debug_state/2,
    state_file_path/1,
    state_file_path/2,
    write_state_file/2
]}).

debug_state(State, 'state' = Field) ->
    write_state_file(state_file_path(Field), State);
debug_state(State, Field) ->
    case erlang:is_atom(Field) andalso
            erlang:function_exported('rebar_state', Field, 1) of
        true ->
            write_state_file(state_file_path(Field),
                rebar_state:Field(State));
        _ ->
            write_state_file(state_file_path(['opts', Field]),
                rebar_state:get(State, Field, '$not_found$'))
    end.

state_file_path('state') ->
    state_file_path(['state'], []);
state_file_path(Field) when erlang:is_list(Field) ->
    state_file_path(['state' | Field], []);
state_file_path(Field) ->
    state_file_path(['state', Field], []).

state_file_path([Scope | Scopes], Key) when erlang:is_tuple(Scope) ->
    state_file_path(erlang:tuple_to_list(Scope) ++ Scopes, Key);
state_file_path([Scope | Scopes], []) ->
    state_file_path(Scopes, erlang:atom_to_list(Scope));
state_file_path([Scope | Scopes], Key) ->
    state_file_path(Scopes, Key ++ [$. | erlang:atom_to_list(Scope)]);
state_file_path([], Key) ->
    io_lib:format("/tmp/rebar.~s.config", [Key]).

write_state_file(File, Data) when ?is_rec_type(Data, 'dict') ->
    file:write_file(File, io_lib:format("~p.~n", [dict:to_list(Data)]));
write_state_file(File, Data) ->
    file:write_file(File, io_lib:format("~p.~n", [Data])).

-endif.
