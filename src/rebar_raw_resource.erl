%% -*- mode: erlang; erlang-indent-level: 4; indent-tabs-mode: nil -*-
%% ========================================================================
%% Copyright (c) 2016 T. R. Burghart.
%%
%% Permission to use, copy, modify, and/or distribute this software for any
%% purpose with or without fee is hereby granted, provided that the above
%% copyright notice and this permission notice appear in all copies.
%%
%% THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
%% WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
%% MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
%% ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
%% WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
%% ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
%% OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
%% ========================================================================

-module(rebar_raw_resource).
%%
%% For efficiency in use, we don't have a dependency on rebar itself, so the
%% behaviors this module implements aren't guaranteed to be visible.
%% If they were, they'd be the following:
%-behaviour(provider).
%-behaviour(rebar_resource).

% the dependency resource type identifier associated with this resource.
-define(RTYPE,  raw).

-export([
    % provider
    do/1,
    format_error/1,
    init/1,
    % rebar_resource
    download/3,
    lock/2,
    make_vsn/1,
    needs_update/2
]).

-compile([
    no_auto_import,
    warn_export_all,
    warn_obsolete_guard,
    warnings_as_errors
]).

% For development only - you *really* don't want this defined!
%-define(RRR_DEBUG,  true).

-define(else,   'true').
-define(is_min_tuple(Var, Min),
    erlang:is_tuple(Var) andalso erlang:tuple_size(Var) >= Min).
-define(is_rec_type(Var, Type),
    ?is_min_tuple(Var, 1) andalso erlang:element(1, Var) =:= Type).

-ifdef(RRR_DEBUG).
-define(RRR_STATE(Field),   debug_state(State, Field)).
-else.
-define(RRR_STATE(Field),   'ok').
-endif.

%
% Implementation Notes:
%
% We maintain mappings in the process dictionary between:
%
% - resource types and their implementing modules
% - dependency names and their resource types
% - dependency locations and their names
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
% Because resource specifiers (rightly) don't have a specified schema, we treat
% them as relatively opaque tuples where the first element is the type and the
% second element is the location. Note that this means old-style dependencies
% with a version regex WILL break the mapping strategy, but that's a constraint
% I'm ok with.
%
% Currently, we satisfy rebar's need for an OTP application by scribbling a
% minimal app config file in <dep-path>/ebin/<dep-name>.app if there's not
% such a file already, or its equivalent source in the <dep-path>/src
% directory.
%
% It would be preferable to build the rebar_app_info record dynamically and
% insert it into the state so we didn't have to leave droppings in the
% dependency's filesystem, but it's unclear whether there's a reliable place
% to hook that functionality into the processing sequence or whether rebar
% would accept it if we did without an actual file to check for changes.
%

%% ===================================================================
%% Types - none exported
%% ===================================================================
%
% Type names have prefixes of 'rsrc_' indicating they apply to all dependency
% specs or 'this_' indicating they're specific to this resource type.
%
-type rebar_dep()   :: {rsrc_name()} | {rsrc_name(), rsrc_spec() | rsrc_vsn()}.
-type rebar_dir()   :: file:filename_all().
-type rebar_err()   :: {'error', term()}.
-type rebar_rsrc()  :: {rsrc_type(), rsrc_mod()}.
-type rebar_state() :: rebar_state:t().
-type rebar_vsn()   :: {'plain', rsrc_vsn()}.

-type rsrc_dir()    :: rebar_dir().
-type rsrc_loc()    :: string().    % URL-ish
-type rsrc_mod()    :: module().
-type rsrc_name()   :: keyable().
-type rsrc_spec()   :: tuple().     % {rsrc_type(), rsrc_loc(), ...}
-type rsrc_type()   :: atom().
-type rsrc_vsn()    :: string().

-type this_opt()    :: atom() | {atom(), term()}.
-type this_opts()   :: [this_opt()].
-type this_spec()   :: this_spec2() | this_spec3().
-type this_spec2()  :: {this_type(), rsrc_spec()}.
-type this_spec3()  :: {this_type(), rsrc_spec(), this_opts()}.
-type this_type()   :: ?RTYPE.

-type keyable()     :: atom() | binary() | list().
% -type map_key()   :: name_key() | spec_key() | type_key().
-type name_key()    :: {?MODULE, 'name', rsrc_name()}.    % => rsrc_type()
-type spec_key()    :: {?MODULE, 'spec', rsrc_loc()}.     % => rsrc_name()
-type type_key()    :: {?MODULE, 'type', rsrc_type()}.    % => module()

%% ===================================================================
%% Function Specs
%% ===================================================================
%
% ALL functions are spec'd!
% Specs for exported functions MAY differ from those for their specifying
% behavior.
%
%% ===================================================================
%% Provider Behavior
%% ===================================================================
-spec init(State :: rebar_state:t()) -> {'ok', rebar_state()}.
-spec do(State :: rebar_state:t()) -> {'ok', rebar_state()}.
-spec format_error(Error :: term()) -> iolist().
%% ===================================================================
%% Resource Behavior
%% ===================================================================
-spec download(
        Dest :: rsrc_dir(), From :: this_spec(), State :: rebar_state())
        -> {this_type(), rsrc_dir()} | {'ok', term()} | rebar_err().
-spec lock(Path :: rsrc_dir(), Spec :: this_spec())
        -> this_spec() | rebar_err().
-spec needs_update(Path :: rsrc_dir(), Spec :: this_spec())
        -> boolean() | rebar_err().
-spec make_vsn(Path :: rsrc_dir()) -> rebar_vsn() | rebar_err().
%% ===================================================================
%% Internal
%% ===================================================================
-spec absorb_app_infos(AppInfos :: tuple()) -> 'ok'.
-spec absorb_dep(Name :: keyable(), Spec :: rsrc_spec()) -> 'ok'.
-spec absorb_deps(Deps :: [rebar_dep()]) -> 'ok'.
-spec absorb_named_spec(Name :: keyable(), Spec :: rsrc_spec()) -> 'ok'.
-spec absorb_profiles(Profiles :: [atom()], State :: rebar_state()) -> 'ok'.
-spec absorb_resources(Resources :: [rebar_rsrc()]) -> 'ok'.
-spec absorb_state(State :: rebar_state()) -> 'ok'.

-spec ensure_app(
        Path    :: rsrc_dir(),
        Mod     :: module(),
        Name    :: keyable(),
        Opts    :: this_opts(),
        Result  :: term() )
            ->  term().

-spec path_name(Path :: rsrc_dir()) -> rsrc_name() | rebar_err().
-spec term_to_atom(Term :: keyable()) -> atom() | no_return().
-spec term_to_binary(Term :: keyable()) -> binary() | no_return().

% these all pass errors through
-spec name_key(rsrc_name() | rebar_err()) -> name_key() | rebar_err().
-spec name_mod(rsrc_name() | rebar_err()) -> rsrc_mod() | rebar_err().
-spec name_type(rsrc_name() | rebar_err()) -> rsrc_type() | rebar_err().
-spec spec_key(rsrc_spec() | rsrc_loc() | rebar_err()) -> spec_key() | rebar_err().
-spec spec_mod(rsrc_spec() | rsrc_loc() | rebar_err()) -> rsrc_mod() | rebar_err().
-spec spec_name(rsrc_spec() | rsrc_loc() | rebar_err()) -> rsrc_name() | rebar_err().
-spec spec_type(rsrc_spec() | rsrc_loc() | rebar_err()) -> rsrc_type() | rebar_err().
-spec type_key(rsrc_type() | rebar_err()) -> type_key() | rebar_err().
-spec type_mod(rsrc_type() | rebar_err()) -> rsrc_mod() | rebar_err().

%% ===================================================================
%% Provider API
%% ===================================================================

%
% Installs the resource handler, the provider itself does nothing.
%
% This gets called repeatedly, for each profile, and in each case we want
% to prime the process environment with any info we may need later, as
% download/3 is NOT called first if the dependency is already present, and
% it's the only resource call that gets to see the rebar state.
%
init(State) ->
    'ok' = absorb_state(State),
    {'ok', rebar_state:add_resource(State, {?RTYPE, ?MODULE})}.

%
% Fulfills the `provider' contract, does nothing ... for now.
%
% IF there's a viable way to hook rebar's app_discovery provider, this will
% be the place to do it, but it looks like rebar really wants to see a physical
% file so there's not much we can do.
%
do(State) ->
    {'ok', State}.

%
% Converts specified Error to a string.
%
format_error(Error) ->
    lists:flatten(io_lib:format("~p", [Error])).

%% ===================================================================
%% Resource API
%% ===================================================================

%
% Download the specified resource using its underlying handler.
%
download(Dest, {?RTYPE, Spec}, State) ->
    download(Dest, {?RTYPE, Spec, []}, State);

download(Dest, {?RTYPE, Spec, Opts}, State) ->
%   ?RRR_STATE('state'),
%   ?RRR_STATE('opts'),
%   ?RRR_STATE('lock'),

    'ok' = absorb_state(State),
    Name = spec_name(Spec),
    case name_mod(Name) of
        {'error', _} = Err ->
            Err;
        Mod ->
            case Mod:download(Dest, Spec, State) of
                {'error', _} = Err ->
                    Err;
                {'ok', _} = Ret ->
                    ensure_app(Dest, Mod, Name, Opts, Ret);
                _ ->
                    ensure_app(Dest, Mod, Name, Opts, {?RTYPE, Dest})
            end
    end.

%
% Pass through to the underlying resource handler.
%
lock(Path, {?RTYPE, Spec}) ->
    case spec_mod(Spec) of
        {'error', _} = Err ->
            Err;
        Mod ->
            case Mod:lock(Path, Spec) of
                {'error', _} = Err ->
                    Err;
                Ret ->
                    {?RTYPE, Ret}
            end
    end;

lock(Path, {?RTYPE, Spec, Opts}) ->
    case spec_mod(Spec) of
        {'error', _} = Err ->
            Err;
        Mod ->
            case Mod:lock(Path, Spec) of
                {'error', _} = Err ->
                    Err;
                Ret ->
                    {?RTYPE, Ret, Opts}
            end
    end.

%
% Pass through to the underlying resource handler.
%
needs_update(Path, {?RTYPE, Spec, _Opts}) ->
    needs_update(Path, {?RTYPE, Spec});

needs_update(Path, {?RTYPE, Spec}) ->
    case spec_mod(Spec) of
        {'error', _} = Err ->
            Err;
        Mod ->
            Mod:needs_update(Path, Spec)
    end.

%
% Pass through to the underlying resource handler.
%
make_vsn(Path) ->
    case name_mod(path_name(Path)) of
        {'error', _} = Err ->
            Err;
        Mod ->
            Mod:make_vsn(Path)
    end.

%% ===================================================================
%% Internal
%% ===================================================================

%
% Soak up whatever we care about from the state.
% There's a lot of code here that may be redundant and/or unused as I feel
% around trying to make sure all of the dependencies are found in each runtime
% scenario.
% Hopefully it'll all be cleaned up someday.
%

absorb_state(State) ->
    absorb_resources(rebar_state:resources(State)),
    absorb_deps(rebar_state:get(State, 'deps', [])),
    absorb_app_infos(rebar_state:lock(State)),
%   absorb_profiles(rebar_state:current_profiles(State), State),
    dump_state().

-compile({nowarn_unused_function, absorb_app_infos/1}).
absorb_app_infos([AppInfo | AppInfos]) ->
    absorb_dep(rebar_app_info:name(AppInfo), rebar_app_info:source(AppInfo)),
    absorb_app_infos(AppInfos);
absorb_app_infos([]) ->
    'ok'.

absorb_deps([Dep | Deps]) ->
    absorb_dep(Dep),
    absorb_deps(Deps);
absorb_deps([]) ->
    'ok'.

-compile({nowarn_unused_function, absorb_profiles/2}).
absorb_profiles([Profile | Profiles], State) ->
    absorb_app_infos(rebar_state:get(State, {'parsed_deps', Profile}, [])),
    absorb_profiles(Profiles, State);
absorb_profiles([], _) ->
    'ok'.

%
% Allow for whatever may come through to handle future extensions.
%
absorb_resources([Res | Resources]) when ?is_min_tuple(Res, 2) ->
    erlang:put(
        type_key(erlang:element(1, Res)),
        term_to_atom(erlang:element(2, Res))),
    absorb_resources(Resources);
absorb_resources([_ | Resources]) ->
    absorb_resources(Resources);
absorb_resources([]) ->
    'ok'.

%
% Accommodate dependencies with or without the rebar2 regex string.
% Be as lenient as we can about current and future structure.
%
absorb_dep(Dep) when ?is_min_tuple(Dep, 2)
        andalso erlang:is_tuple(erlang:element(2, Dep)) ->
    absorb_dep(erlang:element(1, Dep), erlang:element(2, Dep));
absorb_dep(Dep) when ?is_min_tuple(Dep, 3)
        andalso erlang:is_tuple(erlang:element(3, Dep)) ->
    absorb_dep(erlang:element(1, Dep), erlang:element(3, Dep));
absorb_dep(_) ->
    'ok'.

absorb_dep(Name, {?RTYPE, Spec, _}) ->
    absorb_named_spec(Name, Spec);
absorb_dep(Name, {?RTYPE, Spec}) ->
    absorb_named_spec(Name, Spec);
absorb_dep(_, _) ->
    'ok'.

absorb_named_spec(NameIn, Spec) when ?is_min_tuple(Spec, 2) ->
    Name = term_to_atom(NameIn),
    Type = spec_type(Spec),
    erlang:put(name_key(Name), Type),
    erlang:put(spec_key(Spec), Name),
    'ok';
absorb_named_spec(_, _) ->
    'ok'.

%
% Make sure there's something rebar will consider to be an app in the directory
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
            Vsn = case proplists:get_value(vsn, Opts) of
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
            case filelib:ensure_dir(BApp) of
                'ok' ->
                    case file:write_file(BApp, Data) of
                        'ok' ->
                            Result;
                        Err ->
                            Err
                    end;
                Err ->
                    Err
            end
    end.

% Get the resource name from the specified dependency path.
path_name(Path) ->
    term_to_atom(lists:last(filename:split(Path))).

% make the specified term into an atom
term_to_atom(Term) when erlang:is_atom(Term) ->
    Term;
term_to_atom(Term) when erlang:is_binary(Term) ->
    erlang:binary_to_atom(Term, 'latin1');
term_to_atom(Term) when erlang:is_list(Term) ->
    erlang:list_to_atom(Term);
term_to_atom(Term) ->
    erlang:error('badarg', [Term]).

-compile({nowarn_unused_function, term_to_binary/1}).
% make the specified term into a binary
term_to_binary(Term) when erlang:is_atom(Term) ->
    erlang:atom_to_binary(Term, 'latin1');
term_to_binary(Term) when erlang:is_binary(Term) ->
    Term;
term_to_binary(Term) when erlang:is_list(Term) ->
    erlang:list_to_binary(Term);
term_to_binary(Term) ->
    erlang:error('badarg', [Term]).

%
% Process environment lookup functions.
% These all accommodate being called with an error result, which they just
% pass back, so nested calls don't have to use intervening case statements.
%

spec_name({error, _} = Error) ->
    Error;
spec_name(Spec) when ?is_min_tuple(Spec, 2) ->
    spec_name(erlang:element(2, Spec));
spec_name(Spec) ->
    case erlang:get(spec_key(Spec)) of
        'undefined' ->
            error_result('unmapped_spec', Spec);
        Name ->
            Name
    end.

spec_type({error, _} = Error) ->
    Error;
spec_type(Spec) when ?is_min_tuple(Spec, 2) ->
    term_to_atom(erlang:element(1, Spec));
spec_type(Spec) ->
    name_type(spec_name(Spec)).

spec_mod({error, _} = Error) ->
    Error;
spec_mod(Spec) ->
    type_mod(spec_type(Spec)).

name_type({error, _} = Error) ->
    Error;
name_type(Name) ->
    case erlang:get(name_key(Name)) of
        'undefined' ->
            error_result('unmapped_name', Name);
        Type ->
            Type
    end.

name_mod({error, _} = Error) ->
    Error;
name_mod(Name) ->
    type_mod(name_type(Name)).

type_mod({error, _} = Error) ->
    Error;
type_mod(TypeIn) ->
    Type = term_to_atom(TypeIn),
    case erlang:get(type_key(Type)) of
        'undefined' ->
            error_result('unmapped_type', Type);
        Mod ->
            Mod
    end.

%
% Process environment keys.
%

type_key({'error', _} = Error) ->
    Error;
type_key(Type) ->
    {?MODULE, 'type', term_to_atom(Type)}.

name_key({'error', _} = Error) ->
    Error;
name_key(Name) ->
    {?MODULE, 'name', term_to_atom(Name)}.

spec_key({'error', _} = Error) ->
    Error;
spec_key(Spec) when ?is_min_tuple(Spec, 2) ->
    spec_key(erlang:element(2, Spec));
spec_key(Spec) ->
    {?MODULE, 'spec', Spec}.

%
% To debug, or not to debug.
%
-ifndef(RRR_DEBUG).

error_result(Class, Data) ->
    {'error', {?MODULE, {Class, Data}}}.

-compile({inline, [dump_state/0]}).
dump_state() ->
    'ok'.

-else.

error_result(Class, Data) ->
    erlang:error({?MODULE, {Class, Data, dump_env()}}).

dump_state() ->
    rebar_api:debug("~s state:~n~p", [?MODULE, dump_env()]),
    'ok'.

dump_env() ->
    filter_env(erlang:get(), []).

filter_env([{{?MODULE, _, _}, _} = Rec | Rest], Result) ->
    filter_env(Rest, Result ++ [Rec]);
filter_env([_ | Rest], Result) ->
    filter_env(Rest, Result);
filter_env([], Result) ->
    Result.

% If the ?RRR_STATE(Field) macro isn't used, nothing calls these functions.
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
    state_file_path(Scopes, Key ++ [$., erlang:atom_to_list(Scope)]);
state_file_path([], Key) ->
    io_lib:format("/tmp/rebar.~s.config", [Key]).

write_state_file(File, Data) when ?is_rec_type(Data, 'dict') ->
    file:write_file(File, io_lib:format("~p.~n", [dict:to_list(Data)]));
write_state_file(File, Data) ->
    file:write_file(File, io_lib:format("~p.~n", [Data])).

-endif.

