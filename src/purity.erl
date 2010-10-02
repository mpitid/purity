%% ====================================================================
%% This library is free software; you can redistribute it and/or
%% modify it under the terms of the GNU Lesser General Public
%% License as published by the Free Software Foundation; either
%% version 2.1 of the License, or (at your option) any later version.
%%
%% This library is distributed in the hope that it will be useful,
%% but WITHOUT ANY WARRANTY; without even the implied warranty of
%% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
%% Lesser General Public License for more details.
%%
%% You should have received a copy of the GNU Lesser General Public
%% License along with this library; if not, write to the Free Software
%% Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
%% 02110-1301 USA
%%
%% @copyright 2009-2010 Michael Pitidis, Kostis Sagonas
%% @author Michael Pitidis <mpitid@gmail.com>
%% @end
%% =====================================================================

%%%
%%% @doc Pureness analysis of Erlang functions.
%%%

-module(purity).

-export([module/2]).
-export([module/3, modules/3]).
-export([pmodules/3, panalyse/2]).
-export([is_pure/2]).
-export([propagate/2, find_missing/1]).
-export([analyse_changed/3]).

-import(purity_utils, [fmt_mfa/1, str/2]).
-import(purity_utils, [remove_args/1, dict_cons/3, filename_to_module/1]).

-export_type([pure/0]).


%% Besides built-in functions, a select few of Erlang expressions
%% may influence the purity if functions.
-define(PREDEF, [
        {{erl,'receive'},  [side_effects]},
        {{erl,'catch'},    [non_determinism]}]).
%% Note that most exceptions are expressed in terms of the following
%% BIFs and primops which are hard-coded elsewhere:
%% {erlang,error,1}, {erlang,throw,1}, {erlang,exit,1}
%% {match_fail,1}, {raise,2}

%% The special values are the lowest level dependencies a function
%% can have, and their purity is defined by the user upon invocation
%% of the analysis (except side-effects which are always impure).
-type special() :: side_effects | non_determinism | exceptions.
-type arg_dep() :: {arg, pos_integer()}.
-type ctx_arg() :: {pos_integer(), mfa()}.
-type context() :: {remote, purity_utils:emfa(), [ctx_arg()]}
                 | {local, mfa() | atom(), [ctx_arg()]}
                 | {primop, {atom(), arity()}, [ctx_arg()]}
                 | arg_dep()
                 | {erl, 'receive' | 'catch'}
                 | special().


-type map_key() :: cerl:var_name().
-type map_val() :: mfa() | pos_integer().
-type map()     :: [{map_key(), map_val()}].

-type pure()    :: true | {false, string()} | [context()] | undefined.


%% @spec is_pure(mfa(), dict()) -> boolean()
%%
%% @doc Simple purity test, only distinguishes between pure and impure.
%% Any function missing from the lookup table is also considered impure.
-spec is_pure(mfa(), dict()) -> boolean().

is_pure({_,_,_} = MFA, Table) ->
    case dict:find(MFA, Table) of
        {ok, true} ->
            true;
        _Other ->
            false
    end.

%% @spec module(cerl:c_module(), purity_utils:options()) -> dict()
%%
%% @doc Analyse a module and return a lookup table of concrete results,
%% indexed by `{Module, Function, Arity}'.
%%
%% Analysis starts from parsed core erlang terms.
%%
%% @see is_pure/2
%% @see module/3
%% @see propagate/2
-spec module(cerl:c_module(), purity_utils:options()) -> dict().

module(Core, Options) ->
    Plt = load_plt_silent(Options),
    Tab = purity_plt:get_cache(Plt, Options),
    Dep = module(Core, Options, Tab),
    Res = propagate(Dep, Options),
    Res.

%% @doc Load a PLT from the provided options. If no PLT is found, or
%% there are errors, return a new PLT.
-spec load_plt_silent(purity_utils:options()) -> purity_plt:plt().
load_plt_silent(Opts) ->
    File = option(plt, Opts, purity_plt:get_default_path()),
    Check = not option(no_check, Opts, false),
    case purity_plt:load(File) of
        {error, _Type} ->
            purity_plt:new();
        {ok, Plt} when Check ->
            case purity_plt:check(Plt) of
                old_version ->
                    purity_plt:new();
                {differ, _Failed} ->
                    purity_plt:new();
                ok ->
                    Plt
            end;
        {ok, Plt} -> % No checks, unwise.
            Plt
    end.


%% Keep track of the following values for the currently analysed function.
%% Some of them persist across functions as well.
%%
%% mfa      - Unique identifier of the currently analysed function
%% ctx      - List of dependencies (context) of the current function,
%%            the result of the analysis
%% vars     - Map of higher order variables to MFAs
%% args     - Map names of current function's arguments to their position
%%            in the argument list
%% aliases  - Keep track of aliases to variables for looking up vars/args
%%            more effectively
%% free     - An ordered set of free variables for the current function
%%            (only relevant to nested functions of course)
%% count    - Counter for giving unique names to nested functions
%% names    - Ordered set of reserved function names, for excluding them
%%            from unique identifiers
%% opts     - Any options affecting analysis
%% table    - Mapping of MFAs to their pureness result, be that a concrete
%%            value or a context.
-record(state, {mfa     = undefined  :: mfa() | undefined,
                ctx     = ctx_new()  :: [context()],
                vars    = map_new()  :: map(),
                args    = map_new()  :: map(),
                aliases = dict:new() :: dict(),
                free    = []         :: [cerl:var_name()],
                count   = 1          :: pos_integer(),
                names   = []         :: [atom()],
                opts    = []         :: [any()],
                table   = dict:new() :: dict()}).

-type state() :: #state{}.


%% State record for propagation of dependency lists to pureness values.
-record(pst, {funs = []         :: [mfa()],
              prev = sets:new() :: set(),
              revs              :: dict(),
              cycles            :: dict(),
              table             :: dict()}).


%% @doc Return a list of MFAs and a list of primops for which we have no
%% pureness information.

-spec find_missing(dict()) -> {[mfa()], [purity_utils:primop()]}.

find_missing(Table) ->
    Set1 = ordsets:from_list(collect_function_deps(Table)),
    Set2 = ordsets:from_list(dict:fetch_keys(Table)),
    Funs = ordsets:subtract(Set1, Set2),
    Set3 = ordsets:from_list(collect_primop_deps(Table)),
    Prim = ordsets:subtract(Set3, Set2),
    {Funs, Prim}.

%% Populate the Table with the purity of any BIF necessary.
%% XXX: Not the cleanest approach, but it has the least impact for the moment.
add_bifs(Tab) ->
    lists:foldl(
        fun(F, TabN) -> dict:store(F, is_bif_pure(F), TabN) end,
        Tab, collect_bif_deps(Tab)).

collect_function_deps(Tab) ->
    collect_deps(Tab, fun purity_utils:is_concrete_fun/1).

collect_primop_deps(Tab) ->
    collect_deps(Tab, fun purity_utils:is_primop/1).

collect_bif_deps(Tab) ->
    collect_deps(Tab, fun is_bif/1).

is_bif({M, F, A} = Fun) ->
    purity_utils:is_concrete_fun(Fun) andalso purity_bifs:is_known(M, F, A);
is_bif({P, A}=Pri) ->
    purity_utils:is_primop(Pri) andalso purity_bifs:is_known(P, A);
is_bif(_) ->
    false.

is_bif_pure({M, F, A}) ->
    purity_bifs:is_pure(M, F, A);
is_bif_pure({P, A}) ->
    purity_bifs:is_pure(P, A).

%% @doc Return a list of any functions other functions may depend on.
%% Apply any filtering here instead of the result as an optimisation.
collect_deps(Tab, Filter) ->
    dict:fold(
        fun(_, V, Acc) ->
                [F || F <- purity_utils:collect_dependencies(V),
                    Filter(F)] ++ Acc end,
        [], Tab).


%% @doc Re-analyse changed files and affected modules, update PLT.
-spec analyse_changed(term(), purity_utils:options(), purity_plt:plt()) -> purity_plt:plt().

analyse_changed(Changed, Options, Plt) ->
    Mods = purity_plt:get_affected(Plt, Changed),
    Errors = [F || {error, F} <- Changed],
    Tab = purity_utils:delete_modules(
        purity_plt:get_table(Plt), [filename_to_module(E) || E <- Errors]),
    Files = purity_plt:get_files(Plt),
    FileLookup = make_modlookup(Files),
    ToScan = [F || {ok, F} <- [FileLookup(M) || M <- Mods]] -- Errors,
    purity_plt:new(purity:modules(ToScan, Options, Tab), Files -- Errors).

%% @doc Generate a lokoup function mapping modules to their filename.
make_modlookup(Filenames) ->
    Map = dict:from_list([{filename_to_module(F), F} || F <- Filenames]),
    fun(Mod) -> dict:find(Mod, Map) end.


%% @spec module(cerl:c_module(), options(), dict()) -> dict()
%%
%% @doc Analyse a module and return a lookup table of functions
%% and dependencies, indexed by `{Module, Function, Arity}'.
%%
%% Analysis starts from parsed core erlang terms.
%%
%% @see modules/3

-spec module(cerl:c_module(), purity_utils:options(), dict()) -> dict().

module(Core, Options, Tab0) ->
    CoreLabels = label(Core),
    Module = cerl:concrete(cerl:module_name(CoreLabels)),
    Defs = [{cerl:var_name(Var), Fun} || {Var, Fun} <- cerl:module_defs(CoreLabels)],
    Names = lists:foldl(
        fun({{F,_},_}, Set) -> ordsets:add_element(atom_to_list(F), Set) end,
        ordsets:new(),
        Defs),
    St0 = state_new(Options, Names, purity_utils:delete_modules(Tab0, [Module])),
    Fun = fun({{F,A}, Fun}, St) ->
            analyse(Fun, St#state{mfa = {Module, F, A},
                                  vars = map_new(),
                                  aliases = core_aliases:scan(Fun)}) end,
    St1 = lists:foldl(Fun, St0#state{names = Names}, Defs),
    St1#state.table.


%% @doc Analyse a list of modules.
%%
%% Each module is analysed separately, and the lookup table is incrementally
%% updated.
%%
%% @see module/3

-spec modules([string()], purity_utils:options(), dict()) -> dict().

modules(Modules, Options, Tab0) when is_list(Modules) ->
    lists:foldl(
        fun(File, TabN) ->
                case purity_utils:get_core(File) of
                    {ok, Core} ->
                        module(Core, Options, TabN);
                    {error, Reason} ->
                        purity_utils:emsg(Reason),
                        TabN
                end end,
        Tab0, Modules).

%% @doc Analyse a list of modules in parallel.
%%
%% The number of parallel operations is limited to the number of
%% cpu processors/cores in order to minimise memory use.
%%
%% @see module/3
%% @see modules/3

-spec pmodules([file:filename()], purity_utils:options(), dict()) -> dict().

pmodules(Modules, Options, Tab0) when is_list(Modules) ->
    CPUs = erlang:system_info(logical_processors),
    merge([Tab0 | purity_utils:pmap({purity, panalyse}, [Options], Modules, CPUs)]).

-spec panalyse(file:filename(), purity_utils:options()) -> dict().

panalyse(Filename, Options) ->
    Tab = dict:new(),
    case purity_utils:get_core(Filename) of
        {ok, Core} ->
            module(Core, Options, Tab);
        {error, Reason} ->
            purity_utils:emsg(Reason),
            Tab
    end.

label(Core) ->
    {CoreLabels, _Next} = cerl_trees:label(cerl:from_records(Core)),
    CoreLabels.


analyse(Function, St0) ->
    St1 = St0#state{ctx = ctx_new(),
                    args = fetch_arg_vars(Function),
                    free = cerl_trees:free_variables(Function),
                    count = 1},
    St2 = traverse(cerl:fun_body(Function), St1),
    Ctx = postprocess_locals(St2),
    #state{mfa = MFA, table = Tab} = St2,
    St2#state{table = dict:store(MFA, Ctx, Tab), ctx = Ctx}.


fetch_arg_vars(Fun) ->
    Args = cerl:fun_vars(Fun),
    %% XXX: Breaks the map contract.
    [{cerl:var_name(V), N} || {N, V} <- enumerate(Args), cerl:is_c_var(V)].


%% @doc Traverse a Core Erlang AST and collect necessary information
%% in the form of a dependency list.
traverse(Tree, #state{mfa = MFA, table = _Table, ctx = Ctx} = St0) ->
    case cerl:type(Tree) of
        seq ->
            Arg = cerl:seq_arg(Tree),
            Body = cerl:seq_body(Tree),
            traverse_list([Arg, Body], St0);
        'case' ->
            Arg = cerl:case_arg(Tree),
            Clauses = cerl:case_clauses(Tree),
            traverse_list([Arg|Clauses], St0);
        clause ->
            Patterns = cerl:clause_pats(Tree),
            Guard = cerl:clause_guard(Tree),
            Body = cerl:clause_body(Tree),
            traverse_list([Body,Guard|Patterns], St0);
        'receive' ->
            %% When not specified explicitly, timeout is the infinity literal,
            %% while action is the true literal. Both may contain arbitrary
            %% expressions however.
            Clauses = cerl:receive_clauses(Tree),
            Timeout = cerl:receive_timeout(Tree),
            Action = cerl:receive_action(Tree),
            St1 = St0#state{ctx = ctx_add({erl, 'receive'}, Ctx)},
            traverse_list(Clauses ++ [Timeout, Action], St1);
        'apply' ->
            Op = cerl:apply_op(Tree),
            OpName = cerl:var_name(Op),
            Fun = resolve_fun_binding(OpName, St0),
            case Fun of
                MFA -> % Recursion
                    St0;
                _ ->
                    case promote_free_deps(Fun, St0) of
                        {ok, Fs} ->
                            St0#state{ctx = lists:foldl(fun ctx_add/2, Ctx, Fs)};
                        failed ->
                            Args = harvest_args(cerl:apply_args(Tree), St0),
                            St0#state{ctx = ctx_add({local, Fun, Args}, Ctx)}
                    end
            end;
        'call' ->
            case call_mfa(Tree) of
                MFA -> % Recursion
                    St0;
                CallMFA ->
                    Args = harvest_args(cerl:call_args(Tree), St0),
                    St0#state{ctx = ctx_add({remote, CallMFA, Args}, Ctx)}
            end;
        'fun' ->
            %% This mostly comes from nested funs as return values, etc.
            %% There's not much use for these the way analysis is structured,
            %% but analyse them anyway, for maximum coverage.
            {FunMFA, St1} = gen_fun_uid(Tree, St0),
            #state{table = Tab} = analyse(Tree, St1#state{mfa = FunMFA}),
            St0#state{table = Tab};
        'let' ->
            handle_let(Tree, St0);
        primop ->
            handle_primop(Tree, St0);
        letrec ->
            handle_letrec(Tree, St0);
        values ->
            traverse_list(cerl:values_es(Tree), St0);
        binary ->
            traverse_list(cerl:binary_segments(Tree), St0);
        bitstr ->
            %% Traversal of this node could be omitted altogether, I don't
            %% see how any of these subtrees can be impure in some way.
            traverse_list([cerl:bitstr_val(Tree), cerl:bitstr_size(Tree),
                           cerl:bitstr_unit(Tree), cerl:bitstr_type(Tree),
                           cerl:bitstr_flags(Tree)], St0);
        tuple ->
            traverse_list(cerl:tuple_es(Tree), St0);
        'catch' ->
            %% TODO: Would be nice if use of catch on functions that
            %% could never raise exceptions was detected and this
            %% dependency omitted.
            St1 = St0#state{ctx = ctx_add({erl, 'catch'}, Ctx)},
            traverse(cerl:catch_body(Tree), St1);
        cons ->
            traverse_list([cerl:cons_hd(Tree), cerl:cons_tl(Tree)], St0);
        'try' ->
            %% try_{vars,evars}/ should only contain variable names.
            Arg = cerl:try_arg(Tree),
            %Vars = cerl:try_vars(Tree),
            Body = cerl:try_body(Tree),
            %Evars = cerl:try_evars(Tree),
            Handler = cerl:try_handler(Tree),
            traverse_list([Arg, Body, Handler], St0);
        alias ->
            Var = cerl:alias_var(Tree),
            Pat = cerl:alias_pat(Tree),
            traverse_list([Var, Pat], St0);
        literal ->
            St0;
        var ->
            St0
    end.

traverse_list(Trees, St0) ->
    lists:foldl(fun traverse/2, St0, Trees).

resolve_fun_binding(Var, #state{mfa = {M,_,_}} = St) ->
    case lookup_var(Var, St) of
        {ok, {_,_,_}=FunMFA} ->
            FunMFA;
        error ->
            case Var of
                {F,A} ->
                    %% {Function, Arity} tuples represent module-level
                    %% function variables, but can also be functions
                    %% bound in letrec statements, which are resolved
                    %% to unique MFAs here.
                    {M,F,A};
                _ ->
                    Var
            end
    end.


%% @doc Try to promote dependencies to nested functions to the current one.
%%
%% This only works for nested functions which depend on free variables, e.g:
%% `filter(Pred, List) when is_function(Pred, 1) ->'
%% `    [ E || E <- List, Pred(E) ].'
%% Here, the nested function created for the list comprehension, depends on
%% the free variable Pred, which, in the context of `filter/2' can be
%% resolved to `{arg, 1}'.
%% TODO: Make it work for arbitrary levels of nesting.
-spec promote_free_deps(mfa(), state()) -> {ok, [context()]} | failed.
promote_free_deps(Fun, #state{table = Tab} = St) ->
    case dict:find(Fun, Tab) of
        {ok, [_|_]=Ctx} ->
            Pred = fun({ok, _}) -> true; (error) -> false end,
            case lists:partition(Pred, [lookup_free(C, St) || C <- Ctx]) of
                {Resolved, []} ->
                    {ok, [R || {ok, R} <- Resolved]};
                _Unresolved ->
                    failed
            end;
        _Other ->
            failed
    end.

-spec lookup_free(context(), state()) ->
    {ok, {local, mfa(), [ctx_arg()]} | arg_dep()} | error.
lookup_free({free, {Var, Args}}, #state{} = St) ->
    case lookup_var(Var, St) of
        {ok, {_,_,_}=MFA} ->
            {ok, {local, MFA, Args}};
        error ->
            case lookup_arg(Var, St) of
                {ok, N} ->
                    {ok, {arg, N}};
                error ->
                    error
            end
    end;
%% XXX: Propagate primop dependencies, otherwise this does
%% not work anymore. Not sure the right way to go though.
lookup_free({primop, {_, _}, _} = P, _St) ->
    {ok, P};
lookup_free(_C, _St) ->
    error.

%% @doc Convert unresolved local dependencies to positions in the
%% in the argument list or mark as free variables, whenever possible.
postprocess_locals(#state{ctx = Ctx} = St) ->
    lists:usort([postprocess_locals(C, St) || C <- Ctx]).

postprocess_locals({local, Var, Args} = Value, St)
  when (is_atom(Var) orelse is_integer(Var)) ->
    case is_free(Var, St) of
        true ->
            {free, {Var, Args}};
        false ->
            case lookup_arg(Var, St) of
                {ok, N} ->
                    {arg, N};
                error ->
                    Value
            end
    end;
postprocess_locals(Other, _St) ->
    Other.

is_free(Var, #state{free = Free}) ->
    ordsets:is_element(Var, Free).

enumerate(List) ->
    enumerate(List, 1, []).

enumerate([], _, Acc) ->
    lists:reverse(Acc);
enumerate([H|T], N, Acc) ->
    enumerate(T, N+1, [{N, H}|Acc]).


%% Link variable names to the corresponding MFA, whenever possible.
%% If a name is bound to a different fun, the link will be replaced.
handle_let(Tree, #state{vars = Vs} = St0) ->
    Arg = cerl:let_arg(Tree),
    Body = cerl:let_body(Tree),
    %% It would be nice if 'case' nodes were analysed deeper. This would
    %% require keeping track of a `union' of values for the bound variable,
    %% which complicates matters, so it's skipped for the time being.
    S = case cerl:let_arity(Tree) of
        1 ->
            [Name] = [cerl:var_name(V) || V <- cerl:let_vars(Tree)],
            case cerl:type(Arg) of
                'fun' ->
                    {FunMFA, St1} = gen_fun_uid(Arg, St0),
                    #state{table = Tab} = analyse(Arg, St1#state{mfa = FunMFA}),
                    %% Build on St1 because we need the updated count field.
                    St1#state{table = Tab, vars = map_add(Name, FunMFA, Vs)};
                'call' ->
                    case call_mfa(Arg) of
                        {erlang, make_fun, 3} ->
                            Args = cerl:call_args(Arg),
                            case lists:all(fun cerl:is_literal/1, Args) of
                                true ->
                                    [M, F, A] = [cerl:concrete(L) || L <- Args],
                                    St0#state{vars = map_add(Name, {M,F,A}, Vs)};
                                false ->
                                    St0
                            end;
                        _ ->
                            St0
                    end;
                _T ->
                    St0
            end;
        _N ->
            %% e.g. test/values.erl when compiled with copt.
            St0
    end,
    if S =/= St0 ->
            traverse(Body, S);
        true ->
            traverse_list([Arg, Body], S)
    end.


call_mfa(Tree) ->
    true = cerl:is_c_call(Tree),
    M = cerl:call_module(Tree),
    F = cerl:call_name(Tree),
    A = cerl:call_arity(Tree),
    %% get_name/1 marks variable in calls to easily distinguish them
    %% from regular calls. Maybe there should be a special context type
    %% for this as well.
    {get_name(M), get_name(F), A}.

-spec get_name(cerl:c_var() | cerl:c_literal()) -> {var, atom()} | atom().
get_name(Tree) ->
    case cerl:type(Tree) of
        var ->
            {var, cerl:var_name(Tree)};
        literal ->
            cerl:concrete(Tree)
    end.

handle_letrec(Tree, #state{} = St0) ->
    Defs = cerl:letrec_defs(Tree),
    Body = cerl:letrec_body(Tree),
    {FunDefs, St1} = lists:foldl(fun letrec_names/2, {[], St0}, Defs),
    #state{table = Tab} = lists:foldl(fun letrec_analyse/2, St1, FunDefs),
    %% Analysis is continued with the old state.
    traverse(Body, St1#state{table = Tab}).

letrec_names({Var, Fun}, {Acc, #state{vars = Vs} = St0}) ->
    VarName = cerl:var_name(Var),
    {MFA, St1} = gen_fun_uid(Fun, St0),
    St2 = St1#state{vars = map_add(VarName, MFA, Vs)},
    {[{MFA, Fun}|Acc], St2}.

letrec_analyse({MFA, Fun}, St0) ->
    analyse(Fun, St0#state{mfa = MFA}).


%% @doc Generate a unique function name, making sure it doesn't clash
%% with any of the names in the module's namespace.

-spec gen_fun_uid(cerl:c_fun(), state()) -> {mfa(), state()}.

gen_fun_uid(Tree, #state{mfa = {M,F,A}, count = C0, names = Names} = St) ->
    true = cerl:is_c_fun(Tree),
    {Name, C1} = gen_fun_uid(str("~s_~B", [F, A]), C0, Names),
    Uid = {M, Name, cerl:fun_arity(Tree)},
    {Uid, St#state{count = C1}}.

gen_fun_uid(Fun, Count, Names) ->
    N = str("~s-~B", [Fun, Count]),
    case ordsets:is_element(N, Names) of
        true ->
            gen_fun_uid(Fun, Count + 1, Names);
        false ->
            {list_to_atom(N), Count + 1}
    end.


%% XXX: Context arguments are probably meaningless for primops, however
%% they make handling consistent with that of remote/local dependencies.
handle_primop(Tree, #state{ctx = Ctx} = St0) ->
    true = cerl:is_c_primop(Tree),
    Name = cerl:concrete(cerl:primop_name(Tree)),
    Arity = cerl:primop_arity(Tree),
    St0#state{ctx = ctx_add({primop, {Name, Arity}, []}, Ctx)}.


%% @doc Find any arguments in the list which represents a function.
%% Return a list of {Position, MFA} tuples.
%-spec harvest_args(cerl:cerl(), state()) -> [ctx_arg()]. %% dialyzer chokes on cerl().
harvest_args(Args, #state{} = St) ->
    Vars = [{N, cerl:var_name(V)} || {N, V} <- enumerate(Args),
                                     cerl:is_c_var(V)],
    lists:usort(lists:foldl(
            fun(NV, Acc) -> find_arg(NV, St, Acc) end, [], Vars)).

find_arg({N, {F, A} = Var},  #state{mfa = {M,_,_}, vars = Vs}, Acc) ->
    %% No need to lookup Var here, since it represents `letrec' generated
    %% funs, which will not be passed around as arguments.
    error = map_lookup(Var, Vs),
    [{N, {M,F,A}}|Acc];
%% It appears newer versions of the compiler use variable names like _4540,
%% which are then stored as integers.
find_arg({N, Var}, #state{} = St, Acc)
  when (is_atom(Var) orelse is_integer(Var)) ->
    case lookup_var(Var, St) of
        {ok, {_,_,_}=ArgMFA} ->
            [{N, ArgMFA}|Acc];
        error ->
            case lookup_arg(Var, St) of
                {ok, From} ->
                    [{arg, {From, N}}|Acc];
                error ->
                    Acc
            end
    end.


-spec ctx_new() -> [].
ctx_new() ->
    ordsets:new().

-spec ctx_add(context(), [context()]) -> [context()].
ctx_add(Value, Ctx) ->
    ordsets:add_element(Value, Ctx).

lookup_var(Name, #state{vars = VarMap} = St) ->
    Search = fun(N) -> map_lookup(N, VarMap) end,
    name_or_alias(Name, St, Search).


lookup_arg(Name, #state{args = ArgMap} = St) ->
    Search = fun(N) -> map_lookup(N, ArgMap) end,
    name_or_alias(Name, St, Search).


-spec map_new() -> [].
map_new() ->
    [].

-spec map_add(map_key(), map_val(), map()) -> map().
map_add(Key, Val, Map) ->
    [{Key, Val}|Map].

-spec map_lookup(map_key(), map()) -> error | {ok, map_val()}.
map_lookup(Key, Map) ->
    case lists:keyfind(Key, 1, Map) of
        false ->
            error;
        {Key, Value} ->
            {ok, Value}
    end.


-spec name_or_alias(cerl:var_name(), state(),
    fun((cerl:var_name()) -> error | {ok, any()})) -> error | {ok, any()}.

name_or_alias(Name, St, Fun) ->
    case Fun(Name) of
        error ->
            case lookup_alias(Name, St) of
                {ok, Alias} ->
                    Fun(Alias);
                error ->
                    error
            end;
        Result ->
            Result
    end.


lookup_alias(Name, #state{aliases = Aliases}) ->
    dict:find(Name, Aliases).


state_new(Options, Names, Table) ->
    #state{opts  = Options,
           names = Names,
           table = Table}.


%% @spec propagate(dict(), purity_utils:options()) -> dict()
%%
%% @doc Return a version of the lookup table with dependencies
%% converted to concrete results.
%%
%% The dependency lists returned by `module/3' are converted to concrete
%% values whenever possible, depending on the particular set of options
%% as well.
%%
%% @see module/3
%% @see modules/3

-spec propagate(dict(), purity_utils:options()) -> dict().

propagate(Tab0, Opts) ->
    Fse = {false, fmt_dep(side_effects)},
    Fnd = {false, fmt_dep(non_determinism)},
    Fex = {false, fmt_dep(exceptions)},
    Vals = case option(purelevel, Opts, 1) of
        1 ->
            [Fse, true, true];
        2 ->
            [Fse, Fnd, true];
        3 ->
            [Fse, Fnd, Fex]
    end,
    KeyVals = lists:zip([side_effects, non_determinism, exceptions], Vals),
    Tab1 = merge(add_bifs(Tab0), dict:from_list(?PREDEF ++ KeyVals)),
    converge_pst(#pst{revs = purity_utils:rev_deps(Tab1), table = Tab1}).

%% Higher order analysis should replace call_site analysis completely
%% at some point, but currently it is still useful for functions which
%% take more than one function as argument, or have other dependencies
%% as well.
propagate_loop(#pst{table = Tab} = St0) ->
    {Pure, Impure} = collect_concrete(Tab),
    St1 = propagate_impure(St0#pst{funs = Impure}),
    St2 = propagate_pure(St1#pst{funs = Pure}),
    St3 = call_site_analysis(St2),
    St4 = higher_analysis(St3),
    St5 = mutual_analysis(St4),
    St5.

converge_pst(#pst{table = Tab} = St0) ->
    case propagate_loop(St0) of
        #pst{table = Tab} ->
            Tab;
        St1 ->
            converge_pst(St1)
    end.

%% @doc Return two lists of functions with concrete values, one for 
%% pure and one for impure ones.
collect_concrete(Tab) ->
    dict:fold(fun collect_concrete/3, {[], []}, Tab).

collect_concrete(F, true, {Pure, Impure}) ->
    {[F|Pure], Impure};
collect_concrete(F, [], {Pure, Impure}) ->
    {[F|Pure], Impure};
collect_concrete(F, {false, _}, {Pure, Impure}) ->
    {Pure, [F|Impure]};
collect_concrete(_, _, Acc) ->
    Acc.

%% The set of previously visited functions is necessary in order
%% to avoid endless loops caused by mutually recursive functions.
propagate_pure(#pst{funs = []} = St) ->
    St;
propagate_pure(#pst{funs = Funs0, prev = Set0, table = Tab0} = St) ->
    Tab1 = remove_from_ctx(Tab0, Funs0),
    Set1 = add_elements(Funs0, Set0),
    Deps = [D || F <- Funs0, D <- fetch_deps(F, St#pst.revs),
                 not sets:is_element(D, Set1),
                 is_pure(dict:fetch(D, Tab1))],
    propagate_pure(St#pst{funs = lists:usort(Deps), prev = Set1, table = Tab1}).

%% When propagating impure results, try to keep track of the reason
%% each function is impure, i.e. the impure expressions it directly
%% depends on. Some of these are lost because they are contained in
%% the previously visited set.
propagate_impure(#pst{funs = []} = St) ->
    St;
propagate_impure(#pst{funs = Funs0, table = Tab, prev = Set0} = St) ->
    Deps = [{F, fetch_deps(F, St#pst.revs)} || F <- Funs0],
    Set1 = add_elements(Funs0, Set0),
    %% Using Set0 instead of Set1 here should not influence the final
    %% outcome. However it would keep track of impure reasons in more
    %% detail, but it would also be slower, since more iterations are
    %% required.
    Funs1 = lists:usort([D || {_F, Ds} <- Deps, D <- Ds,
                              not sets:is_element(D, Set0)]),
    propagate_impure(St#pst{funs = Funs1, prev = Set1,
                            table = update(Tab, with_reasons(Deps))}).

add_elements(Elements, Set) ->
    lists:foldl(fun sets:add_element/2, Set, Elements).

fetch_deps(Key, DepMap) ->
    case dict:find(Key, DepMap) of
        {ok, Deps} ->
            Deps;
        error ->
            []
    end.

%% @doc Convert a list of impure functions and their reverse dependencies
%% to a list of those dependencies annotated with the reason they are impure.
with_reasons(Vals) ->
    %% Map each dep back to the list of functions it depends on, to form
    %% the reason of impurity.
    D = lists:foldl(fun map_reverse/2, dict:new(), Vals),
    dict:fold(fun(F, Ds, A) -> [{F, {false, fmt(Ds)}} | A] end, [], D).

map_reverse({F, Deps}, D0) ->
    lists:foldl(fun(D, D1) -> dict_cons(D, F, D1) end, D0, Deps).

fmt(Deps) ->
    %% Keep a list of sorted, unique references.
    Ds = [fmt_dep(D) || D <- lists:usort(Deps)],
    "call to impure " ++ string:join(Ds, ", ").

fmt_dep({erl, A}) ->
    str("~p expression", [A]); % Preserve quotes.
fmt_dep(side_effects) ->
    "side-effects";
fmt_dep(exceptions) ->
    "exceptions";
fmt_dep(non_determinism) ->
    "non-determinism";
fmt_dep(Other) ->
    fmt_mfa(Other).


%% @doc Remove `Funs' from any context dependencies in the `Table'.
remove_from_ctx(Table, Funs) ->
    Set = sets:from_list(Funs),
    Pred = fun({_Type, MFA, _Args}) -> not sets:is_element(MFA, Set);
              %% This covers special dependencies and expressions like
              %% {erl,'catch'}. Other stuff like {arg,N} will not be
              %% part of the set so they will remain.
              (Other) -> not sets:is_element(Other, Set) end,
    dict:map(
        fun(_F, Ctx) when is_list(Ctx) -> ordsets:filter(Pred, Ctx);
           (_F, Val) -> Val end,
        Table).

is_pure(true) ->
    true;
is_pure([]) ->
    true;
is_pure(_) ->
    false.


higher_analysis(#pst{table = Tab, revs = Rev} = St) ->
    G = purity_hofs:make_arg_graph(Tab, Rev),
    St#pst{table = dict:map(
            fun(F, V) -> higher_analysis(F, V, Tab, G) end, Tab)}.

higher_analysis(Fun, Val, Table, Graph) ->
    %purity_hofs:to_dot(Graph, str("graphs/graph_~4..0b.dot", [purity_utils:count(hofs)])),
    case purity_hofs:higher_analysis(Fun, remove_args(Val), Table, Graph) of
        {resolved, pure} ->
            true;
        {resolved, impure} ->
            %% TODO: Keep track of the offending function!
            {false, "impure call to higher order function"};
        unresolved ->
            Val
    end.


call_site_analysis(#pst{table = Tab} = St) ->
    St#pst{table = dict:map(
            fun(_, V) -> call_site_analysis(V, Tab) end, Tab)}.

%% TODO:
%% - Clean up if possible.
call_site_analysis(Ctx0, Table) when is_list(Ctx0) ->
    Ctx1 = [call_site_analysis1(remove_args(C), Table) || C <- Ctx0],
    case [C || C <- Ctx1, C =/= true] of
        [] ->
            %% XXX This covers two cases:
            %% - Call site analysis of all pure results.
            %% - Call site analysis of pure functions with [] as their value.
            %% Thus, conversion of `[]' to `true' takes place here.
            true;
        Ctx2 ->
            case lists:keyfind(false, 1, Ctx2) of
                false ->
                    %% Return the possibly reduced context.
                    Ctx2;
                {false, _Reason} = Result ->
                    Result
            end
    end;
call_site_analysis(Value, _Table) ->
    Value.

call_site_analysis1({_Type, MFA, Args} = Value, Table) ->
    case analyse_call(MFA, Args, Table) of
        failed ->
            Value;
        Result ->
            Result
    end;
call_site_analysis1(Value, _Table) ->
    Value.

%% @doc Return true/{false, Reason} or failed.
analyse_call(CallMFA, Args, Table) ->
    case dict:find(CallMFA, Table) of
        {ok, [_|_] = Ctx} ->
            case find_matching_args(Ctx, Args) of
                none ->
                    failed;
                %% The only way this can be resolved to a concrete value
                %% is if an impure result is found, or *all* calls are pure.
                {Found, MFAs} ->
                    TheirPurity = [dict:find(F, Table) || F <- MFAs],
                    case {Found, pick_only_concrete(TheirPurity)} of
                        {all, pure} ->
                            true;
                        {_Any, impure} ->
                            {false, "impure call to " ++ fmt_mfa(CallMFA)};
                        _AnythingElse ->
                            failed
                    end
            end;
        {ok, undefined} ->
            failed;
        %% Any other values (true/false) will have been propagated by now.
        error ->
            failed
    end.


pick_only_concrete(Values) ->
    reduce(Values, pure).

reduce([{ok, true}|T], pure) ->
    reduce(T, pure);
reduce([{ok, []}|T], pure) ->
    reduce(T, pure);
reduce([{ok, {false, _}}|_], _) ->
    impure;
reduce([_|T], _) ->
    reduce(T, other);
reduce([], Result) ->
    Result.


find_matching_args(ArgDeps, Args) ->
    case match_args(ArgDeps, Args, [], false) of
        {[], _} ->
            none;
        {Matches, false} ->
            {all, Matches};
        {Matches, true} ->
            {some, Matches}
    end.

%% FIXME: Rewrite, don't depend on sorted context.
match_args([{arg, N}|T1], [{N, MFA}|T2], Matches, Rem) ->
    match_args(T1, T2, [MFA|Matches], Rem);
match_args([{arg, N1}|_]=L1, [{N2, _}|T2], Matches, Rem) when N1 > N2 ->
    match_args(L1, T2, Matches, Rem);
match_args([{arg, N1}|T1], [{N2, _}|_]=L2, Matches, _Rem) when N1 < N2 ->
    match_args(T1, L2, Matches, true);
match_args([], _, Matches, Rem) ->
    {Matches, Rem};
match_args(_, [], Matches, _Rem) ->
    {Matches, true};
match_args([_|T1], L2, Matches, _Rem) -> %% Non-arg dependencies.
    match_args(T1, L2, Matches, true).


%% @doc Detect functions which remain unresolved solely because of
%% mutually recursive dependencies.
%%
%% The process is started by selecting those functions whose sole
%% dependencies are other functions in the same (call graph) cycle.
%% Then, this set of functions is gradually reduced, by filtering
%% out any functions whose dependencies are not themselves part of
%% the set. Only the surviving functions can be safely marked pure.
mutual_analysis(#pst{cycles = undefined, table = T} = St) ->
    %% Cache mapping of mutually recursive functions to their cycle.
    %% This is only a minor optimisation, the biggest gain is from
    %% waiting up to this point in the propagation to built the map.
    mutual_analysis(St#pst{cycles = build_cycle_map(T)});
mutual_analysis(#pst{cycles = C, table = T} = St) ->
    Funs = [F || {F, _} <- converge(fun mutual_selection/1,
                                    mutual_candidates(C, T))],
    St#pst{table = update(T, Funs, true)}.

mutual_candidates(Cycles, Tab) ->
    dict:fold(fun(F, V, A) -> mutual_candidates(F, V, A, Cycles) end, [], Tab).

mutual_candidates(F, Ctx, Acc, CM) when is_list(Ctx) ->
    case just_deps(Ctx, []) of
        {ok, Deps} ->
            case all_mutual(F, Deps, CM) of
                true ->
                    [{F, Deps}|Acc];
                false ->
                    Acc
            end;
        error ->
            Acc
    end;
mutual_candidates(_, _, Acc, _) ->
    Acc.

%% @doc If the dependency list consists exclusively of dependencies to
%% other functions, return their MFAs, otherwise fail.
just_deps([{_, {_,_,_} = F, _}|T], A) ->
    just_deps(T, [F|A]);
just_deps([], A) ->
    {ok, lists:usort(A)};
just_deps(_, _) ->
    error.

all_mutual(Fun, Deps, Cycles) ->
    case dict:find(Fun, Cycles) of
        {ok, _CycleID} = Result ->
            lists:all(fun(F) -> dict:find(F, Cycles) =:= Result end, Deps);
        error ->
            false
    end.

mutual_selection(FunDeps) ->
    Set = sets:from_list([F || {F, _} <- FunDeps]),
    [V || {_, Deps} = V <- FunDeps,
        lists:all(fun(D) -> sets:is_element(D, Set) end, Deps)].

converge(Fun, Data) ->
    case Fun(Data) of
        Data ->
            Data;
        Next ->
            converge(Fun, Next)
    end.

build_cycle_map(Tab) ->
    cycle_map(digraph_utils:cyclic_strong_components(dependency_graph(Tab))).

%% @doc Return a mapping of functions to the specific cycle in the call
%% graph they are part of, if any.
cycle_map(CyclicComponents) ->
    %% There's no need to keep the actual cycles, just a unique reference.
    dict:from_list([{F, N} || {N, CC} <- enumerate(CyclicComponents), F <- CC]).

dependency_graph(Table) ->
    dict:fold(fun add_edges/3, digraph:new(), Table).

add_edges(Fun, Ctx, Graph) when is_list(Ctx) ->
    MFAs = [MFA || {_, {_,_,_}=MFA, _} <- Ctx],
    digraph:add_vertex(Graph, Fun),
    lists:foreach(
        fun(F) ->
                digraph:add_vertex(Graph, F),
                digraph:add_edge(Graph, Fun, F) end, MFAs),
    Graph;
add_edges(_, _, Graph) ->
    Graph.


%%% Various helpers. %%%

update(Table, KeyVals) ->
    lists:foldl(fun({K, V}, D) -> dict:store(K, V, D) end, Table, KeyVals).

update(Table, Funs, Value) ->
    update(Table, [{F, Value} || F <- Funs]).

option(Name, Options, Default) ->
    proplists:get_value(Name, Options, Default).

%% @doc Merge two dictionarys keeping values from the second one when
%% conflicts arise.
merge(D1, D2) ->
    dict:merge(fun(_K, _V1, V2) -> V2 end, D1, D2).

%% @doc Merge a non-empty list of dictionaries.
merge([D0|Ds]) ->
    lists:foldl(fun merge/2, D0, Ds).

