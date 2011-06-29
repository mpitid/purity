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
-export([propagate/2, propagate_termination/2, propagate_purity/2,
         propagate_both/2, find_missing/1]).
-export([analyse_changed/3]).

-export([propagate_new/2, purity_of/2, convert/2]).

-import(purity_utils, [fmt_mfa/1, str/2]).
-import(purity_utils, [remove_args/1, dict_cons/3, filename_to_module/1]).

-export_type([pure/0]).

-ifdef(TEST).
-include("purity_tests.hrl").
-endif.

%% Besides built-in functions, a select few of Erlang expressions
%% may influence the purity if functions.
-define(PREDEF, [
        {{erl,{'receive',finite}},    [side_effects]},
        {{erl,{'receive',infinite}},  [side_effects]},
        {{erl,'catch'},               [non_determinism]}]).
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
                 | {erl, {'receive', finite | infinite} | 'catch'}
                 | special().


-type map_key() :: cerl:var_name().
-type map_val() :: mfa() | pos_integer().
-type map()     :: [{map_key(), map_val()}].

-type sub() :: {dict(), dict()}.

-type pure()    :: true
                 | false | {false, string() | binary()}
                 | [context()]
                 | undefined.


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
%% subs     - Keep track of variables which are subsets of arguments
%% aliases  - Keep track of aliases to variables for looking up vars/args
%%            more effectively
%% free     - An ordered set of free variables for the current function
%%            (only relevant to nested functions of course)
%% nested   - Keep track of the MFAs of any nested functions defined in
%%            the body of the currently analysed one.
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
                subs    = sub_new()  :: sub(),
                aliases = dict:new() :: dict(),
                free    = []         :: [cerl:var_name()],
                nested  = []         :: [mfa()],
                count   = 1          :: pos_integer(),
                names   = []         :: [atom()],
                opts    = []         :: [any()],
                table   = dict:new() :: dict()}).

-type state() :: #state{}.


%% State record for propagation of dependency lists to pureness values.
-record(pst, {funs = []         :: [mfa()],
              prev = sets:new() :: set(),
              revs              :: dict(),
              rsns = false      :: boolean(),
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
-spec analyse_changed(purity_plt:changed_files(), purity_utils:options(), purity_plt:plt()) -> purity_plt:plt().

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
    Module = cerl:concrete(cerl:module_name(Core)),
    Defs = [{cerl:var_name(Var), Fun} || {Var, Fun} <- cerl:module_defs(Core)],
    Names = lists:foldl(
        fun({{F,_},_}, Set) -> ordsets:add_element(atom_to_list(F), Set) end,
        ordsets:new(),
        Defs),
    St0 = state_new(Options, Names, purity_utils:delete_modules(Tab0, [Module])),
    Fun = fun({{F,A}, Fun}, St) ->
            analyse(Fun, St#state{mfa = {Module, F, A},
                                  nested = [],
                                  vars = map_new(),
                                  subs = sub_new(),
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
    prune_merge(Tab0,
                lists:zip([filename_to_module(M) || M <- Modules],
                          purity_utils:pmap({purity, panalyse},
                                            [Options], Modules, CPUs))).

%% Before merging the tables remove any values with the same module
%% that may be contained already. To make this faster first index
%% on the module, so that there is no need to traverse the whole
%% table to remove the values.
prune_merge(Tab, MTs) ->
    ungroup(update(group(Tab), MTs)).

%% Group all values sharing the same module to a single key.
group(Tab) ->
    dict:fold(fun group_add/3, dict:new(), Tab).

group_add({M,_,_}=K, V, T) ->
    dict_cons(M, {K, V}, T);
group_add(K, V, T) ->
    %% Make sure non-MFA keys are not overwritten, hence the tuple.
    dict_cons({non_mfa}, {K, V}, T).

ungroup(Tab) ->
    %% The values of the first table are grouped as a list,
    %% while those of the rest as dicts.
    dict:fold(fun(_, Vs, T) when is_list(Vs) -> update(T, Vs);
                 (_, Vs, T) -> dict:fold(fun dict:store/3, T, Vs) end,
              dict:new(), Tab).


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


analyse(Function, St0) ->
    St1 = St0#state{ctx = ctx_new(),
                    args = fetch_arg_vars(Function),
                    free = cerl_trees:free_variables(Function),
                    count = 1},
    St2 = traverse(cerl:fun_body(Function), St1),
    St3 = promote_nested(St2#state{ctx = postprocess_locals(St2)}),
    St3#state{table = dict:store(St3#state.mfa, St3#state.ctx, St3#state.table)}.


fetch_arg_vars(Fun) ->
    Args = cerl:fun_vars(Fun),
    %% XXX: Breaks the map contract.
    [{cerl:var_name(V), N} || {N, V} <- enumerate(Args), cerl:is_c_var(V)].


%% @doc Traverse a Core Erlang AST and collect necessary information
%% in the form of a dependency list.
traverse(Tree, #state{ctx = Ctx} = St0) ->
    case cerl:type(Tree) of
        seq ->
            Arg = cerl:seq_arg(Tree),
            Body = cerl:seq_body(Tree),
            traverse_list([Arg, Body], St0);
        'case' ->
            handle_case(Tree, St0);
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
            Type = receive_type(Timeout),
            St1 = St0#state{ctx = ctx_add({erl, {'receive', Type}}, Ctx)},
            traverse_list(Clauses ++ [Timeout, Action], St1);
        'apply' ->
            Op = cerl:apply_op(Tree),
            OpName = cerl:var_name(Op),
            Fun = resolve_fun_binding(OpName, St0),
            Args = handle_args(Fun, cerl:apply_args(Tree), St0),
            St0#state{ctx = ctx_add({local, Fun, Args}, Ctx)};
        'call' ->
            Args = handle_args(call_mfa(Tree), cerl:call_args(Tree), St0),
            St0#state{ctx = ctx_add({remote, call_mfa(Tree), Args}, Ctx)};
        'fun' ->
            %% This mostly comes from nested funs as return values, etc.
            %% There's not much use for these the way analysis is structured,
            %% but analyse them anyway, for maximum coverage.
            {FunMFA, St1} = gen_fun_uid(Tree, St0),
            #state{table = Tab, nested = Nst} =
                analyse(Tree, St1#state{mfa = FunMFA}),
            St0#state{table = Tab, nested = nst_add(FunMFA, Nst)};
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

%% @doc A receive statement is considered finite only if it has a
%% constant literal as a timeout value. Missing `after' clauses
%% are translated to a timeout of `infinity' in Core Erlang.
receive_type(Tree) ->
    case cerl:is_literal(Tree) of
        true ->
            case cerl:concrete(Tree) of
                infinity ->
                    infinite;
                _Val ->
                    finite
            end;
        false -> % var, call or apply
            infinite
    end.

%% @doc Flatten dependencies to nested functions.
%%
%% Consider the following example: ``` a(F, L) -> [F(E) || E <- L]. '''
%% The `a' function depends on the nested `a_2-1/1' function, which in
%% turn depends on the free variable `F'. Since that variable is bound
%% in the scope of `a', flattening the dependencies will resolve it to
%% `{arg, 1}'. All other dependencies are propagated unchanged, with
%% the exception of self calls which are transformed to self calls of
%% the parent function in order to preserve the semantics of the analysis
%% (in the case of HOFs, but also with regard to termination analysis
%% which is not implemented yet).
promote_nested(#state{mfa = Fun, ctx = Ctx} = St) ->
    {Nested, Rest} = lists:partition(fun(D) -> is_nested(D, St) end, Ctx),
    Promoted = lists:flatten([map_nested(Fun, N, St) || N <- Nested]),
    St#state{ctx = ctx_rem(remove, ctx_add_many(Promoted, Rest))}.

is_nested({_, Fun, _}, #state{nested = Nst, mfa = MFA}) ->
    Fun =/= MFA andalso nst_mem(Fun, Nst);
is_nested(_, _) ->
    false.

map_nested(Fun, {_, Dep, _} = Orig, #state{table = Tab} = St) ->
    Vals = [map_nested(Fun, Dep, C, St) || C <- dict:fetch(Dep, Tab)],
    case lists:member(unmappable, Vals) of
        true ->
            %% Some of the values failed to map, restore the original dep.
            [Orig];
        false ->
            Vals
    end.

map_nested(_, _, {free, {Var, _Args}} = Dep, St) ->
    case is_free(Var, St) of
        true -> %% Still a free variable, let the parents handle it.
            Dep;
        false -> %% Bind to argument or fail.
            case lookup_free(Var, St) of
                {ok, {arg, _} = NewDep} ->
                    NewDep;
                error ->
                    unmappable
            end
    end;
map_nested(Fun, _, {Type, Fun, Args} = Dep, St) ->
    %% Dependency on the parent: this should be converted to recursion.
    %% The arguments may contain free variables however, which could be
    %% mapped to concrete arguments of the caller and make the recursive
    %% dependency safe to remove later on.
    case check_passed_args(Fun, Args, St) of
        still_free ->
            Dep;
        unmappable ->
            unmappable;
        NewArgs ->
            {Type, Fun, NewArgs}
    end;
map_nested(_Fun, Dep, {_, Dep, _}, _) ->
    %% Recursion in the nested function. This can only happen with
    %% `letrec', which is generated by Erlang for list comprehensions.
    %% It may be considered terminating since it is over a finite list,
    %% so we don't care about this dependency in any way.
    remove;
map_nested(_, _, {arg, _}, _) ->
    %% Not much we can do if the nested function is a HOF.
    unmappable;
%% Everything else passes through unchanged, just being explicit.
map_nested(_, _, {_, _, _} = Dep, _) ->
    Dep;
map_nested(_, _, {primop, _} = P, _) ->
    P;
map_nested(_, _, {erl, _} = E, _) ->
    E.

check_passed_args(_F, [], _St) ->
    [];
check_passed_args(_, [{arg,{_,_}}|_], _) ->
    %% Converting the argument mapping could be tricky so play it safe.
    unmappable;
check_passed_args(Fun, [{N, {free, Var}}|T], St) ->
    case is_free(Var, St) of
        true ->
            still_free;
        false ->
            case lookup_free(Var, St) of
                error ->
                    unmappable;
                {ok, {arg, K}} ->
                    case check_passed_args(Fun, T, St) of
                        Args when is_list(Args) ->
                            %% All arguments bound, epic win!
                            [{arg, {K, N}}|Args];
                        Fail when is_atom(Fail) ->
                            Fail
                    end
            end
    end.

lookup_free(Var, #state{} = St) ->
    case lookup_arg(Var, St) of
        {ok, N} ->
            {ok, {arg, N}};
        error ->
            error
    end.

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
                    #state{table = Tab, nested = Nst} =
                        analyse(Arg, St1#state{mfa = FunMFA}),
                    %% Build on St1 because we need the updated count field.
                    St1#state{table = Tab, vars = map_add(Name, FunMFA, Vs),
                              nested = nst_add(FunMFA, Nst)};
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
    #state{table = Tab, nested = Nst} =
        lists:foldl(fun letrec_analyse/2, St1, FunDefs),
    %% Analysis is continued with the old state.
    traverse(Body, St1#state{table = Tab,
                             nested = nst_add_many(unzip1(FunDefs), Nst)}).

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

%% @doc Detect simple cases of variables which represent a strict subset of
%% one of the arguments. This is useful for detecting recursive functions
%% which consume one of their arguments, and are therefore guaranteed
%% to terminate (or crash). Currently this works for some cases of lists
%% and binaries.
handle_case(Tree, St0) ->
    true = cerl:is_c_case(Tree),
    Arg = cerl:case_arg(Tree),
    Cls = cerl:case_clauses(Tree),
    %% Since pattern variable names may repeat themselves, use a
    %% distinct subset map for each clause.
    #state{subs = Sm0, args = Args} = St1 = traverse(Arg, St0),
    St2 = lists:foldl(
        fun(Cl, St) ->
                traverse(Cl,
                    St#state{subs = submerge(Args, Sm0, submap(Arg, Cl))}) end,
        St1, Cls),
    %% Restore the original map before return.
    %% Assert that the map of St0 is equal to that of St1.
    #state{subs = Sm0} = St0,
    St2#state{subs = Sm0}.

%% @doc Keep track of two distinct mappings:
%% - From each variable to the one it is a subset of
%% - From each variable to the position of the argument it is a subset of.
%% While only the second mapping is useful, the first is necessary
%% in order to recreate it at each new case clause.
submerge(Args, {Map0, Sub0}, Map1) ->
    Map2 = merge(Map0, Map1),
    {Map2, merge(Sub0, to_argument_map(Args, Map2))}.

%% @doc Generate the mapping of variables to the position of
%% the argument they are a subset of.
to_argument_map(Args, Map) ->
    G = dict:fold(fun make_edge/3, digraph:new(), Map),
    M = lists:foldl(
        fun({A,N}, D) -> update(D, reaching(G, A), N) end,
        dict:new(), Args),
    digraph:delete(G),
    M.

make_edge(V1, V2, G) ->
    digraph:add_edge(G, digraph:add_vertex(G, V1),
                        digraph:add_vertex(G, V2)), G.

reaching(G, A) ->
    digraph_utils:reaching_neighbours([A], G).

submap(Tree, Clause) ->
    Items =
      case cerl:type(Tree) of
          var -> %% single variable match
              find_matching_patterns([Tree], Clause);
          values -> %% tuple match, e.g. function args
              find_matching_patterns(cerl:values_es(Tree), Clause);
          _o ->
              []
      end,
    mapof(Items).

find_matching_patterns(Vals, Clause) ->
    Pats = cerl:clause_pats(Clause),
    case length(Vals) =:= length(Pats) of
        true ->
            [subpattern(V, P)
                || {V, P} <- lists:zip(Vals, [unalias(P) || P <- Pats])];
        false ->
            []
    end.

subpattern(Val, Pat) ->
    case {cerl:type(Val), cerl:type(Pat)} of
        {var, cons} -> %% List pattern match
            mapto(Val, Pat, fun cons_vars/1);
        {var, binary} -> %% Binary pattern match
            mapto(Val, Pat, fun bin_vars/1);
        _o ->
            []
    end.

mapto(Var, Pat, Extract) ->
    Vn = cerl:var_name(Var),
    [{cerl:var_name(V), Vn} || V <- Extract(Pat), cerl:is_c_var(V)].

cons_vars(Tree) ->
    case cerl:type(Tree) of
        cons ->
            [cerl:cons_hd(Tree) | cons_vars(cerl:cons_tl(Tree))];
        _ ->
            [Tree]
    end.

bin_vars(Tree) ->
    [cerl:bitstr_val(B) || B <- cerl:binary_segments(Tree)].

%% @doc Extract the pattern from a variable alias.
unalias(Tree) ->
    case cerl:type(Tree) of
        alias ->
            cerl:alias_pat(Tree);
        _ ->
            Tree
    end.

mapof(Items) -> dict:from_list(lists:flatten(Items)).


%% @doc Add subset information on recursive calls.
%% @see handle_case/2
handle_args(MFA, Args, #state{mfa = MFA} = St) -> %% Recursion
    ordsets:union(harvest_args(Args, St), get_subsets(Args, St));
handle_args(_Call, Args, #state{} = St) ->
    harvest_args(Args, St).

get_subsets(Args, #state{}=St) ->
    ordsets:from_list(oklist([get_subset(V, St) || V <- enum_args(Args)])).

get_subset({N, V}, #state{subs = {_, S}}) ->
    case dict:find(V, S) of
        {ok, N} -> {ok, {sub,N}};
        {ok, _} -> error;
        error -> error end.

oklist(L) ->
    [E || {ok, E} <- L].

enum_args(Args) ->
    [{N, cerl:var_name(A)} || {N, A} <- enumerate(Args), cerl:is_c_var(A)].

%% @doc Find any arguments in the list which represents a function.
%% Return a list of {Position, MFA} tuples.
%-spec harvest_args(cerl:cerl(), state()) -> [ctx_arg()]. %% dialyzer chokes on cerl().
harvest_args(Args, #state{} = St) ->
    lists:usort(lists:foldl(
            fun(NV, Acc) -> find_arg(NV, St, Acc) end, [], enum_args(Args))).

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
                    case is_free(Var, St) of
                        true -> %% Keep track of free vars passed as args
                            [{N, {free, Var}}|Acc];
                        false -> %% Give up...
                            Acc
                    end
            end
    end.


-spec ctx_new() -> [].
ctx_new() ->
    ordsets:new().

-spec ctx_add(context(), [context()]) -> [context()].
ctx_add(Value, Ctx) ->
    ordsets:add_element(Value, Ctx).

ctx_add_many(Values, Ctx) ->
    lists:foldl(fun ctx_add/2, Ctx, Values).

ctx_rem(Value, Ctx) ->
    ordsets:del_element(Value, Ctx).

nst_add(Val, Nst) ->
    ordsets:add_element(Val, Nst).

nst_add_many(Vals, Nst) ->
    lists:foldl(fun nst_add/2, Nst, Vals).

nst_mem(Val, Nst) ->
    ordsets:is_element(Val, Nst).

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

sub_new() -> {dict:new(), dict:new()}.

%% @doc Select the appropriate propagation function or both, depending
%% on the current set of options.
%%
%% @see propagate_purity/2
%% @see propagate_termination/2

-spec propagate(dict(), purity_utils:options()) -> dict().

propagate(Tab, Opts) ->
    case option(both, Opts) of
        true ->
            propagate_both(Tab, Opts);
        false ->
            case option(termination, Opts) of
                true ->
                    propagate_termination(Tab, Opts);
                false ->
                    %propagate_purity(Tab, Opts)
                    propagate_new(Tab, Opts)
            end
    end.


%% @doc Combine the propagation into one function, which is
%% significantly faster. First perform an impure purity propagation,
%% and then run the termination analysis.
-spec propagate_both(dict(), purity_utils:options()) -> dict().

propagate_both(Tab0, Opts) ->
    Tab1 = merge(add_bifs(Tab0), dict:from_list(?PREDEF)),
    Vs =
        case option(purelevel, Opts, 1) of
          1 -> [false, true, true];
          2 -> [false, false, true];
          3 -> [false, false, false]
      end,
    %% Note that 'receive' will be covered by side_effects.
    KVs = lists:zip([side_effects, non_determinism, exceptions], Vs),
    Tab2 = update(Tab1, KVs),
    St0 = #pst{funs = collect_impure(Tab2),
               revs = purity_utils:rev_deps(Tab2),
               rsns = option(with_reasons, Opts),
               table = Tab2},
    St1 = propagate_impure(St0),
    Tab3 = remove_selfrec(termination, St1#pst.table),
    Funs = recursive_functions(Tab3),
    Tab4 = update(Tab3, Funs, false),
    converge_pst(fun propagate_termination_loop/1,
                 St1#pst{funs = Funs, table = Tab4}).

collect_impure(Tab) ->
    dict:fold(fun collect_impure/3, [], Tab).

collect_impure(F, V, A) ->
    case impure_val(V) of
        true -> [F|A];
        false -> A
    end.


%% @doc Crude and very conservative termination analysis.
%%
%% A function is considered non-terminating if it calls itself,
%% has a receive statement with a potentially infinite timeout, or
%% depends on another function which is non-terminating. Certain
%% cases of functions which consume one of their arguments are
%% also detected and considered terminating.

-spec propagate_termination(dict(), purity_utils:options()) -> dict().

propagate_termination(Tab0, Opts) ->
    %% All BIFs are considered terminating, but we have to keep track
    %% of higher order BIFs too.
    Tab1 = merge(add_bifs(Tab0), dict:from_list(?PREDEF)),
    KeyVals = [
        {side_effects, true}, {non_determinism, true}, {exceptions, true},
        {{erl, {'receive', infinite}}, false}],
    Tab2 = remove_selfrec(termination, merge(Tab1, dict:from_list(KeyVals))),
    Funs = recursive_functions(Tab2),
    Tab3 = update(Tab2, Funs, {false, <<"recursion">>}),
    converge_pst(fun propagate_termination_loop/1,
                 #pst{funs = Funs, table = Tab3,
                      rsns = option(with_reasons, Opts),
                      revs = purity_utils:rev_deps(Tab3)}).

propagate_termination_loop(#pst{table = Tab0} = St0) ->
    {Pure, Impure} = collect_concrete(Tab0),
    St1 = propagate_impure(St0#pst{funs = Impure}),
    St2 = propagate_pure(St1#pst{funs = Pure}),
    St3 = call_site_analysis(St2),
    St4 = higher_analysis(St3),
    St4.

recursive_functions(Tab) ->
    %% This could also be expanded with digraph_utils:reaching,
    %% but there is no performance gain.
    [F || C <- digraph_utils:cyclic_strong_components(dependency_graph(Tab)),
          F <- C].

%% @spec propagate_purity(dict(), purity_utils:options()) -> dict()
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

-spec propagate_purity(dict(), purity_utils:options()) -> dict().

propagate_purity(Tab0, Opts) ->
    Vs =
      case option(purelevel, Opts, 1) of
          1 -> [false, true, true];
          2 -> [false, false, true];
          3 -> [false, false, false]
      end,
    KVs = lists:zip([side_effects, non_determinism, exceptions], Vs),
    Tab1 = merge(add_bifs(Tab0), dict:from_list(?PREDEF ++ KVs)),
    Tab2 = remove_selfrec(purity, Tab1),
    converge_pst(fun propagate_loop/1,
                 #pst{revs = purity_utils:rev_deps(Tab2),
                      table = Tab2, rsns = option(with_reasons, Opts)}).

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


%%% Recursion Handling %%%

remove_selfrec(purity, Tab) ->
    dict:map(fun remove_selfrec_p/2, Tab);
remove_selfrec(termination, Tab) ->
    dict:map(fun remove_selfrec_t/2, Tab).

%% Observing that only the purity of certain higher order functions
%% may depend on recursive dependencies, remove them from all other
%% cases to simplify the rest of purity analysis.
remove_selfrec_p(F, C) when is_list(C) ->
    Keep =
      case is_hof(C) of
          true ->
              Exp = [N || {arg,N} <- C],
              fun({_, D, Args}) when F =:= D ->
                      passes_unknown_fun(Args, Exp);
                 (_) -> true end;
          false ->
              fun(D) -> not selfrec(F, D) end
      end,
    [D || D <- C, Keep(D)];
remove_selfrec_p(_, V) -> V.

%% @doc Remove any self-recursive dependencies which consume one of
%% their arguments.
remove_selfrec_t(F, C) when is_list(C) ->
    case is_hof(C) andalso prevent_removal(F, C) of
        true ->
            clear_sub(C);
        false ->
            remove_selfrec_with_subset(F, C)
    end;
remove_selfrec_t(_, V) -> V.

remove_selfrec_with_subset(F, C) ->
    RecArgs = [A || {_, D, A} <- C, D =:= F],
    C1 =
      case all_subsets(RecArgs) andalso no_high_callsite(RecArgs) of
          true ->
              [D || D <- C, not selfrec(F, D)];
          false ->
              C
      end,
    %% Subset information is no longer useful so remove it.
    lists:usort(clear_sub(C1)).

selfrec(F, {_, F, _}) ->
    true;
selfrec(_, _) ->
    false.

%% Prevent subset recursion removal for hofs which pass unknown
%% functions to the recursive call.
prevent_removal(F, C) ->
    Exp = [N || {arg, N} <- C],
    lists:any(
        fun({_, D, Args}) when F =:= D ->
                    passes_unknown_fun(Args, Exp);
           (_) -> false end,
        C).

%% @doc Check if the arguments passed to a recursive call in a HOF
%% HOF are not some permutation of the arguments expected as higher
%% order functions, e.g.
%% > a(F, G, A) -> G(F(A)),..., a(F, G, _). or a(G, F, _).
%% In such cases the self-recursive dependency should be preserved (and
%% make the function impure) since we cannot statically deduce its
%% purity or termination.
passes_unknown_fun(Args, Expecting) ->
    ESet = ordsets:from_list(Expecting),
    ASet = ordsets:from_list([N || {arg, {N, K}} <- Args,
                                   ordsets:is_element(K, ESet)]),
    ESet =/= ASet. %% Safe to compare ordsets directly.

%% @doc Check whether all calls have at least one common subset as
%% argument.
all_subsets(Args) ->
    case [ordsets:from_list([N || {sub, N} <- A]) || A <- Args] of
        [] -> false;
        [H|T] -> [] =/= lists:foldl(fun ordsets:intersection/2, H, T)
    end.

%% @doc Check whether there is no concrete call for recursive higher
%% order functions.
%% XXX What about checking for HOF first? Could it be an indirect HOF?
no_high_callsite(Args) ->
    not lists:any(fun concrete_arg/1, lists:flatten(Args)).

concrete_arg({_N, {_M,_F,_A}}) -> true;
concrete_arg(_) -> false.

is_hof(C) ->
    lists:any(fun arg_dep/1, C).

arg_dep({arg, _}) ->
    true;
arg_dep(_) ->
    false.

clear_sub(C) ->
    [clear_sub1(D) || D <- C].

clear_sub1({T,F,Args}) when is_list(Args) ->
    {T, F, [A || A <- Args, not sub(A)]};
clear_sub1(D) ->
    D.

sub({sub,_}) ->
    true;
sub(_) ->
    false.


%%% Propagation Helpers %%%

converge_pst(Fun, #pst{table = Tab} = St0) ->
    case Fun(St0) of
        #pst{table = Tab} ->
            Tab;
        St1 ->
            converge_pst(Fun, St1)
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
collect_concrete(F, false, {Pure, Impure}) ->
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
                 pure_val(dict:fetch(D, Tab1))],
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
                            table = update_false(Tab, Funs1, Deps, St#pst.rsns)}).

add_elements(Elements, Set) ->
    lists:foldl(fun sets:add_element/2, Set, Elements).

fetch_deps(Key, DepMap) ->
    case dict:find(Key, DepMap) of
        {ok, Deps} ->
            Deps;
        error ->
            []
    end.

update_false(Tab, Funs, Deps, Reasons) ->
    case Reasons of
        false ->
            update(Tab, Funs, false);
        true ->
            update(Tab, with_reasons(Deps))
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
    Tl = list_to_binary(string:join(Ds, ", ")),
    <<"call to impure ", Tl/binary>>.

fmt_dep({erl, {'receive',_}}) ->
    "'receive' expression";
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
            {false, <<"impure call to higher order function">>};
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

call_site_analysis1({_Type, _MFA, _Args} = Value, Table) ->
    case analyse_call(Value, Table) of
        failed ->
            Value;
        Result ->
            Result
    end;
call_site_analysis1(Value, _Table) ->
    Value.

%% @doc Return true/{false, Reason} or failed.
analyse_call({_Type, CallMFA, Args} = Val, Table) ->
    case dict:find(CallMFA, Table) of
        {ok, [_|_] = Ctx0} ->
            %% Remove the value being resolved from the context. This can
            %% happen in recursive HOFs which call themselves with concrete
            %% values (i.e. CallMFA =:= Caller).
            Ctx1 = ctx_rem(Val, Ctx0),
            case find_matching_args(Ctx1, Args) of
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
                            {false, bin("impure call to ~s", [fmt_mfa(CallMFA)])};
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

pick_only_concrete(Vals) ->
    lists:foldl(fun reduce/2, pure, Vals).

reduce({ok, Val}, Prev) ->
    case impure_val(Val) of
        true -> impure;
        false ->
            case pure_val(Val) andalso Prev =:= pure of
                true -> pure;
                false -> other
            end
    end;
reduce(error, _) -> other.

pure_val(true) -> true;
pure_val([]) -> true;
pure_val(_) -> false.

impure_val(false) -> true;
impure_val({false,_}) -> true;
impure_val(_) -> false.

find_matching_args(ArgDeps, DepArgs) ->
    case match_args(ArgDeps, DepArgs, [], []) of
        {[], _} ->
            none;
        {Matching, []} ->
            {all, Matching};
        {Matching, _Remaining} ->
            {some, Matching}
    end.

match_args([{arg,N}=Arg|T], Deps0, Matching, Remaining) ->
    case lists:keytake(N, 1, Deps0) of
        {value, {N, MFA}, Deps1} ->
            match_args(T, Deps1, [MFA|Matching], Remaining);
        false ->
            match_args(T, Deps0, Matching, [Arg|Remaining])
    end;
match_args([NonArg|T], Deps, Matching, Remaining) ->
    match_args(T, Deps, Matching, [NonArg|Remaining]);
match_args([], _Deps, Matching, Remaining) ->
    {lists:reverse(Matching), lists:reverse(Remaining)}.


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
    %% waiting up to this point in the propagation to build the map.
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

option(Name, Options) -> option(Name, Options, false).
option(Name, Options, Default) ->
    proplists:get_value(Name, Options, Default).

%% @doc Merge two dictionarys keeping values from the second one when
%% conflicts arise.
merge(D1, D2) ->
    dict:merge(fun(_K, _V1, V2) -> V2 end, D1, D2).

%% @doc Extract the first elements from a list of tuples.
unzip1(Items) ->
    unzipN(1, Items).

%% @doc Extract the Nth elements from a list of tuples.
unzipN(N, Items) ->
    [element(N, Tuple) || Tuple <- Items].

bin(Fmt, Args) ->
    list_to_binary(io_lib:format(Fmt, Args)).



%%% Simplified algorithm %%%

%% @doc State record for the new algorithm.
-record(s, {tab :: dict(),
            rev :: dict(),
            unk  = sets:new() :: set(),
            diff = dict:new() :: dict(),
            ws   = []         :: list(),
            cs   = sets:new() :: set()}).

%% Migration helpers:
%% Convert values from the previous algorithm to the ones needed by
%% the current one. Handle new values transparently, as will also
%% be used on new tables when loading from a PLT.

%% The new value is a 2-tuple: {Purity, Dependency List}
convert_value(true) ->
    {p, []};
convert_value([exceptions]) ->
    {e, []};
convert_value(false) ->
    {s, []};
convert_value({false, _}) ->
    {s, []};
convert_value([side_effects]) ->
    {s, []};
convert_value([non_determinism]) ->
    {d, []};
convert_value(C) when is_list(C) ->
    {p, C};
convert_value(undefined) ->
    % This is a bit of a hack: in order to mark it unhandled, add a
    % nonsensical dependency.
    {p, [undefined]};
convert_value({_P, D} = NewValue) when is_list(D) ->
    NewValue. % Preserve new type values.


%%% Pureness values have a well defined ordering: s > d > e > p
%% @doc Implement the ordering relation of purity values.
sup(e, p) -> e;
sup(d, p) -> d;
sup(d, e) -> d;
sup(s, _) -> s;
sup(A, A) -> A;
sup(A, B) -> sup(B, A).

sup(Values) when is_list(Values) ->
    lists:foldl(fun sup/2, p, Values).

-spec propagate_new(dict(), purity_utils:options()) -> dict().

propagate_new(Tab, _Opts) ->
    %% These functions work on previous types of values.
    %% Leave removal of self-recursive dependencies to the end of the
    %% preprocessing stage in order to exploit any information when
    %% unfolding HOFs.
    T1 = add_predefined(add_bifs(Tab)),
    T2 = dict_vmap(fun convert_value/1, T1),

    S0 = #s{tab = T2,
            rev = purity_utils:rev_deps(T1)},

    S1 = preprocess(S0),
    T3 = converge_contaminate(S1#s{ ws = initial_workset(S1#s.tab) }),
    S2 = postprocess(S1#s{tab = T3}),

    S2#s.tab.


%% @doc Update table with predefined values for certain expressions.
add_predefined(Tab) ->
    lists:foldl(fun({K, V}, D) -> dict:store(K, V, D) end, Tab, ?PREDEF).


%% @doc Build the initial working set, consisting of any values with empty
%% dependency lists.
initial_workset(Tab) ->
    % Guaranteed no duplicates, so ordsets:from_list == lists:sort.
    lists:sort(dict:fold(
            fun(F, {_P, []}, W) -> [F|W]; (_, _, W) -> W end,
            [], Tab)).


%%% Contamination: This is the core of the algorithm.
%%% Pureness values contaminate dependent functions, and functions
%%% whose dependency list has been completely %% resolved are added
%%% to the working set.

converge_contaminate(#s{tab = T} = S0) ->
    case resolve_independent_sccs(contaminate(S0)) of
        #s{tab = T} -> T;
        S1 -> converge_contaminate(S1)
    end.

contaminate(#s{ws = []} = S) ->
    S;
contaminate(#s{ws = W} = S) ->
    contaminate(lists:foldl(fun contaminate/2, S#s{ws = []}, W)).

contaminate(E, #s{} = S) ->
    Dependent = [F || F <- reverse_deplist(E, S), not visited(F, S)],
    set_visited(E, contaminate(E, Dependent, S)).

contaminate(_, [], S) ->
    S;
contaminate(E, [F|Fs], #s{tab = T} = S0) ->
    {Pe,_De} = lookup(E, T),
    {Pf, Df} = lookup(F, T),
    S1 =
      case { sup(Pe, Pf), remove_dep(E, Df) } of
        {P, D} when P =:= s orelse D =:= [] ->
            %% Fully-resolved function, strip dependency list.
            update_tab(F, P, [], extend_workset(F, S0));
        {P, D} ->
            update_tab(F, P, D, S0)
      end,
    contaminate(E, Fs, S1).


%%% State record helpers.

reverse_deplist(Function, #s{rev = R}) ->
    dict_fetch(Function, R, []).

visited(F, #s{cs = C}) ->
    sets:is_element(F, C).

set_visited(F, #s{cs = C} = S) ->
    S#s{cs = sets:add_element(F, C)}.

extend_workset(F, #s{ws = W} = S) ->
    S#s{ws = ordsets:add_element(F, W)}.

update_tab(Function, Purity, DepList, #s{tab = T} = S) ->
    S#s{tab = dict:store(Function, {Purity, DepList}, T)}.

lookup(Function, Table) ->
    dict:fetch(Function, Table).

lookup_purity(Function, Table) ->
    element(1, lookup(Function, Table)).

lookup_deplist(Function, Table) ->
    element(2, lookup(Function, Table)).


%%% Dependency List helpers.

%% Dependencies could be simplified in this stage,
%% for instance lacking type and argument lists.
%% However, these would need to be restored afterwards, for
%% any remaining dependencies, so that they remain a part of the PLT.
remove_dep(F, DepList) ->
    lists:filter(
        fun({_, D, _})    -> F =/= D;
           ({erl, _} = D) -> F =/= D;
           ({primop,_}=D) -> F =/= D;
           (_) -> true end,
       DepList).


%%% Analysis of mutually recursive functions.

%% FIXME: Naming of functions.
resolve_independent_sccs(#s{tab = T, ws = []} = S) ->
    ICCs = with_graph(build_call_graph(T), fun locate_iccs/1),
    S#s{tab = lists:foldl(fun set_mutual_purity/2, T, ICCs),
        ws = workset(lists:flatten(ICCs))}.


set_mutual_purity(Fs, T) ->
    P = sup([lookup_purity(F, T) || F <- Fs]),
    lists:foldl(fun(F, Tn) -> dict:store(F, {P, []}, Tn) end, T, Fs).


%% @doc Locate independent components in the call graph.
%%
%% Independent components are strongly connected components without
%% dependencies to other SCCs. Specifically, we are interested in the
%% subset of those components which form a cycle between them, i.e.
%% represent mutually recursive functions. These components will be any
%% vertices of the condensed graph with a loop. The relation they
%% satisfy is more accurately the following:
%%   `out_neighbours(V) == [V] and member(V, in_neighbours(V))'
%% Since we are only interested in condensed vertices with at least 2
%% elements, which can be pattern matched, the condition is then
%% simplified to `out_degree(V) == 1'.
locate_iccs(G) ->
    with_graph(digraph_utils:condensation(G), fun select_iccs/1).

select_iccs(G) ->
    [V || [_,_|_] = V <- digraph:vertices(G),
        1 =:= digraph:out_degree(G, V),
        assert_independence(G, V)].

-ifdef(NOASSERT).
assert_independence(_, _) -> true.
-else.
assert_independence(G, V) ->
    In = digraph:in_neighbours(G, V),
    Out = digraph:out_neighbours(G, V),
    [V] = Out,
    %% Only when length(In) > 1 will the algorithm progress
    %% afterwards. This could be exploited, but the gain is
    %% marginal, the current bottleneck is the first contamination.
    true = lists:member(V, In).
-endif.

build_call_graph(Table) ->
    dict:fold(fun build_call_graph/3, digraph:new(), Table).

build_call_graph(F, {_P, D}, G) when is_list(D) ->
    Deps = lists:usort([collect_dep(Dep) || Dep <- D]),
    digraph:add_vertex(G, F),
    lists:foreach(
        fun(Dep) ->
                digraph:add_vertex(G, Dep),
                digraph:add_edge(G, F, Dep) end,
        Deps),
    G.


%% @doc Collect functions, primops and expressions from dependencies.
%% Anything unresolvable like [free] variable dependencies is
%% represented by a dependency to `undefined'.
collect_dep({erl, _} = E) ->
    E;
collect_dep({Type, Fun, A}) when is_list(A) ->
    true = lists:member(Type, [local, remote, primop]),
    case Type == primop orelse purity_utils:is_mfa(Fun) of
        true ->
            Fun;
        false ->
            true = is_variable(Fun),
            undefined
    end;
collect_dep({free, _}) ->
    undefined;
collect_dep(undefined) ->
    undefined.

%% Call with variable module, function or both.
is_variable({{var, M}, {var, F}, A}) ->
    true = purity_utils:is_mfa({M,F,A});
is_variable({{var, M}, F, A}) ->
    true = purity_utils:is_mfa({M,F,A});
is_variable({M, {var, F}, A}) ->
    true = purity_utils:is_mfa({M,F,A});
%% Variable application.
is_variable(Var) when is_atom(Var) ->
    true.


%%% Pre-Processing step:

preprocess(#s{tab = T} = S) ->
    reset_visited(
        strip_arg_deps(
            unfold_hofs(
                S#s{ ws = initial_pre_workset(T) }))).

initial_pre_workset(Tab) ->
    dict:fold(fun collect_hofs/3, [], Tab).

collect_hofs(F, {_P, D}, W) ->
    case is_hof(D) of
        true -> [F|W];
        false -> W
    end.

unfold_hofs(#s{ws = []} = S) ->
    S;
unfold_hofs(#s{ws = [F|Fs]} = S0) ->
    Rs = reverse_deplist(F, S0),
    S1 = unfold_hofs_dep_loop(F, Rs, S0#s{ws = Fs}),
    unfold_hofs(S1).

unfold_hofs_dep_loop(_, [], S) ->
    S;
unfold_hofs_dep_loop(F, [R|Rs], #s{tab = T} = S0) ->
    Df = lookup_deplist(F, T),
    Dr = lookup_deplist(R, T),
    Sn =
      case concrete_calls(F, Df, Dr, T) of
        {{all, PassedFunctions}, _} ->
            extend_deplist_with_funs(R, PassedFunctions, S0);

        {{maybe_some, PassedFunctions}, RestOfDr} ->
            S1 = extend_deplist_with_funs(R, PassedFunctions, S0),

            {Which, IndirectPositions} = indirect_args(F, Df, RestOfDr),

            S2 = extend_deplist_with_args(R, IndirectPositions, S1),

            %% Distinguish visited nodes by deplist value as well, so that
            %% we can continue in case of self-recursion, as long as new
            %% indirect arguments are added.
            %NDL = lookup_deplist(R, S2#s.tab),
            NDL = IndirectPositions,
            case Which of
                all ->
                    case visited({F, R, NDL}, S0) of
                        true -> S2;
                        false -> set_visited({F, R, NDL}, extend_workset(R, S2))
                    end;
                maybe_some ->
                    set_unknown(R, S2)
            end
      end,
    unfold_hofs_dep_loop(F, Rs, Sn).


%%% PRE: Dependency list helpers.
extend_deplist_with_funs(Function, NewDeps, #s{tab = T} = S0) ->
    OldDeps = lookup_deplist(Function, T),
    Deps = deplist(OldDeps ++ [{remote,D,[]} || D <- NewDeps]),
    S1 = update_deplist(Function, Deps, S0),
    update_reverse_deps(Function, NewDeps, S1).

extend_deplist_with_args(Function, Args, #s{tab = T} = S) ->
    Deps = lookup_deplist(Function, T),
    update_deplist(Function, deplist(Deps ++ [{arg,A} || A <- Args]), S).

update_deplist(F, D, #s{tab = T} = S) ->
    P = lookup_purity(F, T),
    S#s{tab = dict:store(F, {P, D}, T)}.

update_reverse_deps(_, [], S) ->
    S;
update_reverse_deps(F, [D|Ds], #s{rev = R} = S) ->
    %% Only MFAs would be passed as concrete arguments to higher order
    %% functions.
    S1 =
      case purity_utils:is_mfa(D) of
        true ->
            Rs = dict_fetch(D, R, []),
            S#s{rev = dict:store(D, ordsets:add_element(F, Rs), R)};
        false ->
            {arg, _} = D,
            S
      end,
    update_reverse_deps(F, Ds, S1).

deplist(Deps) ->
    ordsets:from_list(Deps).


%%% PRE: State record helpers.

set_unknown(F, #s{unk = U} = S) ->
    S#s{unk = sets:add_element(F, U)}.

reset_visited(#s{} = S) ->
    S#s{cs = sets:new()}.


%%% PRE: HOF helpers.

concrete_calls(F, Df, Dr, T) ->
    Positions = ordsets:from_list([N || {arg, N} <- Df]),
    Candidates = [Args || {_, D, Args} <- Dr, D =:= F],
    Results = [find_calls(F, Positions, Args, T) || Args <- Candidates],
    ToPurge = ordsets:from_list(
        [Args || {{all, _}, Args} <- lists:zip(Results, Candidates)]),
    %% Remove any of the dependencies which pass concrete arguments.
    RestOfDr = lists:filter(
        fun ({_, D, Args}) ->
                not (D =:= F andalso ordsets:is_element(Args, ToPurge));
            (_) -> true end,
        Dr),
    {collect_results(Results), RestOfDr}.

find_calls(H, Positions, Args, T) ->
    Fs = [Fun || {N, Fun} <- Args,
          purity_utils:is_concrete_fun(Fun),
          ordsets:is_element(N, Positions)],
    %% Passing HOFs as a concrete argument does not count, although
    %% the HOF is added to the returned list, so that is pureness value
    %% is propagated to the caller. There is one exception however, when
    %% the concrete HOF passed is the same as the HOF it is passed to,
    %% e.g. for performing recursion with an anonymous function.
    Pred = fun(F) ->
            {_, D} = dict_fetch(F, T, {p, []}),
            H =/= F andalso is_hof(D) end,
    {_, NotHOFs} = lists:partition(Pred, Fs),
    case length(NotHOFs) == length(Positions) of
        true  -> {all, Fs};
        false -> {maybe_some, Fs}
    end.

indirect_args(F, Df, Dr) ->
    Positions = ordsets:from_list([N || {arg, N} <- Df]),
    collect_results(
        [find_indirect(Positions, Args) || {_, D, Args} <- Dr, D == F]).

find_indirect(Positions, Args) ->
    {Fs, Ts} = lists:unzip([FromTo || {arg, {_From, To} = FromTo} <- Args,
                            ordsets:is_element(To, Positions)]),
    case ordsets:from_list(Ts) of
        Positions -> {all, Fs};
        _ -> {maybe_some, Fs}
    end.


collect_results(Results) ->
    {Which, Values} = lists:foldl(fun collect_results/2, {all, []}, Results),
    {Which, lists:usort(Values)}.

collect_results({all, R1}, {all, R2}) ->
    {all, R1 ++ R2};
collect_results({_, R1}, {_, R2}) ->
    {maybe_some, R1 ++ R2}.


%% @doc Remove all HOFs from the table in order to keep contamination simple.
%% Certain HOFs will also have prevented some self-dependencies from being
%% removed, so get rid of those here too.
strip_arg_deps(#s{tab = T0} = S) ->
    {T1, Diff} = dict_mapfold(fun stripper/3, dict:new(), T0),
    S#s{tab = T1, diff = Diff}.

%% @doc Generate a new deplist with arguments and self-references stripped.
%% Keep track of stripped arguments in order to restore them later to
%% mark HOFs.
%%
%% It is important to remove self-dependencies here and not at the beginning
%% of propagation for 3 reasons:
%% - HOF unfolding may add self-dependencies passed as concrete arguments,
%%   so they will have to be removed again anyway.
%% - HOF unfolding is better at marking a function as unknown than keeping
%%   a mysterious self-rec as unresolved dependency. Furthermore, such
%%   dependencies can help indirect HOF analysis (see test/nested) and
%%   it is necessary for them to be all present for optimal results.
stripper(F, {P, D0}, Diff) ->
    Rs = [D || D <- D0, not is_rec(F, D)],
    D1 = [D || D <- Rs, not is_arg(D)],
    case ordsets:subtract(Rs, D1) of
        [] -> { {P, D1}, Diff };
        Df -> { {P, D1}, dict:store(F, Df, Diff) }
    end.

is_arg({arg, _}) ->
    true;
is_arg(_) ->
    false.

is_rec(F, {_, F, A}) when is_list(A) ->
    true;
is_rec(_, _) ->
    false.


restore_arg_deps(#s{tab = T0, diff = Diff} = S) ->
    T1 = dict:map(
        fun(_, {s, _}=V) -> V;
           (F, {P, D0}) ->
                {P, ordsets:union(D0, dict_fetch(F, Diff, []))} end,
        T0),
    S#s{tab = T1}.


%%% Post-Processing step:

postprocess(#s{unk = U} = S) ->
    restore_arg_deps(
        mark_at_least(
            propagate_unhandled(
                S#s{ ws = workset(sets:to_list(U)) }))).


%% @doc Create a set comprising of all the functions whose purity was
%% not conclusively determined.
%%
%% These consist of any functions which were marked as unknown during
%% the pre-processing stage and all those which depend on them, HOFs,
%% and functions which were left with non-empty dependency lists after
%% the contamination phase.
propagate_unhandled(#s{ws = []} = S) ->
    S;
propagate_unhandled(#s{ws = [F|Fs]} = S) ->
    Rs = [R || R <- reverse_deplist(F, S), not unknown(R, S)],
    propagate_unhandled(set_unknown(F, S#s{ws = workset(Rs ++ Fs)})).


% Decided not to mark these as unknown since they can be identified
% as {at_least, P} by their non-empty dependency list. This way it is
% possible to distinguish between truly unknown functions when for
% instance the purity of a function is re-evaluated because one of
% its missing dependencies has just been found.
%other_unknown(#s{tab = T, unk = U0} = S) ->
%    U1 = dict:fold(fun funs_with_non_empty_deplist/3, sets:new(), T),
%    U2 = sets:from_list(dict:fold(fun collect_hofs/3, [], T)),
%    S#s{unk = sets:union([U0, U1, U2])}.
%
%funs_with_non_empty_deplist(_, {_, []}, S) ->
%    S;
%funs_with_non_empty_deplist(F, {_, D}, S) when is_list(D) ->
%    sets:add_element(F, S).


%% @doc Change the purity of unknown functions from P to {at_least, P}.
mark_at_least(#s{tab = T, unk = U} = S) ->
    S#s{tab = sets:fold(fun mark_at_least/2, T, U)}.

mark_at_least(F, T) ->
    {P, D} = lookup(F, T),
    case P of
        s -> T; % s == at_least(s).
        _ -> dict:store(F, { {at_least, P}, D }, T)
    end.


%%% POST: State record helpers.

unknown(F, #s{unk = U}) ->
    sets:is_element(F, U).

workset(Functions) ->
    ordsets:from_list(Functions).


%%% Miscellaneous helpers.


-spec purity_of(any(), dict()) -> atom() | {at_least, atom()}.

purity_of(F, T) ->
    case dict:fetch(F, T) of
        %% Fully resolved functions.
        {P, []} -> P;
        %% Functions marked unknown.
        {{at_least, _} = P, _} -> P;
        %% Functions with non-empty dependency lists.
        {P, D} when is_atom(P), is_list(D) -> {at_least, P}
    end.

%% Dict helpers.

dict_vmap(Fun, D) ->
    dict:map(fun(_, V) -> Fun(V) end, D).

%% @doc Fetch a value from a dict or fallback to a default if missing.
dict_fetch(Key, Dict, Default) ->
    case dict:find(Key, Dict) of
        {ok, Value} -> Value;
        error -> Default
    end.

%% @doc Not as efficient as a native implementation would be,
%% but usefull all the same.
dict_mapfold(Fun, Acc0, Dict) ->
    dict:fold(
        fun(K, V1, {Map, Acc1}) ->
                {V2, Acc2} = Fun(K, V1, Acc1),
                {dict:store(K, V2, Map), Acc2} end,
        {dict:new(), Acc0}, Dict).


%% Digraph helpers.

%% @doc The digraph module uses ETS tables which are not garbage collected,
%% so digraphs have to be explicitly destroyed.
with_graph(Graph, Function) ->
    Result = Function(Graph),
    true = digraph:delete(Graph),
    Result.


%% Convert values to the true/false for comparison with the previous algorith.
-spec convert(dict(), purity_utils:options()) -> dict().
convert(Tab, Opts) ->
    Map = dict:from_list(
      case option(purelevel, Opts, 1) of
        1 -> [{p, true}, {e, true}, {d, true}, {s, false}];
        2 -> [{p, true}, {e, true}, {d, false}, {s, false}];
        3 -> [{p, true}, {e, false}, {d, false}, {s, false}]
      end),
    dict:map(
        fun(_, {{at_least,P}, []}) -> [P];
           (_, {{at_least,_P}, D}) -> D;
           (_, {P, []}) -> dict:fetch(P, Map);
           (_, {P, D}) -> [P|D] end,
        Tab).

