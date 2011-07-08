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

% FIXME:
% - Add separate predefined values for termination.
% - Characterise higher order function arguments as remote/local.

% TODO


-module(purity).

-define(utils, purity_utils).
-define(bifs, purity_bifs).
-define(plt, purity_plt).

-export([module/2]).
-export([module/3, modules/3]).
-export([pmodules/3, panalyse/2]).
-export([is_pure/2]).
-export([propagate/2,
         propagate_both/2,
         propagate_purity/2,
         propagate_termination/2,
         find_missing/1]).
-export([analyse_changed/3]).
-export([purity_of/2]).


-import(?utils, [dict_cons/3, dict_mapfold/3,
                 dict_store/2, dict_store/3, dict_fetch/3 ]).
-import(?utils, [str/2, filename_to_module/1 ]).

-export_type([pure/0]).

-ifdef(TEST).
-include("purity_tests.hrl").
-endif.

%% Besides built-in functions, a select few of Erlang expressions
%% may influence the purity and termination of functions.
-define(PREDEF_P, [
        {{erl,{'receive',finite}},    {s, []}},
        {{erl,{'receive',infinite}},  {s, []}},
        {{erl,'catch'},               {d, []}}]).

-define(PREDEF_T, [
        {{erl,{'receive',finite}},    {p, []}},
        {{erl,{'receive',infinite}},  {s, []}},
        {{erl,'catch'},               {p, []}}]).

%% Note that most exceptions are expressed in terms of the following
%% BIFs and primops which are hard-coded elsewhere:
%% {erlang,error,1}, {erlang,throw,1}, {erlang,exit,1}
%% {match_fail,1}, {raise,2}

-type purity()       :: purity_utils:purity().
-type options()      :: purity_utils:options().
-type deplist()      :: purity_utils:deplist().
%-type argument()     :: purity_utils:argument().
-type dependency()   :: purity_utils:dependency().
-type purity_level() :: purity_utils:purity_level().

-type plt() :: purity_plt:plt().

-type map_key() :: cerl:var_name().
-type map_val() :: mfa() | pos_integer().
-type map()     :: [{map_key(), map_val()}].

-type sub() :: {dict(), dict()}.

-type pure() :: {purity_utils:purity(), purity_utils:deplist()}.


%% @doc Simple purity test, only distinguishes between pure and impure.
%% Any function missing from the lookup table is also considered impure.
-spec is_pure(mfa(), dict()) -> boolean().

is_pure({_,_,_} = MFA, Table) ->
    case dict:find(MFA, Table) of
        {ok, {p, []}} ->
            true;
        _ ->
            false
    end.

%% @doc Analyse a module and return a lookup table of concrete results,
%% indexed by `{Module, Function, Arity}'.
%%
%% Analysis starts from parsed core erlang terms.
%%
%% @see is_pure/2
%% @see module/3
%% @see propagate/2
-spec module(cerl:c_module(), options()) -> dict().

module(Core, Options) ->
    Plt = load_plt_silent(Options),
    Tab = ?plt:table(Plt, Options),
    Dep = module(Core, Options, Tab),
    Res = propagate(Dep, Options),
    Res.

%% @doc Load a PLT from the provided options. If no PLT is found, or
%% there are errors, return a new PLT.
-spec load_plt_silent(options()) -> plt().
load_plt_silent(Opts) ->
    File = option(plt, Opts, ?plt:default_path()),
    Check = not option(no_check, Opts, false),
    case ?plt:load(File) of
        {error, _Type} ->
            ?plt:new();
        {ok, Plt} when Check ->
            case ?plt:verify(Plt) of
                ok -> Plt;
                _F -> ?plt:new()
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
                ctx     = ctx_new()  :: deplist(),
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

%% Populate the table with the purity of any BIF necessary.
add_bifs(Tab) ->
    lists:foldl(
        fun(F, T) -> dict:store(F, ?bifs:is_pure(F), T) end,
        Tab, collect_bif_dependencies(Tab)).


collect_function_deps(Tab) ->
    collect_dependencies(Tab, fun ?utils:is_mfa/1).
collect_primop_deps(Tab) ->
    collect_dependencies(Tab, fun ?utils:is_primop/1).

collect_bif_dependencies(Table) ->
    collect_dependencies(Table, fun is_bif/1).


collect_dependencies(Table, Filter) ->
    ?utils:uflatten(dict:fold(dep_collector(Filter), [], Table)).

dep_collector(Filter) ->
    fun (_, {_, DL}, Ds) -> [?utils:dependencies(DL, Filter, true)|Ds] end.

is_bif(Fun) ->
    (?utils:is_mfa(Fun) orelse ?utils:is_primop(Fun))
    andalso ?bifs:is_known(Fun).



%% @doc Remove any files with errors from the PLT, and re-analyse
%% changed files, as well as any dependencies thereof.

-spec analyse_changed({[file:filename()], [file:filename()]},
                      options(), plt()) -> plt().

analyse_changed({Changed, Errors}, Options, Plt) ->
    Combined = Changed ++ Errors,
    %% First strip the table of both changed and removed files, so that
    %% there are no left-over MFAs, e.g. when removing a function from a module.
    T1 = ?utils:delete_modules(?plt:info_table(Plt), to_modules(Combined)),
    %% Determine which modules should be re-analysed: Dependent -- Missing.
    DM = ?plt:dependent_modules(Plt, Combined) -- to_modules(Errors),
    %% We need the filenames of these modules. Since we cannot map a module to
    %% a specific filename, figure this out by the list of filenames stored in
    %% the PLT. It's a given that true == subset(DM, to_modules(Files)).
    Files = ?plt:filenames(Plt) -- Errors,
    Map = dict:from_list([{?utils:filename_to_module(F), F} || F <- Files]),
    DF = [dict:fetch(M, Map) || M <- DM],
    %% Collect information on these modules, and create a new PLT. Naturally
    %% any cached result tables are dismissed.
    ?plt:new(modules(DF, Options, T1), Files).

to_modules(Filenames) ->
    [?utils:filename_to_module(F) || F <- Filenames].


%% @doc Analyse a module and return a lookup table of functions
%% and dependencies, indexed by `{Module, Function, Arity}'.
%%
%% Analysis starts from parsed core erlang terms.
%%
%% @see modules/3

-spec module(cerl:c_module(), options(), dict()) -> dict().

module(Core, Options, Tab0) ->
    Module = cerl:concrete(cerl:module_name(Core)),
    Defs = [{cerl:var_name(Var), Fun} || {Var, Fun} <- cerl:module_defs(Core)],
    Names = lists:foldl(
        fun({{F,_},_}, Set) -> ordsets:add_element(atom_to_list(F), Set) end,
        ordsets:new(),
        Defs),
    St0 = state_new(Options, Names, ?utils:delete_modules(Tab0, [Module])),
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

-spec modules([string()], options(), dict()) -> dict().

modules(Modules, Options, Tab0) when is_list(Modules) ->
    lists:foldl(
        fun(File, TabN) ->
                case ?utils:get_core(File) of
                    {ok, Core} ->
                        module(Core, Options, TabN);
                    {error, Reason} ->
                        ?utils:emsg(Reason),
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

-spec pmodules([file:filename()], options(), dict()) -> dict().

pmodules(Modules, Options, Tab0) when is_list(Modules) ->
    CPUs = erlang:system_info(logical_processors),
    prune_merge(Tab0,
                lists:zip([filename_to_module(M) || M <- Modules],
                          ?utils:pmap({purity, panalyse},
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


-spec panalyse(file:filename(), options()) -> dict().

panalyse(Filename, Options) ->
    Tab = dict:new(),
    case ?utils:get_core(Filename) of
        {ok, Core} ->
            module(Core, Options, Tab);
        {error, Reason} ->
            ?utils:emsg(Reason),
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
%% (in the case of HOFs, but also with regard to termination analysis).
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
%-spec harvest_args(cerl:cerl(), state()) -> [argument()]. %% dialyzer chokes on cerl().
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

-spec ctx_add(dependency(), D) -> D when D :: deplist().
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

-spec propagate(dict(), options()) -> dict().

propagate(Tab, Opts) ->
    case option(both, Opts) of
        true ->
            propagate_both(Tab, Opts);
        false ->
            case option(termination, Opts) of
                true ->
                    propagate_termination(Tab, Opts);
                false ->
                    propagate_purity(Tab, Opts)
            end
    end.



is_hof(C) ->
    lists:any(fun arg_dep/1, C).

arg_dep({arg, _}) ->
    true;
arg_dep(_) ->
    false.


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



%%% Simplified algorithm %%%

%% @doc State record for the new algorithm.
-record(s, {tab :: dict(),
            rev :: dict(),
            unk  = sets:new() :: set(),
            diff = dict:new() :: dict(),
            ws   = []         :: list(),
            cs   = sets:new() :: set()}).


%% Convert a lookup table returned by the analysis to the one required
%% by the propagation stage by providing an initial purity for each
%% function. Since this stage can also be applied to mixed tables, when
%% a PLT has been loaded for instance, handle new values transparently.
initialise(Table) ->
    ?utils:dict_map(fun initial_purity/1, Table).

-spec initial_purity(deplist()) -> pure() ; (P) -> P when P :: pure().
%% Initialise info tables to pure.
initial_purity(DL) when is_list(DL) ->
    {p, DL};
%% Handle already processed tables transparently.
initial_purity({_P, DL} = V) when is_list(DL) ->
    V.


%%% Pureness values have a well defined ordering: s > d > e > p
%% @doc Implement the ordering relation of purity values.
-spec sup(purity_level(), purity_level()) -> purity_level().
sup(e, p) -> e;
sup(d, p) -> d;
sup(d, e) -> d;
sup(s, _) -> s;
sup(A, A) when is_atom(A) -> A;
sup(A, B) when is_atom(A), is_atom(B) -> sup(B, A).

-spec sup([purity_level()]) -> purity_level().
sup(Values) when is_list(Values) ->
    lists:foldl(fun sup/2, p, Values).

-spec propagate_purity(dict(), options()) -> dict().

propagate_purity(Tab, _Opts) ->
    %% These functions work on previous types of values.
    %% Leave removal of self-recursive dependencies to the end of the
    %% preprocessing stage in order to exploit any information when
    %% unfolding HOFs.
    T1 = add_predefined_purity(initialise(Tab)),

    S0 = #s{tab = T1, rev = ?utils:function_rmap(T1)},

    S1 = preprocess(S0),
    Fn = fun(S) -> resolve_independent_sccs(contaminate(S)) end,
    T2 = converge_contaminate(Fn, S1#s{ ws = initial_workset(S1#s.tab) }),
    S2 = postprocess(S1#s{tab = T2}),

    map_to_level(S2#s.tab, _Opts).


%% Update table with the values of any necessary BIFs as well
%% as Erlang expressions.
add_predefined_purity(Tab) ->
    dict_store(?PREDEF_P, add_bifs(Tab)).

add_predefined_termination(Tab) ->
    %% All BIFs are considered terminating.
    %% Except HOFs and any ones marked as unknown.
    BIFs = [{B, rectify(?bifs:is_pure(B))} || B <- collect_bif_dependencies(Tab)],
    dict_store(?PREDEF_T, dict_store(BIFs, Tab)).

%% This is based on the following assumptions about BIFs (and cheats):
%% - Values with a deplist are either HOFs or depend on some other BIF,
%%   so they should be preserved.
%% - Anything marked unknown is most likely unknown termination-wise as
%%   well, so that is preserved too. This is currently only used in
%%   erlang:apply/3, where there is insufficient information to determine
%%   the purity or termination of the function statically.
%% - Any other value should be marked terminating, as BIFs are guaranteed
%%   to terminate (in theory at least).
%%   XXX: It is still possible for a BIF or a cheat to wait indefinitely
%%   for some reason, e.g. port communication, waiting on a message, etc.
%%   There should be separate termination values for such BIFs. TODO

rectify({{at_least, _}, DL}) when is_list(DL) ->
    {{at_least, p}, DL};
rectify({_, DL}) when is_list(DL) ->
    {p, DL}.


%% @doc Build the initial working set, consisting of any values with empty
%% dependency lists.
initial_workset(Tab) ->
    % Guaranteed no duplicates, so ordsets:from_list == lists:sort.
    lists:sort(dict:fold(
            fun(F, {_P, []}, W) -> [F|W]; (_, _, W) -> W end,
            [], Tab)).


%%% Contamination: This is the core of the algorithm.
%%% Pureness values contaminate dependent functions, and functions
%%% whose dependency list has been completely resolved are added to
%%% the working set.

converge_contaminate(_, #s{ws = [], tab = T}) ->
    T;
converge_contaminate(Fun, #s{} = S) ->
    converge_contaminate(Fun, Fun(S)).


contaminate(#s{ws = []} = S) ->
    S;
contaminate(#s{ws = W} = S) ->
    Fs = lists:usort(lists:flatten(W)),
    contaminate(lists:foldl(fun contaminate/2, S#s{ws = []}, Fs)).

%% Note that reverse dependency lists still contain self references,
%% but the performance impact of analysing them as well is marginal.
%% If necessary they can easily be removed right after pre-processing.
contaminate(E, #s{tab = T} = S) ->
    Dependent = [F || F <- reverse_deplist(E, S), not visited(F, S)],
    set_visited(E, contaminate({E, lookup_purity(E, T)}, Dependent, S)).

contaminate(_, [], S) ->
    S;
contaminate({_, s}, Fs, #s{tab = T, ws = W} = S) ->
    S#s{tab = dict_store(Fs, {s, []}, T), ws = [Fs|W]};
contaminate({E, Pe} = EP, [F|Fs], #s{tab = T, ws = W} = S0) ->
    {Pf, Df} = lookup(F, T),
    S1 =
      case { sup(Pe, Pf), remove_dep(E, Df) } of
        {_, []} = P ->
            %% Fully-resolved function, add to workset.
            S0#s{tab = dict:store(F, P, T), ws = [F|W]};
        P ->
            S0#s{tab = dict:store(F, P, T)}
      end,
    contaminate(EP, Fs, S1).


%%% State record helpers.

reverse_deplist(Function, #s{rev = R}) ->
    dict_fetch(Function, R, []).

visited(F, #s{cs = C}) ->
    sets:is_element(F, C).

set_visited(F, #s{cs = C} = S) ->
    S#s{cs = sets:add_element(F, C)}.

extend_workset(F, #s{ws = W} = S) ->
    S#s{ws = ordsets:add_element(F, W)}.

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
    case Type == primop orelse ?utils:is_mfa(Fun) of
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
    true = ?utils:is_mfa({M,F,A});
is_variable({{var, M}, F, A}) ->
    true = ?utils:is_mfa({M,F,A});
is_variable({M, {var, F}, A}) ->
    true = ?utils:is_mfa({M,F,A});
%% Variable application.
is_variable(Var) when is_atom(Var) ->
    true.


%%% Pre-Processing step:

preprocess(#s{tab = T} = S) ->
    unmark_unknown(
      reset_visited(
        strip_arg_deps(
          unfold_hofs(
              S#s{ ws = initial_pre_workset(T) })))).

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
            %% indirect arguments are added. Add unknown values to the
            %% working set as well, as long as some positions are found.
            S3 =
              case IndirectPositions of
                [] -> S2;
                IP ->
                    Key = {F, R, IP},
                    case visited(Key, S0) of
                        true -> S2;
                        false -> set_visited(Key, extend_workset(R, S2))
                    end
              end,
            case Which of
                all -> S3;
                maybe_some -> set_unknown(R, S3)
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
      case ?utils:is_mfa(D) of
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

%% XXX:
%% Minor issue when starting the analysis from a pre-analysed table:
%% Since HOFs have already been unfolded, and concrete arguments moved
%% to the dependency list, in the case were the passed argument is the
%% HOF itself, and when that dependency remains because it could not be
%% resolved, there is now a new, unresolvable HOF dependency, which
%% causes the function to be marked as unknown. The termination
%% analysis of `mochiweb_request:read_chunks/1' is an example.
%% I can't see it affecting the analysis in any way, besides giving
%% different output between runs on the original table and cached
%% versions of the result in the PLT (i.e. p [deps...] and >= p [deps...]).
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
          ?utils:is_mfa(Fun),
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
        mark_unknown(
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
mark_unknown(#s{tab = T, unk = U} = S) ->
    S#s{tab = sets:fold(fun mark_unknown/2, T, U)}.

mark_unknown(F, T) ->
    {P, D} = lookup(F, T),
    case P of
        s -> T; % s == at_least(s).
        _ -> dict:store(F, { {at_least, P}, D }, T)
    end.


%% @doc Convert the purity of {at_least, P} functions to P and add them
%% to the unknown set. This step is necessary when working with previous
%% analysis results from a PLT.
unmark_unknown(#s{tab = T, unk = U} = S) ->
    {T1, U1} = dict_mapfold(fun unmark_unknown/3, U, T),
    S#s{tab = T1, unk = U1}.

unmark_unknown(F, {{at_least,P}, DL}, Unk) ->
    {{P, DL}, sets:add_element(F, Unk)};
unmark_unknown(_F, P, Unk) ->
    {P, Unk}.


%%% POST: State record helpers.

unknown(F, #s{unk = U}) ->
    sets:is_element(F, U).

workset(Functions) ->
    ordsets:from_list(Functions).


%%% Miscellaneous helpers.


-spec purity_of(term(), dict()) -> purity().

purity_of(F, T) ->
    case dict:fetch(F, T) of
        %% Fully resolved functions.
        {P, []} -> P;
        %% Functions marked unknown.
        {{at_least, _} = P, _} -> P;
        %% Functions with non-empty dependency lists.
        {P, D} when is_atom(P), is_list(D) -> {at_least, P}
    end.


%% Digraph helpers.

%% @doc The digraph module uses ETS tables which are not garbage collected,
%% so digraphs have to be explicitly destroyed.
with_graph(Graph, Function) ->
    Result = Function(Graph),
    true = digraph:delete(Graph),
    Result.


map_to_level(Tab, Opts) ->
    case option(purelevel, Opts, none) of
        1 -> convert(Tab, []);
        2 -> convert(Tab, [d]);
        3 -> convert(Tab, [e, d]);
        none -> Tab
    end.

convert(Tab, Values) ->
    ?utils:dict_map(fun (V) -> map_purity(V, Values) end, Tab).

map_purity({{at_least, P}, DL}, Values) ->
    case lists:member(P, Values) of
        true -> {s, []};
        false -> {{at_least, p}, DL}
    end;
map_purity({P, DL}, Values) ->
    case lists:member(P, Values) of
        true -> {s, []};
        false -> {p, DL}
    end.


%%% Termination analysis with the new algorithm. %%%
%% Re-use as much as possible from the purity propagation algorithm.
%% For instance, termination values are the subset {p, s} of purity
%% values, since there can be only two states, terminating (pure) or
%% non-terminating (equivalent to the maximal value of `side-effect').

-spec propagate_termination(dict(), options()) -> dict().

propagate_termination(Tab, _Opts) ->
    T1 = add_predefined_termination(initialise(Tab)),
    S0 = #s{tab = T1, rev = ?utils:function_rmap(T1)},

    S1 = preprocess_termination(S0),
    Fn = fun(S) -> mark_sccs(contaminate(S)) end,
    T2 = converge_contaminate(Fn, S1#s{ ws = initial_workset(S1#s.tab) }),
    S2 = postprocess(S1#s{tab = T2}),

    S2#s.tab.


%% @doc When it comes to termination analysis this step overlaps with
%% the contamination algorithm, and is not strictly necessary.
%% Furthermore, it can be used before contamination, as was the case
%% with the old termination analysis, to produce more starting values.
%% However, building the call graph for sufficiently large data sets
%% (e.g. the whole of OTP) is prohibitively slow. Instead, run it after
%% an initial contamination run, to mark values as definitely impure,
%% instead of unresolved which is how contamination leaves them.
mark_sccs(#s{tab = T, ws = []} = S) ->
    CSCs = with_graph(build_call_graph(T),
                     fun digraph_utils:cyclic_strong_components/1),
    W = workset(lists:flatten(CSCs)),
    S#s{tab = dict_store(W, {s, []}, T), ws = W}.


preprocess_termination(#s{tab = T} = S) ->
    unmark_unknown(
      reset_visited(
        strip_arg_deps(
          mark_recursive(
            unfold_hofs(
                S#s{ ws = initial_pre_workset(T) }))))).


%% @doc Mark any recursive functions as non-terminating, with the
%% exception of those recursive functions which pass "reduced" versions
%% of their arguments to all recursive calls. These calls are guaranteed
%% to either terminate or crash.
mark_recursive(#s{tab = T} = S) ->
    S#s{tab = dict:map(fun mark_recursive/2, T)}.

mark_recursive(F, {_, D} = V) ->
    case should_mark_recursive(F, D) of
        true  -> {s, []};
        false -> V
    end.

should_mark_recursive(F, D) ->
    %% The function should be marked if:
    As = [A || {_T, Fun, A} <- D, F =:= Fun],
    %% it has recursive dependencies
    [] =/= As andalso
    %% and it does not pass reduced arguments to all of them.
    [] =:= intersection([reduced_arguments(A) || A <- As]).

reduced_arguments(Args) ->
    %% No need to usort, args should already be an ordset.
    [N || {sub, N} <- Args].

%% @doc Return the intersection of a list of ordered sets.
intersection([]) ->
    [];
intersection([S|Sets]) ->
    lists:foldl(fun ordsets:intersection/2, S, Sets).



-spec propagate_both(dict(), options()) -> dict().
propagate_both(Tab, Opts) ->
    Tp = propagate_purity(Tab, Opts),
    Tt = propagate_termination(Tab, Opts),
    dict:merge(fun unite/3, Tp, Tt).

unite(_, {Pp, Dp}, {Pt, Dt}) ->
    case sup_at_least(Pp, Pt) of
        s -> {s, []};
        P -> {P, ordsets:union(Dp, Dt)}
    end.

sup_at_least({at_least, Pp}, {at_least, Pt}) ->
    {at_least, sup(Pp, Pt)};
sup_at_least({at_least, _}, s) ->
    s;
sup_at_least({at_least, Pp}, Pt) ->
    {at_least, sup(Pp, Pt)};
sup_at_least(Pp, Pt) when is_atom(Pp), is_atom(Pt) ->
    sup(Pp, Pt);
sup_at_least(Pp, Pt) when is_atom(Pp) ->
    sup_at_least(Pt, Pp).

