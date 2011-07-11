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
%% @copyright 2009-2011 Michael Pitidis, Kostis Sagonas
%% @author Michael Pitidis <mpitid@gmail.com>
%% @end
%% =====================================================================


%%%
%%% Traverse Core Erlang Abstract Syntax Trees and collect the necessary
%%% information for the analysis.
%%%

-module(purity_collect).

-define(utils, purity_utils).

-export([module/3, modules/3, pmodules/3]).

-export([panalyse/2]).

-import(?utils, [dict_cons/3, str/2]).


-type map_key() :: cerl:var_name().
-type map_val() :: mfa() | pos_integer().
-type map()     :: [{map_key(), map_val()}].

-type sub() :: {dict(), dict()}.

-type options()      :: purity_utils:options().
-type deplist()      :: purity_utils:deplist().
-type dependency()   :: purity_utils:dependency().


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
                lists:zip([?utils:filename_to_module(M) || M <- Modules],
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


%%% Various helpers. %%%

update(Table, KeyVals) ->
    lists:foldl(fun({K, V}, D) -> dict:store(K, V, D) end, Table, KeyVals).

update(Table, Funs, Value) ->
    update(Table, [{F, Value} || F <- Funs]).

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

