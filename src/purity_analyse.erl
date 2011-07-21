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
%%% Analyse collected information and resolve the purity or termination
%%% of each function.
%%%

-module(purity_analyse).


-define(plt, purity_plt).
-define(bifs, purity_bifs).
-define(utils, purity_utils).

-import(?utils, [dict_mapfold/3, dict_store/2, dict_store/3, dict_fetch/3]).


-export([analyse/3,
         propagate/2,
         propagate_both/2,
         propagate_purity/2,
         propagate_termination/2]).

-export([purity_of/2]).

-export_type([pure/0]).


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
%-type dependency()   :: purity_utils:dependency().
-type purity_level() :: purity_utils:purity_level().


-type pure() :: {purity_utils:purity(), purity_utils:deplist()}.


%% Populate the table with the purity of any BIF necessary.
add_bifs(Tab) ->
    lists:foldl(
        fun(F, T) -> dict:store(F, ?bifs:is_pure(F), T) end,
        Tab, bif_dependencies(Tab)).

bif_dependencies(Table) ->
    ?utils:dependencies(Table, fun ?utils:is_bif/1).


%% @doc Select the appropriate propagation function or both, depending
%% on the current set of options.
%%
%% @see propagate_purity/2
%% @see propagate_termination/2

-spec propagate(dict(), options()) -> dict().

propagate(Tab, Opts) ->
    case ?utils:option(both, Opts) of
        true ->
            propagate_both(Tab, Opts);
        false ->
            case ?utils:option(termination, Opts) of
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

propagate_purity(Tab, Opts) ->
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

    map_to_level(S2#s.tab, Opts).


%% Update table with the values of any necessary BIFs as well
%% as Erlang expressions.
add_predefined_purity(Tab) ->
    dict_store(?PREDEF_P, add_bifs(Tab)).

add_predefined_termination(Tab) ->
    %% All BIFs are considered terminating.
    %% Except HOFs and any ones marked as unknown.
    BIFs = [{B, rectify(?bifs:is_pure(B))} || B <- bif_dependencies(Tab)],
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
    case ?utils:option(purelevel, Opts, none) of
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


%% @doc Combine purity and termination analysis.
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


%% @doc Analyse the minimum set of required modules from the PLT.
%%
%% If the PLT is to be updated, analyse any functions in the result
%% table which are still unresolved, in case some of their dependencies
%% are now present. It is presumably less expensive to blindly add
%% these functions instead of checking exactly which ones have
%% dependencies on the newly analysed modules. TODO Verify
-spec analyse(dict(), purity_plt:plt(), options()) -> dict().

analyse(Tab, Plt, Opts) ->
    T =
      case ?plt:result_table(Plt, Opts) of
          error ->
              %% No cached results, analyse the whole PLT.
              replace_modules(?plt:info_table(Plt), Tab);
          {ok, Res} ->
              %% Remove any re-analysed modules first.
              R1 = ?utils:delete_modules(Res, all_modules(Tab)),
              R2 = add_dependencies(Tab, R1),
              case ?utils:option(add_to_plt, Opts) of
                  false -> R2;
                  true  -> add_unresolved(R2, R1)
              end
      end,
    propagate(T, Opts).


%% @doc Replace any modules present in Table 1 with the values of Table 2.
%% This is not a simple update operation, since we must also make sure
%% that any deleted functions are removed as well.
replace_modules(T1, T2) ->
    ?utils:dict_update(?utils:delete_modules(T1, all_modules(T2)), T2).

%% @doc Return a list of all the modules in a lookup table.
all_modules(Tab) ->
    lists:usort(dict:fold(
            fun ({M,_,_}, _, Ms) -> [M|Ms]; (_, _, Ms) -> Ms end, [], Tab)).


%% @doc Add any dependencies present in the PLT to the table.
add_dependencies(T, R) ->
    %% T and R are disjoint by now.
    Ds = ?utils:dependencies(T, fun (K) -> dict:is_key(K, R) end),
    ?utils:dict_store([{F, dict:fetch(F, R)} || F <- Ds], T).


add_unresolved(T1, T2) ->
    R1 = dict:filter(fun (_, {_, D}) -> D =/= [] end, T2),
    %% R1 is not enough, we must collect any concrete dependencies
    %% which are part of higher order calls and add them as well.
    R2 = collect_higher_deps(R1, T2),
    ?utils:dict_update(T1, R2).


collect_higher_deps(T1, T2) ->
    %% Only one pass is necessary, since *all* unresolved functions
    %% have been added to the table in the previous pass.
    dict:fold(
        fun (_, {_, DL}, T) ->
                Ds = ?utils:dependencies(DL, fun ?utils:is_mfa/1, true),
                Vs = [{F, dict:find(F, T2)} || F <- Ds],
                ?utils:dict_store([{F, V} || {F, {ok, V}} <- Vs], T) end,
        T1, T1).

