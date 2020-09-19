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
%%% @doc Analysis of indirect higher order functions.
%%%

-module(purity_hofs).

-export([make_arg_graph/2, test_make_arg_graph/0]).
-export([higher_analysis/4, test_higher_analysis/0]).
-export([to_dot/2]).

%%%
%%% Build a digraph representing the flow of arguments towards
%%% higher order functions, then use it to perform call site analysis
%%% on such `indirecty' higher order functions.
%%%

-record(lst, {tab                   :: dict:dict(),
              rev                   :: dict:dict(),
              graph                 :: digraph(),
              closed = sets:new()   :: sets:set()}).


%% @doc Build a directed graph representing calls to higher order functions,
%% where an argument of the calling function is passed where a higher order
%% argument is expected. Vertices are MFAs while edges are labeled with the
%% a {From, To} tuple regarding the argument in question.
%% Limited to functions with a single function as argument at the moment.
-spec make_arg_graph(dict:dict(), dict:dict()) -> digraph().
make_arg_graph(Table, Reverse) ->
    Graph = digraph:new([acyclic]),
    %% The initial set of functions are those which directly
    %% depend on their arguments. These are leafs in the graph.
    Funs = dict:fold(fun extract_seed/3, [], Table),
    graph_loop(Funs, #lst{tab = Table, rev = Reverse, graph = Graph}).


%% This is the first point we would have to change in order to add
%% support for functions with multiple higher order arguments. XXX
extract_seed({_,_,_} = Fun, [{arg, _} = Arg], Acc) ->
    [{Fun, Arg}|Acc];
extract_seed(_NonMFA, _orOther, Acc) ->
    Acc.

%% For a given set of functions, find the directly dependent ones,
%% which also pass _their_ argument to them. These become the set
%% of functions for the next iteration. The closed set is used to
%% avoid endless loops in case of recursive dependencies.
graph_loop([], #lst{graph = G}) ->
    G;
graph_loop(Funs, #lst{closed = CS} = L) ->
    Next0 = lists:flatten([add_edges(F, A, L) || {F, A} <- Funs]),
    Next1 = lists:usort([Val || {_, _} = Val <- Next0,
            not sets:is_element(Val, CS)]),
    graph_loop(Next1, L#lst{closed = update_with(Next1, CS)}).

update_with(Elements, Set) ->
    lists:foldl(fun sets:add_element/2, Set, Elements).

%% This is the second point. It would have to be a loop over a list
%% of Args. XXX
add_edges({_,_,_} = Fun, {arg, _} = Arg, #lst{rev = Reverse} = L) ->
    case dict:find(Fun, Reverse) of
        {ok, Deps} ->
            lists:foldl(
                fun(Dep, Next) -> add_edge(Fun, Dep, Arg, Next, L) end, [], Deps);
        error ->
            []
    end.
%% XXX: nonMFA?

%% @doc If the dependent fun passes one of its arguments K to one of the
%% `slots' N in Fun, add an {K,N} labeled edge from Dep to Fun. Return
%% the list of {Dep,K} pairs which represent new functions with `slots',
%% used as the next seed.
add_edge({_,_,_} = Fun, {_,_,_} = Dep, {arg, _N} = Arg,
    Next, #lst{graph = G, tab = Table}) ->
    case dict:fetch(Dep, Table) of
        [_|_] = Ctx ->
            case has_arg(Arg, ctx_get_args(Ctx, Fun)) of
                error -> %% Does not pass argument, move on.
                    Next;
                {ok, {arg, {From, _To} = FromTo}} ->
                    digraph:add_vertex(G, Fun),
                    digraph:add_vertex(G, Dep),
                    digraph:add_edge(G, Dep, Fun, FromTo),
                    %% FIXME: How should cycles in the graph be handled?
                    %% Should they be checked for here? We could also
                    %% force the graph to be acyclic and have it crash.
                    [{Dep, {arg, From}}|Next]
            end;
        _Otherwise -> %% Does not pass argument or pure/impure, move on.
            Next
    end;
add_edge({_,_,_}, _nonMFADep, _Arg, Next, _L) ->
    io:format("XXX: Not sure this should happen (nonMFADep: ~p, ~p)~n", [_nonMFADep, _Arg]),
    Next.

has_arg({arg, {_,_}} = A, Args) ->
    find(fun(E) -> E =:= A end, Args);
has_arg({arg, N}, Args) when is_integer(N) ->
    %% The second clause in the predicate is for {N, MFA} args.
    find(fun({arg,{_,N2}}) -> N =:= N2; (_) -> false end, Args).


%% @doc Return {ok,Elem} for the first element of the list to match Pred,
%% or the atom error if none does.
find(Pred, []) when is_function(Pred, 1) ->
    error;
find(Pred, [H|T]) ->
    case Pred(H) of
        true ->
            {ok, H};
        false ->
            find(Pred, T)
    end.

ctx_get_args(Ctx, {_,_,_} = Fun) when is_list(Ctx) ->
    lists:foldl(
        fun({_Type, Dep, Args}, Acc) when Dep =:= Fun -> Args ++ Acc;
           (_Other, Acc) -> Acc end,
        [], Ctx).

%% This should produce the following graph:
%%   F2 --1--> F1
%% Which can be used to resolve the purity of F3 to pure.
-spec test_make_arg_graph() -> {dict:dict(), digraph()}.
test_make_arg_graph() ->
    F1 = {m,f1,3},
    F2 = {m,f2,3},
    F3 = {m,f3,2},
    F4 = {m,p,1},
    Deps = [{ F1, [{arg,1}] },
            { F2, [{local, F1, [{arg,{1,1}}]}] },
            { F3, [{local, F2, [{1,F4}]}] },
            { F4, true }],
    Tab = dict:from_list(Deps),
    Gra = make_arg_graph(Tab, purity_utils:rev_deps(Tab)),
    {Tab, Gra}.


%%% === Analysis === %%%

-type resolution() :: {resolved, pure | impure} | unresolved.
-spec higher_analysis(mfa(), term(), dict:dict(), digraph()) -> resolution().

higher_analysis(_Fun, [{_Type, {_,_,_} = Dep, [{N, {_,_,_} = Arg}]}], Table, G) ->
    case dict:find(Dep, Table) of
        %% XXX: While it appears that values like {false, _} should have been
        %% dealt with at this point, this is not the case, and it is actually
        %% pretty weird that call site analysis does not crash because of this.
        %% It is entirely possible that Dep has just become false from the previous
        %% pass, and its value has not been propagated yet (since call site did not
        %% crash this means _that_ was the pass that caused it).
        %% Example: reltool_fgraph,step,3 [{reltool_fgraph,map,2}]
        %% Note how this is an impure higher order function.
        {ok, undefined} ->
            unresolved;
        {ok, {false, _Rsn}} ->
            {resolved, impure};
        {ok, false} ->
            {resolved, impure};
        {ok, Ctx} when is_list(Ctx) ->
            higher_callsite(Dep, N, Arg, Table, G);
        error ->
            unresolved
    end;
higher_analysis(_Fun, _Val, _T, _G) ->
    unresolved.

%% @doc Traverse the vertices of the graph until a higher order function
%% is reached and then try to resolve the call.
higher_callsite({_,_,_} = Dep, N, {_,_,_} = Arg, Tab, G) ->
    case tractable(Dep, Tab) of
        false ->
            unresolved;
        true ->
            case is_leaf(Dep, G) of
                true ->
                    try_to_resolve(Arg, Tab);
                false ->
                    case has_edge(Dep, N, G) of
                        {true, {Next, N2}} ->
                            higher_callsite(Next, N2, Arg, Tab, G);
                        false ->
                            unresolved
                    end
            end
    end.

tractable({_,_,_} = Fun, Table) ->
    %% Functions with any other value should not have propagated
    %% up to this point.
    case dict:fetch(Fun, Table) of
        [_] -> % Assume this is the context of the next dep.
            true;
        Ctx when is_list(Ctx) ->
            false
    end.

try_to_resolve({_,_,_} = Fun, Table) ->
    case dict:find(Fun, Table) of
        {ok, true} ->
            {resolved, pure};
        {ok, {false, _Rsn}} ->
            {resolved, impure};
        {ok, false} ->
            {resolved, impure};
        _AnythingElse ->
            unresolved
    end.

is_leaf(Fun, G) ->
    case digraph:vertex(G, Fun) of
        {Fun, []} ->
            0 =:= digraph:out_degree(G, Fun);
        false ->
            false
    end.

%% Check if Fun has an edge from the specified slot, and return
%% the incident vertex along with the slot it fits in.
has_edge({_,_,_} = Fun, Label, G) ->
    case digraph:vertex(G, Fun) of
        {Fun, []} ->
            Edges = [digraph:edge(G, E) || E <- digraph:out_edges(G, Fun)],
            %% The digraph implementation supports multiple edges with the same
            %% vertices and labels, hence the need for usort.
            Picks = [{Next, To} || {_E, _Fun, Next, {From, To}} <- Edges,
                From =:= Label],
            case lists:usort(Picks) of
                [] ->
                    false;
                %% TODO: When/if multiple indirect dependencies to HOFs are
                %% supported, there could be more here.
                [NextTo] ->
                    {true, NextTo}
            end;
        false ->
            false
    end.


-spec test_higher_analysis() -> ok.

test_higher_analysis() ->
    {T, G} = test_make_arg_graph(),
    F = {m,f3,2},
    {resolved, pure} = higher_analysis(F, dict:fetch(F, T), T, G),
    ok.


%% @doc Write a representation of the specified graph in the
%% dot language, suitable for processing with graphviz.
-spec to_dot(digraph(), file:filename()) -> ok.

to_dot(Graph, Filename) ->
    hipe_dot:translate_digraph(Graph, Filename, "ArgGraph",
        fun purity_utils:fmt_mfa/1, edge_labels(Graph)).

%% The dot generation functions needs explicit options for
%% labeling the edges.
edge_labels(G) ->
    [{V1, V2, {label, purity_utils:str("~b-~b", [N1,N2])}} ||
        {_E, V1, V2, {N1,N2}} <- [digraph:edge(G, E) || E <- digraph:edges(G)]].

