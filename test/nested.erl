-module(nested).
-compile(export_all).

%% global [{test,{filter,reasons}},{test,{filter,nested}}]
%< global [{test,{filter,nested}},{test,{filter,args}}]

%% Common pattern of nested functions: The list comprehension creates
%% a nested letrec expression, which will depend on itself and the free
%% variable Pred. The outer function however knows that Pred is its
%% argument, so we should be able to figure out it is a HOF.
%< a/2 e [1]
a(Pred, List) when is_function(Pred, 1), is_list(List) ->
    [Elem || Elem <- List, Pred(Elem)].

%% A variation of the above with an explicitly nested function.
%< b/2 p [1]
b(F, A) ->
    fun(E) -> F(E) end( A ).

%% Multiple levels of nesting
%< aaa/3 e [1,2]
aaa(P1, P2, L) ->
    [[[E || E <- N, P2(E)] || N <- M, P1(N)] || M <- L].

%% While fairly uncommon, HOFs with nested functions that map to
%% recursive calls can be handled to some extent. In this case, the
%% call to `c' in the `letrec' expression is mapped to a recursive
%% call in `c', while the free variable `F' passed as argument to the
%% call is successfully matched with the first argument of `c', making
%% it possible to ignore the recursive call altogether. Look at the
%% tests in `higher' for more on that.
%< c/2 e [1]
c(_, []) ->
    [];
c(F, [H|T]) when is_list(H) ->
    [c(F, E) || E <- H] ++ c(F, T);
c(F, E) ->
    F(E).

%% Same as before, but with a more complex case, where the two higher
%% order arguments are transposed. Again see `higher'.
%< d/3 e [1,2]
d(_, _, []) ->
    [];
d(F, G, [H|T]) when is_list(H) ->
    [d(G, F, E) || E <- H] ++ d(F, G, T);
d(F, G, E) ->
    F(G(E)).

%% In this case there is no explicit dependency on the second
%% argument and we previously could not safely remove the recursive
%% call. This is now possible with indirect HOF analysis, by marking
%% the e/3 functions as indirectly dependent on 2. See more elaborate
%% l/m examples later on.
%< e/3 e [1,2]
e(_, _, []) ->
    [];
e(F, G, [H|T]) when is_list(H) ->
    [e(G, F, E) || E <- H] ++ e(F, G, T);
e(F, _, E) ->
    F(E).

%< e1/0 e
e1() ->
    e(fun abs/1, fun abs/1, [[1,2]]).

%< e2/0 s
e2() ->
    e(fun abs/1, fun put/2, []).


%% In this example the free variable passed as argument cannot be
%% resolved to anything meaningful in the parent, so the nested
%% dependency is left as is.
%% f/3 [{arg,1},{local,{nested,'f_3-1',1},[]}]
%< f/3 >= e [1]
f(_, _, []) ->
    [];
f(F, G, [H|T]) when is_list(H) ->
    D = hd(H),
    [f(D, F, E) || E <- H] ++ f(F, G, T);
f(F, _, E) ->
    F(E).

%% Combination of nested function and indirect HOF:
%% g/2 is recognised as passing its first argument to the nested HOF,
%% and thus becomes an indirect HOF.
%% Improved g/2 [{local,{nested,'g_2-1',1},[]}]
%< g/2 p [1]
g(F, L) ->
    G = fun(H) -> H(L) end,
    G(F, L).

%< g1/0 e
g1() ->
    g(fun abs/1, -3).


%% This is an example of blocking the promotion of a dependency to
%% the parent function, by way of the presense of {arg,{_,_}} in the
%% dependency. Notice how {func,whatever,1} would be in the dep list if
%% it was promoted instead 'k_2-1' (i.e. G).
%< k/2 p [{local,{nested,'k_2-1',1},[]}]
k(A, B) ->
    G = fun(C) -> k(C, func:whatever(B)) end,
    G(A).


%% A few (contrived) examples which showcase the combination of nested
%% promotion with indirect analysis.

%% Make sure the analysis works for more than 1 indirect argument, where
%% each indirect argument is only discovered after the previous one has.

%% Note how not removing self-recs prior to indirect analysis is crucial
%% in this example, since otherwise the second call which retains F as its
%% first argument would have been removed, making the analysis impossible.
%< l/4 e [1,2,3]
l(F, G, X, [H|T]) when is_list(H) ->
    [{l(G, F, X, E), l(F, X, G, E)} || E <- H] ++ l(F, G, X, T);
l(F, _, _, E) ->
    F(E).

%< m/5 e [1,2,3,4]
m(F, G, X, Y, [H|T]) when is_list(H) ->
    [{m(G,F,X,Y,E), m(X,G,F,Y,E), m(Y,F,G,X,E)} || E <- H] ++ m(F, G, X, Y, T);
m(F, _, _, _, E) ->
    F(E).

%% This is an example of a function which does not get resolved
%% with the change in self-rec removal, although it previously was.
%% The reason is because not all recursive calls are resolved to
%% either concrete values, or indirect args. It should be possible
%% to combine detection of the two however.
%% For a real life example look at dets_utils:leafs_to_nodes/4.
%< n/2 >= e [1]
n(H, [V|_]) ->
    n(H, V);
n(H, V) ->
    n(fun abs/1, V),
    H(V).

