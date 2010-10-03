-module(nested).
-compile(export_all).

%% Common pattern of nested functions: The list comprehension creates
%% a nested letrec expression, which will depend on itself and the free
%% variable Pred. The outer function however knows that Pred is its
%% argument, so we should be able to figure out it is a HOF.
% a/2 [{arg,1}]
a(Pred, List) when is_function(Pred, 1), is_list(List) ->
    [Elem || Elem <- List, Pred(Elem)].

%% A variation of the above with an explicitly nested function.
% b/2 [{arg,1}]
b(F, A) ->
    fun(E) -> F(E) end( A ).

%% Multiple levels of nesting
% aaa/3 [{arg,1},{arg,2}]
aaa(P1, P2, L) ->
    [[[E || E <- N, P2(E)] || N <- M, P1(N)] || M <- L].

%% While fairly uncommon, HOFs with nested functions that map to
%% recursive calls can be handled to some extent. In this case, the
%% call to `c' in the `letrec' expression is mapped to a recursive
%% call in `c', while the free variable `F' passed as argument to the
%% call is successfully matched with the first argument of `c', making
%% it possible to ignore the recursive call altogether. Look at the
%% tests in `higher' for more on that.
% c/2 [{arg,1}]
c(_, []) ->
    [];
c(F, [H|T]) when is_list(H) ->
    [c(F, E) || E <- H] ++ c(F, T);
c(F, E) ->
    F(E).

%% Same as before, but with a more complex case, where the two higher
%% order arguments are transposed. Again see `higher'.
% d/3 [{arg,1},{arg,2}]
d(_, _, []) ->
    [];
d(F, G, [H|T]) when is_list(H) ->
    [d(G, F, E) || E <- H] ++ d(F, G, T);
d(F, G, E) ->
    F(G(E)).

%% In this case there is no explicit dependency on the second
%% argument and we cannot safely remove the recursive call.
%% Note: I suppose type analysis would deduce out that G has to
%% be a function as well.
% e/3 [{arg,1},{local,{nested,e,3},[]}]
e(_, _, []) ->
    [];
e(F, G, [H|T]) when is_list(H) ->
    [e(G, F, E) || E <- H] ++ e(F, G, T);
e(F, _, E) ->
    F(E).

%% In this example the free variable passed as argument cannot be
%% resolved to anything meaningful in the parent, so the nested
%% dependency is left as is.
% f/3 [{arg,1},{local,{nested,'f_3-1',1},[]}]
f(_, _, []) ->
    [];
f(F, G, [H|T]) when is_list(H) ->
    D = hd(H),
    [f(D, F, E) || E <- H] ++ f(F, G, T);
f(F, _, E) ->
    F(E).

%% Same thing as the previous example, but for a different reason:
%% the nested function is a HOF.
% g/2 [{local,{nested,'g_2-1',1},[]}]
g(F, L) ->
    G = fun(H) -> H(L) end,
    G(F, L).

