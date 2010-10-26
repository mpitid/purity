
-module(dest).

-compile([export_all]).

%% Termination analysis of functions which consume an argument.
%< global [termination,{test,{filter,reasons}}]

%% Traverse a list.
%< a/1 true
a([]) -> [];
a([H|T]) -> [H|a(T)].

%% A bit more useful, apply a function to each element of the list.
%< b/2 [{arg,1}]
b(F, []) when is_function(F,1) -> [];
b(F, [H|T]) -> [F(H)|b(F, T)].

%% Variation of the above with explicit case.
%< b1/2 [{arg,1}]
b1(F, L) ->
    case L of
        [H|T] = L -> [F(H)|b1(F, T)];
        [] -> [] end.

%% Make sure variables with the same name are correctly detected.
%< c/2 {false,"recursion"}
c([a|T], C) -> [a|c(T, C)];
c([H|C], T) -> [H|c(T, C)].

%% Don't really care that another argument gets augmentend,
%% or that we lack a base case.
%< d/3 true
d([_,H2|T], B, C) -> d(T, H2, [H2,B|C]);
d([H|T], B, C) -> d(T, B, [H|C]).

%% Not all cases reduce.
%< e/3 {false,"recursion"}
e([_|T], B, C) -> e(T, B, C);
e([], B, C) -> e(B, [], C).

%< e1/2 {false,"recursion"}
e1([H|T], B) -> e1([B|T], H).

%< e2/2 {false,"recursion"}
e2([_|T], B) -> e2(T, B);
e2([], B) -> e2([], B).

%< do_flatten/2 true
do_flatten([H|T], Tail) when is_list(H) ->
    do_flatten(H, do_flatten(T, Tail));
do_flatten([H|T], Tail) ->
    [H|do_flatten(T, Tail)];
do_flatten([], Tail) ->
    Tail.

%% Binaries work in a similar fashion.
%< b2l/1 true
b2l(<<H:8,T/binary>>) -> [H|b2l(T)];
b2l(<<>>) -> [].

%< l2b/1 true
l2b([H|T]) -> Tl = l2b(T), <<H:8,Tl/binary>>;
l2b([]) -> <<>>.

%< f/1 {false,"recursion"}
f(<<H:8,_S:8>>=_T) -> L = 2 * H, f(<<L>>).

%% FIXME: Detect aliases.
%< g/1 {false,"recursion"}
g(<<H:8,_/binary>>) ->
    case H of
        a -> ok;
        D -> g(D)
    end.

