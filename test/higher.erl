-module(higher).
-compile(export_all).

%%% Test various aspects of higher order functions. %%%

%< global [{test,with_reasons},with_reasons]

%% Some simple preliminary cases, which should be easily resolvable
%% with call site analysis. The b/c functions should be equivalent.

%< a/3 p [1]
a(F, A1, A2) ->
    F(A1, A2).

%< b/0 e
%< [termination] b/0 p
b() ->
    a(fun erlang:'+'/2, 40, 2).

%< c/0 e
%< [termination] c/0 p
c() ->
    apply(fun erlang:'+'/2, [40, 2]).


%% Try a user defined function instead of a built-in.
%< d/2 e
%< [termination] d/2 p
d(X, Y) ->
    X + Y.

%< e/0 e
%< [termination] e/0 p
e() ->
    a(fun d/2, 40, 2).


%% Some edge cases of call site analysis:
%% Higher order recursive functions may potentially call themselves with
%% concrete arguments at some point. This creates two distinct problems:
%% Pure calls should be correctly detected and removed (requires extra
%% checks at call site), while impure ones should be propagated as usual.
%% Either way, this signifies the importance of tracking *recursive* calls,
%% since we could miss out on these impurities and incorrectly mark
%% certain functions as pure.

%% This is somewhat contrived, but for a real life example look at
%% `dets_utils:leafs_to_nodes/4'.
%< f/2 e [1]
%< [termination] f/2 s
f(_F, none) ->
    f(fun erlang:abs/1, 21);
f(F, N) when is_integer(N) ->
    F(N) * 2.

%< g/2 s
%< [termination] g/2 s
g(_F, none) ->
    g(fun erlang:put/2, 21);
g(F, Val) ->
    F(key, 2 * Val).

%< h/0 e
%< [termination] h/0 s
h() ->
    f(fun erlang:abs/1, 21).

%< i/0 s
i() ->
    g(fun d/2, 42).

%% Recursive HOFs present another challenge as it is possible that
%% the recursive call contains some unknown function. Usually however
%% this unknown function is the same one which characterised the function
%% as higher order (e.g. one of its arguments). We try to detect some
%% of these cases.
%< j/2 e [1]
%< [termination] j/2 p [1]
j(F, [H|T]) ->
    [F(H)|j(F, T)];
j(_, []) ->
    [].

%< k/3 e [1,2]
%< [termination] k/3 p [1,2]
k(F, G, [H|T]) ->
    [G(F(H))|k(F, G, T)];
k(_, _, []) ->
    [].

%% Variation of the previous example, with the higher order arguments
%% being transposed.
%< l/3 e [1,2]
%< [termination] l/3 p [1,2]
l(F, G, [H|T]) ->
    [G(F(H))|l(G, F, T)];
l(_, _, []) ->
    [].

%% Example of an unresolvable unknown function (an element of the list).
%< m/2 >= e [1]
%< [termination] m/2 >= p [1]
m(F, [G,E|T]) ->
    [F(E)|m(G, T)];
m(_, []) ->
    [].

