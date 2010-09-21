-module(higher).
-compile(export_all).

%%% Higher order functions.

% d3/0 true
d3() -> apply(fun erlang:'+'/2, [1, 2]).
% d2/0 true
d2() -> d1(fun erlang:'+'/2, 1, 2).
% d1/3 [{arg,1}]
d1(Fun, N1, N2) -> Fun(N1, N2).

% apply(erlang, '+', [1,2]) gets optimized to 3.
%d4(N) -> apply(erlang, '+', [1, N]).

% f1/2 true
% f2/0 true
f1(N1, N2) -> N1 + N2.
f2() -> d1(fun f1/2, 1, 2).

% h1/0 true
h1() ->
    Fun = fun(_) -> 3 end,
    Sum = 3 + Fun(1),
    Sum.
