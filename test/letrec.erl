
-module(letrec).

-compile(export_all).

%< f1/2 e
f1(A1, A2) ->
    [f2(A) || A <- A1 ++ A2].

%< f2/1 e
f2(E) ->
    [f1(A,B) || {A,B} <- E].

% Nested letrec expressions.
%< f3/2 e
f3(X,Y) ->
    L1 = [{A,B} || A <- X, B <- Y],
    [A || A <- L1].

%% While this is a total function, it is still marked `e' because both
%% length/1 and the generated letrec function may raise match_fail.
%< f4/1 e
f4(L) when length(L) >= 0 ->
    [E || E <- L];
f4(_) -> error.

%% Function nested in letrec.
%f5(L) ->
%    [fun() -> [X || X <- E] end || E <- L].
