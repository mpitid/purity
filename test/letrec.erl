
-module(letrec).

-compile(export_all).

%< f1/2 true
f1(A1, A2) ->
    [f2(A) || A <- A1 ++ A2].

%< f2/1 true
f2(E) ->
    [f1(A,B) || {A,B} <- E].

% Nested letrec expressions.
%< f3/2 true
f3(X,Y) ->
    L1 = [{A,B} || A <- X, B <- Y],
    [A || A <- L1].

%% While this is a total function, if exceptions are considered impure
%% it will be impure, because both length and the generated letrec may
%% generate a match_fail.
%< f4/1 true
f4(L) when length(L) >= 0 ->
    [E || E <- L];
f4(_) -> error.

%% Function nested in letrec.
%f5(L) ->
%    [fun() -> [X || X <- E] end || E <- L].
