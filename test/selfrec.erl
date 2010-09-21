
-module(selfrec).
-compile(export_all).

% fact/1 true
fact(0) -> 1;
fact(N) -> N * fact(N-1).
