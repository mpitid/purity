
-module(selfrec).
-compile(export_all).

%< fact/1 e
%< [termination] {false,"recursion"}
fact(0) -> 1;
fact(N) -> N * fact(N-1).
