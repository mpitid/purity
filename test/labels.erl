
-module(labels).
-compile(export_all).

% l1/0 true
l1() -> fun(X) -> X rem 1 end.

