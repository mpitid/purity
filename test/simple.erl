-module(simple).
-compile(export_all).

%< d2/0 true
d2() -> 1 + d1() + d0().
%< d1/0 true
d1() -> 1 + d0().
%< d0/0 true
d0() -> 0.
%< dnone/1 true
dnone(_) -> none.

%< myfun/0 true
myfun() ->
    {X, Y} = {3, 4},
    X + Y.
