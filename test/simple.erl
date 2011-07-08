-module(simple).
-compile(export_all).

%< d0/0 p
d0() -> 0.

%< d1/0 e
d1() -> 1 + d0().

%< d2/0 e
d2() -> 1 + d1() + d0().

%< dnone/1 p
dnone(_) -> none.

%< myfun/0 e
myfun() ->
    {X, Y} = {3, 4},
    X + Y.
