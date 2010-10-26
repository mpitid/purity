-module(mutual).
-compile(export_all).

%< global [{test,with_reasons},with_reasons]

%%% Provide mutually recursive functions.

%< d2/0 true
d2() -> 1 + d1() + d0().
%< d1/0 true
d1() -> 1 + d2() + d0() + d3().
%< d3/0 true
d3() -> 1 + d2().
%< d0/0 true
d0() -> 0.

%< m1/1 {false,"call to impure mutual:m2/1"}
%< m2/1 {false,"call to impure erlang:'!'/2, mutual:m1/1"}
m1(Pid) -> m2(Pid).
m2(Pid) -> m1(Pid), Pid ! 0.

%< m3/1 true
%< m4/1 true
m3(N) -> abs(N) + m4(N).
m4(N) -> m3(N).

%% This is an example of mutually recursive functions which cannot be
%% resolved, showcasing why it is not enough to consider functions pure
%% if all of their dependencies are in the same call graph cycle.
%% While the first one is picked as a mutual candidate, it does not
%% make it through the reduction step, since f2/0 has other unresolved
%% dependencies too.

%< f1/0 [{local,{mutual,f2,0},[]}]
f1() ->
    f2().

%< f2/0 [{local,{mutual,f1,0},[]},{remote,{unknown,function,0},[]}]
f2() ->
    f1() + unknown:function().

