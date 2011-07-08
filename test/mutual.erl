-module(mutual).
-compile(export_all).

%< global [{test,with_reasons},with_reasons]

%%% Provide mutually recursive functions.

%< d0/0 p
d0() -> 0.

%< d1/0 e
d1() -> 1 + d2() + d0() + d3().

%< d2/0 e
d2() -> 1 + d1() + d0().

%< d3/0 e
d3() -> 1 + d2().

%< m1/1 s
%< m2/1 s
m1(Pid) -> m2(Pid).
m2(Pid) -> m1(Pid), Pid ! 0.

%< m3/1 e
%< m4/1 e
m3(N) -> abs(N) + m4(N).
m4(N) -> m3(N).

%% This is an example of mutually recursive functions which cannot be
%% resolved, showcasing why it is not enough to consider functions pure
%% if all of their dependencies are in the same call graph cycle.
%% While the first one is picked as a mutual candidate, it does not
%% make it through the reduction step, since f2/0 has other unresolved
%% dependencies too.

%% This example also showcases a modest limitation of the new algorithm,
%% the purity of f2 is not propagated to f1. This is not an actual issue,
%% just a limitation on result precision, which can be mitigated by a
%% post-processing step I suppose.

%< f1/0 p [{local,{mutual,f2,0},[]}]
f1() ->
    f2().

%< f2/0 e [{local,{mutual,f1,0},[]},{remote,{unknown,function,0},[]}]
f2() ->
    f1() + unknown:function().

