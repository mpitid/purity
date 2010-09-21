
-module(exceptions).
-compile(export_all).

%%-genex/1 {false,"call to impure primop match_fail:1, erlang:error/1, erlang:exit/1, erlang:throw/1"} --level 3
%% genex/1 true
genex(1) -> a;
genex(2) -> throw(a);
genex(3) -> exit(a);
genex(4) -> {'EXIT', a};
genex(5) -> erlang:error(a).

%%-catcher/1 {false,"call to impure exceptions:genex/1"} --level 3
%% catcher/1 true
catcher(N) ->
    try genex(N) of
        {ok, _Val} -> 3;
        Val -> {N, normal, Val}
    catch
        throw:X -> {N, caught, thrown, X};
        exit:X  -> {N, caught, exited, X};
        error:X -> {N, caught, error, X}
    end.

%%-demo1/0 {false,"call to impure exceptions:'demo1-1'/1"} --level 3
%% demo1/0 true
demo1() ->
    [catcher(I) || I <- [1,2,3,4,5]].

%% `catch' is not referentially transparent!
%%-demo2/0 {false,"call to impure exceptions:'demo2-1'/1"} --level 2
%% demo2/0 true
demo2() ->
    [{I, (catch genex(I))} || I <- [1,2,3,4,5]].

%% nogenex/1 true
nogenex(N) ->
    N.

%% `catch' is not referentially transparent!
%%-demo3/0 {false,"call to impure exceptions:'demo3-1'/1"} --level 2
%% demo3/0 true
demo3() ->
    [{I, (catch nogenex(I))} || I <- [1,2,3,4,5]].

%% demo4/0 true
demo4() ->
    [catcher2(I) || I <- [1,2,3,4,5]].

%% catcher2/1 true
catcher2(N) ->
    try nogenex(N) of
        {ok, _Val} -> 3;
        Val -> {N, normal, Val}
    catch
        throw:X -> {N, caught, thrown, X};
        exit:X  -> {N, caught, exited, X};
        error:X -> {N, caught, error, X}
    end.

%% Older versions of the code did not traverse the body of
%% the exception handler (the 'catch' part):
% coverage/1 {false,"call to impure erlang:put/2"}
coverage(N) ->
    try N + N of
        Sum ->
            Sum
    catch
        Cls:Err ->
            put(Cls, Err)
    end.

