
-module(exceptions).
-compile(export_all).

%< global [{test,{filter,nested}},with_reasons]

%< genex/1 e
genex(1) -> a;
genex(2) -> throw(a);
genex(3) -> exit(a);
genex(4) -> {'EXIT', a};
genex(5) -> erlang:error(a).

%< catcher/1 e
catcher(N) ->
    try genex(N) of
        {ok, _Val} -> 3;
        Val -> {N, normal, Val}
    catch
        throw:X -> {N, caught, thrown, X};
        exit:X  -> {N, caught, exited, X};
        error:X -> {N, caught, error, X}
    end.

%< demo1/0 e
demo1() ->
    [catcher(I) || I <- [1,2,3,4,5]].

%% `catch' is not referentially transparent!
%< demo2/0 d
demo2() ->
    [{I, (catch genex(I))} || I <- [1,2,3,4,5]].

%< nogenex/1 p
nogenex(N) ->
    N.

%% `catch' is not referentially transparent!
%< demo3/0 d
demo3() ->
    [{I, (catch nogenex(I))} || I <- [1,2,3,4,5]].

%< demo4/0 e
demo4() ->
    [catcher2(I) || I <- [1,2,3,4,5]].

%< catcher2/1 e
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
%< coverage/1 s
coverage(N) ->
    try N + N of
        Sum ->
            Sum
    catch
        Cls:Err ->
            put(Cls, Err)
    end.

