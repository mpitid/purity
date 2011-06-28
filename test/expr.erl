-module(expr).
-compile(export_all).

%< global [{test,with_reasons},with_reasons]

%< foo/0 s
%< [termination] foo/0 {false,"call to impure 'receive' expression"}
foo() ->
    receive
        Msg ->
            {ok, Msg}
    end.

%< bar/0 d
bar() ->
    catch (baz()).

%< baz/0 p
baz() ->
    42.


%% Older versions of the code did not traverse after expressions.
%% This was masked by the impure dependency on receive anyway.
%< coverage/0 s
%< [termination] coverage/0 {false,"call to impure 'receive' expression"}
coverage() ->
    receive
        Msg ->
            {ok, Msg}
    after erase(timer) ->
        put(timer, 42)
    end.

