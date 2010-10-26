-module(expr).
-compile(export_all).

%< global [{test,with_reasons},with_reasons]

%< foo/0 {false,"call to impure 'receive' expression"}
%< [termination] foo/0 {false,"call to impure 'receive' expression"}
foo() ->
    receive
        Msg ->
            {ok, Msg}
    end.

%< bar/0 true
%< [{purelevel,2}] bar/0 {false,"call to impure 'catch' expression"}
bar() ->
    catch (baz()).

%< baz/0 true
baz() ->
    42.


%% Older versions of the code did not traverse after expressions.
%% This was masked by the impure dependency on receive anyway.
%< coverage/0 {false,"call to impure 'receive' expression, erlang:erase/1, erlang:put/2"}
%< [termination] coverage/0 {false,"call to impure 'receive' expression"}
coverage() ->
    receive
        Msg ->
            {ok, Msg}
    after erase(timer) ->
        put(timer, 42)
    end.

