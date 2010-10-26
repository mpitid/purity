
-module(args).
-compile(export_all).

%< f1/1 [{arg,1}]
f1(Arg) ->
    case Arg of
        [] ->
            Arg;
        N when is_integer(N) ->
            N;
        F when is_function(F) ->
            F(0)
    end.

% This is depends instead of pure, since we can't resolve the
% first two calls to f1, because they don't have a callable argument.
%< f2/0 [{local,{args,f1,1},[]}]
f2() ->
    f1([]),
    f1(2),
    f1(fun abs/1).
