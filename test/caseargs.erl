
-module(caseargs).

-compile(export_all).

%< f1/2 e
f1(X, Y) ->
    case {X,Y} of
        {1,2} -> ok;
        {1,3} -> not_ok;
        {2,4} -> weird
    end.
