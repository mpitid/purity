
-module(values).

-compile(export_all).

% This is actually false, since Y1 may be io:format,
% but no analysis is performed so as to determine the
% possible values of Y1 atm.
%% X1,Y1 are makred unknown since no aliases are found.
%% This is because they are bound by a let statement, while
%% aliases are only found for case clauses:
%% let X1, Y1 = case cor1, cor2 of ... end
%< f/2 [{local,'X1',[]},{local,'Y1',[]}]
f(X, Y) ->
    {X1, Y1} = case {X, Y} of
        {1,1} ->
            {1, 1};
        {2,2} -> 
            {fun()->2 end, fun()->3 end};
        {3,3} ->
            {fun erlang:abs/1, fun io:format/2};
        _ ->
            {2, 2}
    end,
    %X1, Y1. % true
    X1(), Y1(), X1().
