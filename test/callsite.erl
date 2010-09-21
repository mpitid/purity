
-module(callsite).
-compile(export_all).

% Test for call-site dependencies.

% Complicated version.
%ambifun([F1|_T], A1) ->
%    F1(A1);
%ambifun(F1, A1) when not is_list(F1) ->
%    F1(A1).
%ambifun(F2, A1) when not is_list(F2) ->
%    F2(A1).

% Simple function which depends on the it's 1st argument.
% ambifun/2 [{arg,1}]
ambifun(F1, A1) ->
    F1(A1).

% Pass system function without side-effects.
% caller1/0 true
caller1() ->
    ambifun(fun erlang:abs/1, 2).

% Pass system function with side-effects.
% caller2/0 {false,"impure call to callsite:ambifun/2"}
caller2() ->
    ambifun(fun io:getline/1, 2).

% Pass generated function without side-effects.
% caller3/0 true
caller3() ->
    ambifun(fun(X) -> X end, 2).
