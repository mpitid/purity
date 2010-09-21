-module(indirect).
-compile(export_all).

%%% Test indirect dependencies to higher order functions.
%%% These should work for any level of indirection, but are
%%% limited to functions with a single higher order dependency,
%%% both in the base case and in any indirect level.

%% This is the basic higher order function, easy to resolve.
% fold/3 [{arg,1}]
fold(_Fun, Acc, []) ->
    Acc;
fold(Fun, Acc, [H|T]) ->
    fold(Fun, Fun(H, Acc), T).

%% Its fairly simple to determine that the call-site purity of
%% fold/3 in this case is pure.
% f11/0 true
f11() ->
    fold(fun erlang:'*'/2, 0, [2, 3, 7]).

% f12/0 {false,"impure call to indirect:fold/3"}
f12() ->
    fold(fun erlang:put/2, computer, [ok, error]).

%% One level of indirection.
% fold_1/3 [{local,{indirect,fold,3},[]}]
fold_1(Fun, Acc, Lst) ->
    fold(Fun, Acc, Lst).

% f21/0 true
f21() ->
    fold_1(fun erlang:'*'/2, 0, [2, 3, 7]).

% f22/0 {false,"impure call to higher order function"}
f22() ->
    fold_1(fun erlang:put/2, computer, [ok, error]).

%% Two levels of indirection, plus change in the place of the
%% function argument.
% fold_2/3 [{local,{indirect,fold_1,3},[]}]
fold_2(Lst, Acc, Fun) ->
    fold_1(Fun, Acc, Lst).

% f31/0 true
f31() ->
    fold_2([2, 3, 7], 1, fun erlang:'*'/2).

% f32/0 {false,"impure call to higher order function"}
f32() ->
    fold_2([ok, error], computer, fun erlang:put/2).

% fold_3/1 [{local,{indirect,fold_2,3},[]}]
fold_3(Fun) ->
    fold_2([2, 3, 7], 1, Fun).

% f41/0 true
f41() ->
    fold_3(fun erlang:'*'/2).
% f42/0 {false,"impure call to higher order function"}
f42() ->
    fold_3(fun erlang:put/2).

%% Can't resolve this one because it has two higher order dependencies :(
% fold_3/2 [{local,{indirect,fold_1,3},[]},{local,{indirect,fold_2,3},[]}]
fold_3(Lst, Fun) ->
    fold_2(fold_1(Fun, 1, Lst), 1, Fun).

% f51/0 [{local,{indirect,fold_3,2},[{2,{erlang,'*',2}}]}]
f51() ->
    fold_3([2, 3, 7], fun erlang:'*'/2).

% f52/0 [{local,{indirect,fold_3,2},[{2,{erlang,put,2}}]}]
f52() ->
    fold_3([ok, error], fun erlang:put/2).

