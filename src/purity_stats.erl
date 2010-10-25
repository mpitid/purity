%% ====================================================================
%% This library is free software; you can redistribute it and/or
%% modify it under the terms of the GNU Lesser General Public
%% License as published by the Free Software Foundation; either
%% version 2.1 of the License, or (at your option) any later version.
%%
%% This library is distributed in the hope that it will be useful,
%% but WITHOUT ANY WARRANTY; without even the implied warranty of
%% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
%% Lesser General Public License for more details.
%%
%% You should have received a copy of the GNU Lesser General Public
%% License along with this library; if not, write to the Free Software
%% Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
%% 02110-1301 USA
%%
%% @copyright 2009-2010 Michael Pitidis, Kostis Sagonas
%% @author Michael Pitidis <mpitid@gmail.com>
%% @end
%% =====================================================================

%%%
%%% @doc Generate statistics from purity results of analysed modules.
%%%

-module(purity_stats).

-export([gather/2, write/2]).

-export_type([stats/0]).

-record(stats, {p = 0,   % Pure
                i = 0,   % Impure
                u = 0,   % Undefined
                l = 0}). % Limited by analysis

-type stats() :: #stats{}.
-type mod_stats() :: {module(), stats()}.

%% @doc Generate an assoc list of modules and their statistics.
-spec gather([module()], dict()) -> [mod_stats()].

gather(Modules, Table) ->
    Ms = sets:from_list(Modules),
    Vs = [Val || {{M,_,_}, _} = Val <- dict:to_list(Table),
        sets:is_element(M, Ms)],
    St0 = lists:foldl(fun update_stats/2, dict:new(), Vs),
    Inc = get_inconclusive(Ms, Table),
    St1 = dict:map(
        fun(M, #stats{u = U, l = L} = S) ->
                case dict:find(M, Inc) of
                    {ok, N} ->
                        S#stats{u = U + N, l = L - N};
                    error ->
                        S
                end end,
        St0),
    sort(dict:to_list(St1)).


%% @doc Write an assoc list of modules and statistics to file.
-spec write(file:filename(), [mod_stats()]) -> ok.

write(Filename, Stats) ->
    case file:open(Filename, [write]) of
        {ok, Io} ->
            io:format(Io, "# Pure\tImpure\tUndefined  Limited"
                          " %Pure  Module~n", []),
            lists:foreach(fun(S) -> print(Io, S) end, Stats),
            #stats{p = P, i = I, u = U, l = L} = St = sum(Stats),
            T = total(St),
            io:format(Io, "# Aggregate: pure ~.1f impure ~.1f undefined ~.1f "
                          "limit ~.1f modules ~b functions ~b",
                          [percent(P, T), percent(I, T), percent(U, T),
                              percent(L, T), length(Stats), T]),
            file:close(Io);
        {error, Reason} ->
            io:format("ERROR opening stats file ~p: ~p~n", [Filename, Reason])
    end.


update_stats({{M,_,_} = MFA, Val}, Dict) ->
    case purity_utils:internal_function(MFA) of
        true -> % Ignore internal functions.
            Dict;
        false ->
            F = fun(#stats{} = S) -> incr(Val, S) end,
            dict:update(M, F, incr(Val, #stats{}), Dict)
    end.

incr(true, #stats{p = Pure} = S) ->
    S#stats{p = Pure + 1};
incr({false, _}, #stats{i = Impure} = S) ->
    S#stats{i = Impure + 1};
incr(false, #stats{i = Impure} = S) ->
    S#stats{i = Impure + 1};
incr(undefined, #stats{u = U} = S) ->
    S#stats{u = U + 1};
incr(Ctx, #stats{u = U, l = L} = S) when is_list(Ctx) ->
    case lists:all(fun({arg,_}) -> true; (_) -> false end, Ctx) of
        true ->
            S#stats{u = U + 1};
        false ->
            S#stats{l = L + 1}
    end.

%% @doc Return a dict mapping each module to the number of inconclusive
%% functions it contains.
get_inconclusive(Modules, Table) ->
    RevDeps = purity_utils:rev_deps(Table),
    Funs = [F || {M,_,_} = F <- sets:to_list(get_undef(RevDeps, Table)),
        sets:is_element(M, Modules)],
    lists:foldl(
        fun({M,_,_}, D) -> dict:update_counter(M, 1, D) end, dict:new(), Funs).

%% @doc Return the set of functions with missing or undefined dependencies.
get_undef(Deps, Table) ->
    get_undef(Deps, get_undefined_or_missing(Table), sets:new()).

get_undef(_, [], Set) ->
    Set;
get_undef(Deps, Funs0, Set0) ->
    Funs1 = lists:usort(lists:flatten(
            [R || {ok, R} <- [dict:find(F, Deps) || F <- Funs0]])),
    Funs2 = [F || F <- Funs1, not sets:is_element(F, Set0)],
    Set1 = lists:foldl(fun sets:add_element/2, Set0, Funs2),
    get_undef(Deps, Funs2, Set1).

get_undefined_or_missing(Table) ->
    {Missing, _Prims} = purity:find_missing(Table),
    Undef = [Fun || {Fun, undefined} <- dict:to_list(Table)],
    Missing ++ Undef.


print(IoDev, {M, #stats{p = P, i = I, u = U, l = L} = S}) ->
    io:format(IoDev, "~7b ~7b ~7b ~7b ~8.1f  ~p~n", [P, I, U, L, percent(S), M]).

sum(Stats) ->
    lists:foldl(fun({_M, S}, T) -> sum(S, T) end, #stats{}, Stats).

sum(#stats{p = P1, i = I1, u = U1, l = L1},
    #stats{p = P2, i = I2, u = U2, l = L2} = Acc) ->
    Acc#stats{p = P1 + P2, i = I1 + I2, u = U1 + U2, l = L1 + L2}.


-spec sort([mod_stats()]) -> [mod_stats()].

sort(Stats) ->
    lists:sort(fun compare/2, Stats).

compare({_, S1}, {_, S2}) ->
    percent(S1) =< percent(S2).

percent(#stats{p = P} = S) ->
    percent(P, total(S)).

percent(_Value, Total) when Total == 0 ->
    0.0;
percent(Value, Total) ->
    (100 * Value) / Total.

total(#stats{p = P, i = I, u = U, l = L}) ->
    P + I + U + L.

