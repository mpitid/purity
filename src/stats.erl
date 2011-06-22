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

-module(stats).

-export([gather/2, write/2]).

-export_type([stats/0]).

-record(stats, {p = 0, e = 0, d = 0, s = 0,
                h = 0,
                l = 0,
                u = 0}).

-define(FIELDS, [#stats.p, #stats.e, #stats.d, #stats.s,
                 #stats.h, #stats.l, #stats.u]).

-define(HEADERS, ["pure", "exceptions", "depedent", "effects",
                  "hofs", "limited", "undefined"]).

-define(FLEN, "~10").

-type stats() :: #stats{}.
-type mod_stats() :: {module(), stats()}.

%% @doc Generate an assoc list of modules and their statistics.
-spec gather([module()], dict()) -> [mod_stats()].

gather(Modules, Table) ->
    Ms = sets:from_list(Modules),
    Vs = [Val || {{M,_,_}, _} = Val <- dict:to_list(Table),
        sets:is_element(M, Ms)],
    sort(dict:to_list(
            lists:foldl(fun update_stats/2, dict:new(), Vs) )).


%% @doc Write an assoc list of modules and statistics to file.
-spec write(file:filename(), [mod_stats()]) -> ok.

write(Filename, Stats) ->
    case file:open(Filename, [write]) of
        {ok, Io} ->
            write_stats(Io, Stats),
            file:close(Io);
        {error, Reason} ->
            io:format("ERROR opening stats file ~p: ~p~n", [Filename, Reason])
    end.

write_stats(Io, Stats) ->
    io:format(Io, join(" ", [?FLEN++"s" || _ <- ?HEADERS]) ++ "~n", ?HEADERS),
    lists:foreach(fun(S) -> format(Io, S) end, Stats),
    {_Ms, Ss} = lists:unzip(Stats),
    Sum = sum(Ss),
    Fmt = join(" ", [purity_utils:str("~s ~~.1f", [H]) || H <- ?HEADERS]),
    Vals = [percent(F, Sum) || F <- ?FIELDS],
    io:format(Io,
              "# Aggregate: " ++ Fmt ++ " modules ~b functions ~b~n",
              Vals ++ [length(Stats), total(Sum)]).

format(IoDev, {M, #stats{} = S}) ->
    Fmt = join(" ", [?FLEN++"b" || _ <- ?FIELDS]),
    Vals = [element(F, S) || F <- ?FIELDS],
    io:format(IoDev, Fmt ++ " ~5.1f ~p~n", Vals ++ [percent(S), M]).

sum(StatList) ->
    lists:foldl(fun add_stats/2, #stats{}, StatList).

add_stats(#stats{}=S1, #stats{}=S2) ->
    lists:foldl(
        fun(Field, S) ->
                setelement(Field, S, element(Field, S1) + element(Field, S2)) end,
        #stats{}, ?FIELDS).


update_stats({{M,_,_} = MFA, Val}, Dict) ->
    case purity_utils:internal_function(MFA) of
        true -> % Ignore internal functions.
            Dict;
        false ->
            F = fun(#stats{} = S) -> match(Val, S) end,
            I = match(Val, #stats{}),
            dict:update(M, F, I, Dict)
    end.


match({{at_least, _}, []}, S) ->
    incr(#stats.l, S);

match({P, []}, S) ->
    match_aux(P, S);

match({_, D}, S) ->
    case is_hof(D) of
        true ->
            incr(#stats.h, S);
        false ->
            incr(#stats.u, S)
    end.

match_aux(p, S) -> incr(#stats.p, S);
match_aux(e, S) -> incr(#stats.e, S);
match_aux(d, S) -> incr(#stats.d, S);
match_aux(s, S) -> incr(#stats.s, S).

incr(Field, #stats{} = S) ->
    setelement(Field, S, 1 + element(Field, S)).

is_hof(D) ->
    [] =/= [A || {arg,A} <- D].


-spec sort([mod_stats()]) -> [mod_stats()].

sort(Stats) ->
    lists:sort(fun compare/2, Stats).

compare({_, S1}, {_, S2}) ->
    percent(S1) =< percent(S2).

percent(#stats{} = S) ->
    percent(#stats.p, S).

percent(Field, S) ->
    case total(S) of
        0 -> 0.0;
        T -> (100 * element(Field, S)) / T
    end.

total(#stats{} = S) ->
    lists:foldl(
        fun(Field, Sum) -> Sum + element(Field, S) end,
        0, ?FIELDS).

join(Sep, Strings) ->
    string:join(Strings, Sep).

