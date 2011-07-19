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
%% @copyright 2009-2011 Michael Pitidis, Kostis Sagonas
%% @author Michael Pitidis <mpitid@gmail.com>
%% @end
%% =====================================================================

%%%
%%% @doc Various utility functions for `purity'.
%%%

-module(purity_utils).

-export([dependencies/2, dependencies/3, module_rmap/1, function_rmap/1]).

-export([is_mfa/1, is_primop/1, is_expr/1, is_bif/1]).

-export([delete_modules/2]).

-export([dict_map/2, dict_fold/2, dict_mapfold/3, dict_cons/3]).
-export([dict_store/2, dict_store/3, dict_fetch/3, dict_update/2]).

-export([uflatten/1, str/2, fmt_mfa/1, filename_to_module/1]).

-export([internal_function/1]).

-export([emsg/1, emsg/2]).

-export([pmap/4, pmap/3]).

-export([get_core/1, get_core/2, get_abstract_code_from_beam/1]).

-export([option/2, option/3]).

-export([timeit/2, timeit/3, format_time/1, timed/2, get_time/0]).


-export_type([options/0, purity/0, purity_level/0, primop/0, emfa/0]).
-export_type([dependency/0, deplist/0, argument/0]).


-ifdef(TEST).
-include("purity_utils_tests.hrl").
-endif.


%% The type for options relevant to the analysis.

-type options() :: [atom() | {atom(), any()}].

%% The level of purity a function can have.
%% - p Referrentialy transparent.
%% - e May raise exceptions.
%% - d Dependent on the execution environment.
%% - s Has side-effects.
%% In the case of termination analysis, only two of the levels are used:
%% - p Terminating
%% - s Non-terminating
-type purity_level() :: p | e | d | s.

-type purity() :: purity_level() | {at_least, purity_level()}.

%% The value of the lookup table.
-type tab_value() :: deplist()              %% Info table.
                   | {purity(), deplist()}. %% Result table.

-type deplist() :: [dependency()].

-type dependency() :: {arg, pos_integer()} %% Higher order dependency on argument.
                    | {remote, emfa(), [argument()]}
                    | {local, mfa() | atom(), [argument()]}
                    | {free, atom(), [argument()]} %% Free variable.
                    | {primop, primop(), [argument()]}
                    | expr().

-type argument() :: {pos_integer(), mfa()} %% Concrete argument passed as argument.
                  %% The positions of an argument passed on to another call.
                  %% Used for tracking indirect higher order functions.
                  | {arg, {pos_integer(), pos_integer()}}
                  %% Track arguments which were passed "reduced" in a recursive call.
                  %% Used in termination analysis to detect terminating recursive functions.
                  | {sub, pos_integer()}.

%% Extended MFAs which may include variables in place of modules/functions.
-type emfa()   :: {module()|{var, atom()}, atom()|{var, atom()}, arity()}.

%% Primitive operations: These are implementation dependent and
%% their purity is hard-coded.
-type primop() :: {atom(), arity()}.

%% Erlang expressions influential to the analysis.
%% The `catch' expression depends on the execution environment since it
%% may contain part of the expression's stack trace.
%% The distinction between finite and infinite receive expressions is
%% included for the sake of termination analysis only.
-type expr()   :: {erl, 'catch' | {'receive', finite | infinite}}.


-spec module_rmap(dict()) -> dict().
module_rmap(Tab) ->
    dict:map(fun remove_self/2, dict_fold(fun module_rmap/3, Tab)).

module_rmap({M,_,_}, DL, Ms) ->
    lists:foldl(
        fun ({K,_,_}, Mn) -> dict_cons(K, M, Mn) end,
        Ms, dependencies(DL, fun is_mfa/1, true));
module_rmap(_, _, Ms) -> Ms.

remove_self(M, Rs) ->
    ordsets:del_element(M, ordsets:from_list(Rs)).


-spec function_rmap(dict()) -> dict().
function_rmap(Tab) ->
    dict_map(fun lists:usort/1, dict_fold(fun function_rmap/3, Tab)).

function_rmap(F, {_P, DL}, Rs) ->
    lists:foldl(
        fun (D, Rn) -> dict_cons(D, F, Rn) end,
        Rs, dependencies(DL, fun common_dependencies/1, false)).


-spec dependencies(tab_value(), fun((term()) -> boolean()), boolean()) -> [term()].
dependencies({_P, DepList}, Filter, Higher) when is_list(DepList) ->
    %% Handle the two different lookup tables transparently.
    dependencies(DepList, Filter, Higher);
dependencies(DepList, Filter, Higher) when is_list(DepList) ->
    L1 = [F || {_type, F, _As} <- DepList, Filter(F)] ++
         [E || E <- DepList, is_expr(E), Filter(E)],
    case Higher of
        true ->
            L2 = [F || {_type, _f, As} <- DepList,
                  {N, F} <- As, is_integer(N), Filter(F)],
            lists:reverse(L2, L1); % rev append
        false -> L1
    end.


common_dependencies(D) ->
    is_mfa(D) orelse is_primop(D) orelse is_expr(D).


%% @doc Higher level dependency collectors which work on an entire lookup table.
-spec dependencies(dict(), fun((term()) -> boolean())) -> [term()].

dependencies(Table, Filter) ->
    uflatten(dict:fold(dep_collector(Filter), [], Table)).

%% @doc Create a function to collect any dependencies passing the filter.
dep_collector(Filter) ->
    fun (_, V, Ds) -> [dependencies(V, Filter, true)|Ds] end.


%% Dependency filters.

-spec is_mfa(term()) -> boolean().
is_mfa({M,F,A}) when is_atom(M), is_atom(F), A >= 0, A =< 255 ->
    true;
is_mfa(_) ->
    false.

-spec is_primop(term()) -> boolean().
is_primop({P, A}) when is_atom(P), A >= 0, A =< 255 ->
    true;
is_primop(_) ->
    false.

-spec is_expr(term()) -> boolean().
is_expr({erl, _}) ->
    true;
is_expr(_) ->
    false.

-spec is_bif(term()) -> boolean().
is_bif(Fun) ->
    (is_mfa(Fun) orelse is_primop(Fun)) andalso purity_bifs:is_known(Fun).

%% @doc Remove any functions belonging to Modules from the Table.

-spec delete_modules(D, [module()]) -> D when D :: dict().

delete_modules(Table, []) ->
    Table;
delete_modules(Table, Modules) ->
    S = sets:from_list(Modules),
    dict:filter(
        fun({M,_,_}, _V) -> not sets:is_element(M, S); (_K, _V) -> true end,
        Table).


%%% Dict related helpers. %%%

-spec dict_map(fun((Value) -> Value), D) -> D when D :: dict().
dict_map(Fun, Dict) -> dict:map(fun (_K, V) -> Fun(V) end, Dict).

-spec dict_fold(fun((term(), term(), Acc) -> Acc), dict()) -> Acc when Acc :: dict().
dict_fold(Fun, Dict) -> dict:fold(Fun, dict:new(), Dict).

-spec dict_cons(term(), term(), D) -> D when D :: dict().
dict_cons(Key, Value, Dict) ->
    dict:update(Key, fun (Previous) -> [Value|Previous] end, [Value], Dict).

-spec dict_fetch(term(), dict(), term()) -> term().
dict_fetch(Key, Dict, Default) ->
    case dict:find(Key, Dict) of
        {ok, Value} -> Value;
        error -> Default
    end.

-spec dict_update(dict(), dict()) -> dict().
dict_update(Dict1, Dict2) ->
    dict:merge(fun (_K, _V1, V2) -> V2 end, Dict1, Dict2).


%% @doc Not as efficient as a native implementation would be,
%% but usefull all the same.
-spec dict_mapfold(fun((term(), Value, Acc) -> {Value, Acc}), Acc, dict()) -> {dict(), Acc}.
dict_mapfold(Fun, Acc0, Dict) ->
    dict:fold(
        fun(K, V1, {Map, Acc1}) ->
                {V2, Acc2} = Fun(K, V1, Acc1),
                {dict:store(K, V2, Map), Acc2} end,
        {dict:new(), Acc0}, Dict).


%% @doc Update a dict with a list of key-value pairs.
-spec dict_store([{term(),term()}], dict()) -> dict().
dict_store(KeyVals, Dict) ->
    lists:foldl(fun ({K, V}, D) -> dict:store(K, V, D) end, Dict, KeyVals).

%% @doc Update a list of keys with the same value in a dictionary.
-spec dict_store([term()], term(), dict()) -> dict().
dict_store(Keys, Value, Dict) ->
    lists:foldl(fun (K, D) -> dict:store(K, Value, D) end, Dict, Keys).


%%% Miscellaneous functions %%%

-spec uflatten([term()]) -> [term()].
uflatten(List) ->
    lists:usort(lists:flatten(List)).


-spec str(string(), [term()]) -> string().
str(Fmt, Args) ->
    lists:flatten(io_lib:format(Fmt, Args)).


-spec fmt_mfa(emfa() | primop() | expr()) -> string().
fmt_mfa({M, F, A}) -> % emfa
    str("~p:~p/~b", [M, F, A]);
fmt_mfa({erl,_} = E) -> % expr
    str("~p", [E]);
fmt_mfa({P, A}) -> % primop
    str("~p:/~b", [P, A]).

%% @doc Return what should correspond to the Erlang module for the
%% specified filename.
-spec filename_to_module(file:filename()) -> atom().

filename_to_module(Filename) ->
    list_to_atom(filename:basename(filename:rootname(Filename))).


%% @doc Detect common functions generated by the compiler for each module.
-spec internal_function(term()) -> boolean().

internal_function({_, module_info, 0}) -> true;
internal_function({_, module_info, 1}) -> true;
internal_function({_, record_info, 2}) -> true;
internal_function(_) -> false.


-spec emsg(string()) -> ok.
emsg(Msg) ->
    io:format(standard_error, "ERROR: ~p~n", [Msg]).

-spec emsg(string(), [any()]) -> ok.
emsg(Msg, Args) ->
    io:format(Msg ++ "~n", Args).


%% @doc Variation of the rpc:pmap/3 function which limits the number of
%% active processes. This can prove useful when each process requires
%% lots of memory.

-spec pmap({module(), atom()}, [any()], [any()], pos_integer()) -> [any()].

pmap({M, F}, Extra, List, N) ->
    Funs = [fun() -> apply(M, F, [Arg|Extra]) end || Arg <- List],
    pmap_init(Funs, N).

%% @doc Convenience wrapper around pmap/4 which uses one process per
%% logical processor.

-spec pmap({module(), atom()}, [any()], [any()]) -> [any()].

pmap(MF, Extra, List) ->
    pmap(MF, Extra, List, erlang:system_info(logical_processors)).

-record(pst, {num = 0,
              queue = [],
              results = [],
              active = 0}).

%% @doc Start by running Size processes in parallel, then add
%% one process for each process that terminates.
pmap_init(Funs, Size) ->
    {First, Next} = take(Size, Funs),
    St1 = lists:foldl(
        fun(_F, S) -> spawn_next(S) end, #pst{queue = First}, First),
    pool(St1#pst{queue = Next}).

take(N, List) when N > 0 ->
    take(N, List, []).

take(N, Rest, Acc) when N =:= 0 orelse Rest =:= [] ->
    {lists:reverse(Acc), Rest};
take(N, [H|T], Acc) ->
    take(N-1, T, [H|Acc]).

pool(#pst{active = 0, results = R}) ->
    [V || {_, V} <- lists:keysort(1, R)];
pool(#pst{results = R, active = A} = St0) ->
    receive
        {ok, Key, Val} ->
            St1 = St0#pst{results = [{Key, Val}|R], active = A-1},
            pool(spawn_next(St1))
    end.

spawn_next(#pst{num = N0, queue = [Fun|Qt], active = A} = St0) ->
    N1 = N0 + 1,
    Self = self(),
    spawn(fun() -> Res = Fun(), Self ! {ok, N1, Res} end),
    St0#pst{num = N1, queue = Qt, active = A + 1};
spawn_next(#pst{queue = []} = St0) ->
    St0.


%%% Core Erlang manipulation utilities:
%%% ___________________________________


%% @doc Compile to Core Erlang and return the parsed core tree.

-type get_core_ret() :: {ok, cerl:c_module()} | {error, string()}.
-spec get_core(file:filename()) -> get_core_ret().

get_core(Filename) ->
    get_core(Filename, []).

%% @doc Compile to Core Erlang and return the parsed core tree.

-spec get_core(file:filename(), [atom()]) -> get_core_ret().

get_core(Filename, Options) ->
    Compile = case string:to_lower(filename:extension(Filename)) of
        ".erl" ->
            fun compile_src/2;
        _ -> % Assumes .beam or no extension.
            fun compile_bin/2
    end,
    try Compile(Filename, [binary, copt, to_core, return_errors | Options]) of
        {ok, _Module, Core} ->
            {ok, Core};
        {error, beam} ->
            {error, "Could not extract abstract code from " ++ Filename};
        {error, Errors, _Warnings} ->
            {error, str("Compilation failed with errors: ~s (~p)", [Filename, Errors])}
    catch error:_ ->
        {error, "Compilation raised exception"}
    end.


compile_src(Filename, Options) ->
    compile:file(Filename, Options).


compile_bin(Filename, Options) ->
    case get_abstract_code_from_beam(Filename) of
        {ok, Abstract} ->
            compile:forms(Abstract, Options);
        error ->
            {error, beam}
    end.

%% Copied from dialyzer_utils.
%% term() should be beam_lib:forms() (not exported).
-spec get_abstract_code_from_beam(file:filename()) -> {ok, term()} | error.

get_abstract_code_from_beam(Filename) ->
    case beam_lib:chunks(Filename, [abstract_code]) of
        {ok, {_, List}} ->
            case lists:keyfind(abstract_code, 1, List) of
                {abstract_code, {raw_abstract_v1, Abstr}} ->
                    {ok, Abstr};
                _ ->
                    error
            end;
        _ ->
            %% No or unsuitable abstract code.
            error
    end.


-spec option(atom(), options()) -> term().

option(Name, Options) -> option(Name, Options, false).

-spec option(atom(), options(), term()) -> term().

option(Name, Options, Default) ->
    proplists:get_value(Name, Options, Default).


-type time() :: non_neg_integer().

%% @doc Report the execution time of a function.
%% @see timeit/2
%% @see timed/2

-spec timeit(string(), fun(), [term()]) -> term().

timeit(Msg, Fun, Args) ->
    io:format("~-22s... ", [Msg]),
    {T, R} = timed(Fun, Args),
    io:format("done in ~s~n", [format_time(T)]),
    R.

%% @doc Convenience shortcut to `timeit/3' for a function without arguments.
-spec timeit(string(), fun(() -> T)) -> T.

timeit(Msg, Fun) ->
    timeit(Msg, Fun, []).


%% @doc Format time in miliseconds to Minutes Seconds.Miliseconds.

-spec format_time(time()) -> string().

format_time(T) ->
    str("~bm~5.2.0fs", [T div 60000, (T rem 60000) / 1000]).


%% @doc Time the execution of a specified function, relying on
%% erlang:statistics/1 calls instead of erlang:now/0.

-spec timed(fun(), [term()]) -> {time(), term()}.

timed(Fun, Args) ->
    T1 = get_time(),
    Rt = apply(Fun, Args),
    T2 = get_time(),
    {T2 - T1, Rt}.


-spec get_time() -> time().

get_time() ->
    {T0, _} =
      case get(statistics) of
        undefined -> statistics(wall_clock);
        StatsType -> statistics(StatsType)
      end, T0.

