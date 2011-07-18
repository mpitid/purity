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
%%% @doc Persistent Lookup Tables for `purity'.
%%%

-module(purity_plt).

-define(utils, purity_utils).

-import(?utils, [dict_fetch/3, dict_map/2, dict_update/2]).
-import(?utils, [str/2, uflatten/1]).

-export([load/1, save/2, default_path/0]).
-export([new/0, new/2, update/3, verify/1]).
-export([version/1, table/2, info_table/1, result_table/2]).
-export([dependent_modules/2, filenames/1]).
-export([export/1, export_text/1]).

-export_type([plt/0]).

-define(VERSION, "0.4").

-ifdef(TEST).
-include("purity_plt_tests.hrl").
-endif.

%% Record and type definitions.

-record(plt, {version   = ?VERSION   :: string(),
              checksums = []         :: [file_checksum()],
              modules   = dict:new() :: dict(),
              table     = dict:new() :: dict(),
              cache     = []         :: [{term(), dict()}]}).

-opaque plt() :: #plt{}.

%% Some type shortcuts.
-type files() :: [file:filename()].
-type options() :: purity_utils:options().
-type file_checksum() :: {file:filename(), binary()}.


%%% Creation and access functions %%%

-spec new() -> plt().
new() ->
    #plt{}.

-spec new(dict(), files()) -> plt().
new(Table, Filenames) ->
    #plt{table = Table,
         modules = module_dependencies(Table),
         checksums = compute_checksums(absolute(Filenames))}.

-spec table(plt(), options()) -> dict().
table(#plt{} = Plt, Options) ->
    case result_table(Plt, Options) of
        {ok, Table} -> Table;
        error -> info_table(Plt)
    end.

-spec result_table(plt(), options()) -> error | {ok, dict()}.
result_table(#plt{cache = C}, Options) ->
    assoc_find(cache_key(Options), C).

 -spec info_table(plt()) -> dict().
info_table(#plt{table = Table}) ->
    Table.


-spec version(plt()) -> string().
version(#plt{version = V}) -> V.


-spec filenames(plt()) -> files().
filenames(#plt{checksums = Sums}) ->
    [F || {F, _C} <- Sums].


%%% Persistence related functions %%%

-type load_errors() :: not_plt | no_such_file | read_error.

-spec load(file:filename()) -> {ok, plt()} | {error, load_errors()}.

load(Filename) ->
    case file:read_file(Filename) of
        {ok, Bin} ->
            try binary_to_term(Bin) of
                #plt{} = Plt ->
                    {ok, Plt}
            catch
                _:_ ->
                    {error, not_plt}
            end;
        {error, enoent} ->
            {error, no_such_file};
        {error, _} ->
            {error, read_error}
    end.


-spec save(plt(), file:filename()) -> ok | {error, string()}.

save(Plt, Filename) ->
    Bin = term_to_binary(Plt, [compressed]),
    case file:write_file(Filename, Bin) of
        ok ->
            ok;
        {error, Rsn} ->
            {error, str("Could not save PLT file ~s: ~p", [Filename, Rsn])}
    end.


-spec default_path() -> file:filename().

default_path() ->
    case os:getenv("PURITY_PLT") of
        false ->
            case os:getenv("HOME") of
                false ->
                    {error, "You need to set the HOME environment variable "
                            "in order to load the default PLT"};
                Home ->
                    filename:join(Home, ".purity.plt")
            end;
        PltPath ->
            PltPath
    end.


%%% PLT Verification %%%

 -spec verify(plt()) -> ok
                      | incompatible_version
                      | {changed_files, {files(), files()}}.

verify(#plt{version = ?VERSION, checksums = Sums}) ->
    case verify_file_checksums(Sums) of
        {[], []} ->
            ok;
        Failing ->
            {changed_files, Failing}
    end;
verify(#plt{}) ->
    incompatible_version.

verify_file_checksums(Sums) ->
    lists:foldl(fun verify_file/2, {[], []}, Sums).

verify_file({F, C}, {Mismatches, Errors} = Failing) ->
    case compute_checksum(F) of
        {ok, C} ->
            Failing;
        {ok, _Differs} ->
            {[F|Mismatches], Errors};
        {error, _Reason} ->
            {Mismatches, [F|Errors]}
    end.


%%% Checksum helpers %%%

%% @doc Assumes the files have already been examined and the checksum
%% can be computed without error.
compute_checksums(Filenames) ->
    Combine = fun (F, {ok, Sum}) -> {F, Sum} end,
    lists:zipwith(Combine, Filenames, [compute_checksum(F) || F <- Filenames]).


compute_checksum(Filename) ->
    case filelib:is_regular(Filename) of
        false ->
            {error, "Not a regular file: " ++ Filename};
        true ->
            case purity_utils:get_abstract_code_from_beam(Filename) of
                error ->
                    {error, "Could not extract abstract code from " ++ Filename};
                {ok, Abstract} ->
                    {ok, erlang:md5(term_to_binary(Abstract))}
            end
    end.


%% @doc Provided a list of files, return a list of modules which depend
%% on them and should be re-analysed.
-spec dependent_modules(plt(), files()) -> [module()].
dependent_modules(#plt{modules = Ms}, Filenames) ->
    uflatten([dict_fetch(module(F), Ms, []) || F <- Filenames]).


%% @doc Update the PLT with a new table and files.
-spec update(plt(), options(), {files(), dict(), dict()}) ->
    {ok, plt()} | {error, inconsistent_tables}.

update(Plt, Options, {Filenames, T, R}) ->
    #plt{cache = C0, checksums = CS0, table = T0} = Plt,
    case consistent(T, R) of
        false ->
            {error, inconsistent_tables};
        true ->
            AbsFiles = absolute(Filenames),
            %% Keep track of any modules which should be removed from
            %% the tables because they cannot be checksumed.
            {CS1, CSErrors} = separate([{F, compute_checksum(F)} || F <- AbsFiles]),
            Broken = [module(B) || B <- CSErrors],
            Analysed = [module(F) || F <- Filenames],

            %% Update any previous checksums with the current ones,
            %% in case parts of the table are being re-analysed.
            %% The analysis itself should make sure the table is
            %% consistent with regard to such files.
            CS = update_checksums(CS0, CS1),

            Tn = update_table(T0, T, Analysed, Broken),

            R0 = fetch_results(Options, C0),
            Rn = update_table(R0, R, Analysed, Broken),

            %% Keep only cached results which are still consistent, and
            %% remove broken modules from all of them.
            C1 = [{K, delete_modules(C, Broken)} ||
                  {K, C} <- keep_consistent(C0, Tn)],
            Cn = assoc_store(cache_key(Options), Rn, C1),

            {ok, Plt#plt{table = Tn, cache = Cn,
                         modules = module_dependencies(Tn),
                         checksums = CS}}
         end.

update_checksums(CS1, CS2) ->
    dict:to_list(dict_update(
            dict:from_list(CS1), dict:from_list(CS2))).

fetch_results(O, C) ->
    case assoc_find(cache_key(O), C) of
        {ok, R} ->
            R;
        error ->
            dict:new()
    end.

%% @doc Updating a PLT table consists of the following steps:
%% - Remove any re-analysed modules from the old table.
%%   This is necessary in order to account for the removal of functions
%%   in the re-analysed modules. Providing an explicit list of modules
%%   based on the file list is important too, in order to work seamlessly
%%   with result tables, which may contain arbitrary functions from the
%%   old result table.
%% - Update the resulting table with the new table.
%% - Remove any broken modules from the result.
update_table(Old, New, Modules, Broken) ->
    T1 = delete_modules(Old, Modules),
    T2 = dict_update(T1, New),
    delete_modules(T2, Broken).

keep_consistent(Cache, Info) ->
    lists:filter(fun ({_K, Result}) -> consistent(Info, Result) end, Cache).

%% @doc Since the analysis may add BIFs to the lookup table, just
%% verify that Results is a superset of it.
consistent(Info, Results) ->
    %% set(keys(Info)) <= set(keys(Results))
    lists:all(fun (K) -> dict:is_key(K, Results) end,
              dict:fetch_keys(Info)).

separate(Sums) ->
    lists:foldl(fun separate/2, {[], []}, Sums).

separate({F, {ok, C}}, {Good, Bad}) ->
    {[{F, C}|Good], Bad};
separate({F, {error, _}}, {Good, Bad}) ->
    {Good, [F|Bad]}.

%%% Helpers %%%

module(Filename) ->
    ?utils:filename_to_module(Filename).

delete_modules(Table, Modules) ->
    ?utils:delete_modules(Table, Modules).

%% @doc Produce a key from any relevant options.
cache_key(Options) ->
    lists:usort(lists:filter(fun relevant/1, Options)).

relevant({purelevel, _}) ->
    true;
relevant(termination) ->
    true;
relevant(both) ->
    true;
relevant(_) ->
    false.


%% @doc Reverse lookup table for inter-module dependencies, i.e.
%% each key maps to the list of modules which depend on it.
module_dependencies(T) ->
    dict_map(fun sets:to_list/1, reachable(?utils:module_rmap(T))).

reachable(Map) ->
    dict_map(fun (Fs) -> reachable(Fs, Map, sets:from_list(Fs)) end, Map).

reachable([], _Map, S) -> S;
reachable([K|Ks], Map, S) ->
    case [D || D <- dict_fetch(K, Map, []), not sets:is_element(D, S)] of
        [] -> reachable(Ks, Map, S);
        Ds -> reachable(Ks, Map, reachable(Ds, Map, add_elements(Ds, S)))
    end.

add_elements(Es, S) ->
    lists:foldl(fun sets:add_element/2, S, Es).


%% @doc Refer to filename:absname/1 for limitations of this approach.
absolute(Filenames) ->
    [filename:absname(F) || F <- Filenames].


%% @doc Consistent dict-like interface for handling association lists.
assoc_find(Key, List) ->
    case lists:keyfind(Key, 1, List) of
        false ->
            error;
        {Key, Value} ->
            {ok, Value}
    end.

assoc_store(Key, Value, []) ->
    [{Key, Value}];
assoc_store(Key, Value, [{Key, _Old}|T]) ->
    [{Key, Value}|T];
assoc_store(Key, Value, [H|T]) ->
    [H|assoc_store(Key, Value, T)].


-spec export(plt()) -> {string(), [{_,_}], [{_,_}], [{_,_}], [{_,_}]}.

%% @doc Export a PLT into a simple deterministic structure, useful
%% for debugging.
export(#plt{table = T, cache = C, checksums = CS, modules = Ms, version = V}) ->
    {V, lists:keysort(2, [{md5hex(MD5), F} || {F, MD5} <- CS]),
        lists:sort(dict:to_list(T)),
        lists:sort([{K, lists:sort(dict:to_list(R))} || {K, R} <- C]),
        lists:sort(dict:to_list(Ms))}.


%% @doc Export a PLT as plain text.
-spec export_text(plt()) -> [iolist()].

export_text(Plt) ->
    {Vsn, CS, T, R, M} = export(Plt),
    P1 = fun (F) -> io_lib:format(F ++ "~n", []) end,
    %% Converting to binary is necessary for large PLTs as character
    %% lists are very wasteful with regard to memory.
    P2 = fun (F, A) -> list_to_binary(io_lib:format(F ++ "~n", A)) end,
    PL = fun (L) -> print(P2, "~s: ~w", L, fun ?utils:fmt_mfa/1) end,
    [ P2("PLT ~s", [Vsn]),
      P1("FILES"), print(P2, "~s: ~s", CS),
      P1("TABLE"), PL(T),
      [[P2("RES ~p", [K]), PL(V)] || {K, V} <- R],
      P1("MOD"), print(P2, "~p: ~w", M) ].


print(Print, Fmt, Items) ->
    print(Print, Fmt, Items, fun (X) -> X end).

print(Print, Fmt, Items, MapKey) ->
    [Print(Fmt, [MapKey(K), V]) || {K, V} <- Items].


%md5hex(<<MD5:128/unsigned>>) -> ?utils:str("~32.16.0b", [MD5]).
md5hex(<<A:4/big-unsigned-integer-unit:8,
         B:4/big-unsigned-integer-unit:8,
         C:4/big-unsigned-integer-unit:8,
         D:4/big-unsigned-integer-unit:8>>) ->
    ?utils:str("~8.16.0b~8.16.0b~8.16.0b~8.16.0b", [A, B, C, D]).

