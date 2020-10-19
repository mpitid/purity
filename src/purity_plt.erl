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
%%% @doc Persistent Lookup Tables for `purity'.
%%%

-module(purity_plt).

-export([new/0, new/2]).
-export([check/1, update/5, remove_files/2]).
-export([load/1, save/2, get_default_path/0]).
-export([get_table/1, get_cache/2, get_version/1, get_files/1, get_affected/2]).

-import(purity_utils, [str/2, filename_to_module/1]).

-export_type([plt/0, changed_files/0]).

-define(VERSION, "0.3").

-type file_cksum() :: {file:filename(), binary()}.

-type files() :: [file:filename()].

-record(plt, {version   = ?VERSION   :: string(),
              checksums = []         :: [file_cksum()],
              mod_deps  = dict:new() :: dict:dict(),
              table     = dict:new() :: dict:dict(),
              cache     = []         :: [{term(), dict:dict()}]}).

-opaque plt() :: #plt{}.


-spec new() -> plt().

new() ->
    #plt{}.


-spec new(dict:dict(), files()) -> plt().

new(Table, Filenames) ->
    Checksums = compute_checksums(absolute(Filenames)),
    #plt{table = Table,
         checksums = Checksums,
         mod_deps = purity_utils:rev_mod_deps(Table)}.

absolute(Filenames) ->
    [filename:absname(F) || F <- Filenames].

-spec get_table(plt()) -> dict:dict().

get_table(#plt{table = Table}) ->
    Table.


%% @doc Return the cached version of the table, falling back to the
%% original one if no cache is found.
-spec get_cache(plt(), purity_utils:options()) -> dict:dict().

get_cache(#plt{table = Tab, cache = Cache}, Options) ->
    case assoc_find(cache_key(Options), Cache) of
        {ok, Table} ->
            preprocess(Table);
        error ->
            Tab
    end.


-spec get_version(plt()) -> string().

get_version(#plt{version = Version}) ->
    Version.


%% @doc Return the list of filenames whose pureness values are
%% contained in the PLT.
-spec get_files(plt()) -> files().

get_files(#plt{checksums = Sums}) ->
    [F || {F, _C} <- Sums].


-type load_errors() :: malformed_plt_data | no_such_file | read_error.
-spec load(file:filename()) -> {ok, plt()} | {error, load_errors()}.

load(Filename) ->
    case file:read_file(Filename) of
        {ok, Bin} ->
            try binary_to_term(Bin) of
                #plt{} = Plt ->
                    {ok, Plt}
            catch
                _:_ ->
                    {error, malformed_plt_data}
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


-spec get_default_path() -> file:filename().

get_default_path() ->
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


-type file_sum() :: {file:filename(), binary()}.
-type changed_files() :: [{differ | error, file:filename()}].

-spec check(plt()) -> ok | old_version | {differ, changed_files()}.

check(#plt{checksums = Sums} = P) ->
    case check_version(P) of
        error ->
            old_version;
        ok ->
            case lists:foldl(fun check_file/2, [], Sums) of
                [] ->
                    ok;
                Failed ->
                    {differ, Failed}
            end
    end.


check_version(#plt{version = ?VERSION}) ->
    ok;
check_version(#plt{}) ->
    error.

check_file({Filename, Checksum}, Failed) ->
    case compute_checksum(Filename) of
        {ok, Checksum} ->
            Failed;
        {ok, _Different} ->
            [{differ, Filename}|Failed];
        {error, _Reason} ->
            [{error, Filename}|Failed]
    end.


%% @doc This function assumes all of the files have been previously
%% examined, and their checksum can be computed without error.
-spec compute_checksums(files()) -> [file_sum()].

compute_checksums(Filenames) ->
    Combine = fun(F, {ok, Sum}) -> {F, Sum} end,
    lists:zipwith(Combine, Filenames, [compute_checksum(F) || F <- Filenames]).


-spec compute_checksum(file:filename()) -> {ok, binary()} | {error, string()}.

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


%% @doc Update PLT with a new table and cache, for the extra files provided.
%% The Table is considered to include up-to-date values for both previous
%% files, and ExtraFiles.
%%
%% It is however possible that not all files are valid, even though
%% they could have been analysed. This could be because they were
%% e.g. deleted between the call to analysis and the call to update.
%% Any module we can't checksum is therefore removed from both tables.
-spec update(plt(), files(), dict:dict(), dict:dict(), purity_utils:options()) -> plt().

update(Plt, ExtraFiles0, Table0, Final0, Options) ->
    #plt{cache = Cache0, checksums = Checksums0, mod_deps = MD0} = Plt,
    ExtraFiles = absolute(ExtraFiles0),
    %% Keep only valid modules.
    Sums = [{F, compute_checksum(F)} || F <- ExtraFiles],
    Good = lists:foldl(fun separate/2, [], Sums),
    BadMods = [filename_to_module(B) || B <- ExtraFiles -- [F || {F,_} <- Good]],
    Table1 = purity_utils:delete_modules(Table0, BadMods),
    Final1 = purity_utils:delete_modules(Final0, BadMods),
    %% Update cache.
    Cache1 = assoc_store(cache_key(Options), postprocess(Final1), Cache0),
    ExtraSet = sets:from_list(ExtraFiles),
    %% Update checksums, replacing any older ones.
    %% This could happen for instance when update was called without
    %% checking the PLT first.
    Checksums1 = [CS || {F, _} = CS <- Checksums0,
        not sets:is_element(F, ExtraSet)] ++ Good,
    %% Extract and merge reverse module dependencies.
    MD1 = dict:merge(fun(_K, _V1, V2) -> V2 end, MD0,
        purity_utils:rev_mod_deps(Table1)),
    Plt#plt{table = Table1, cache = Cache1,
            checksums = Checksums1, mod_deps = MD1}.


%% @doc Return the list of modules that need to be re-analysed,
%% because of changed files.
-spec get_affected(plt(), changed_files()) -> [module()].

get_affected(#plt{mod_deps = MD}, Changed) ->
    RevDeps = [dict:find(filename_to_module(F), MD) || {_Rsn, F} <- Changed],
    lists:usort(lists:flatten([Mods || {ok, Mods} <- RevDeps])).


assoc_store(Key, Value, []) ->
    [{Key, Value}];
assoc_store(Key, Value, [{Key, _Old}|T]) ->
    [{Key, Value}|T];
assoc_store(Key, Value, [H|T]) ->
    [H|assoc_store(Key, Value, T)].

assoc_find(Key, List) ->
    case lists:keyfind(Key, 1, List) of
        false ->
            error;
        {Key, Value} ->
            {ok, Value}
    end.


separate({F, {ok, S}}, Acc) ->
    [{F, S}|Acc];
separate({_, {error, Rsn}}, Acc) ->
    purity_utils:emsg(Rsn),
    Acc.


postprocess(Table) ->
    dict:map(fun(_K, {false,_}) -> false; (_K, V) -> V end, Table).

preprocess(Table) ->
    dict:map(fun(_K, false) -> {false, <<"Cache">>}; (_K, V) -> V end, Table).


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


%% @doc Return a copy of the PLT with specified files removed.
%% Any functions from modules corresponding to those files are
%% removed from the normal as well as the cached tables.
-spec remove_files(plt(), [file:filename()]) -> plt().

remove_files(#plt{table = T0, cache = C0, checksums = CS0}, Files) ->
    Mods = sets:from_list([filename_to_module(F) || F <- Files]),
    Pred = fun({M,_,_}, _) -> not sets:is_element(M, Mods); (_, _) -> true end,
    T1 = dict:filter(Pred, T0),
    FS = sets:from_list(Files),
    #plt{table = T1,
         cache = [{K, dict:filter(Pred, C)} || {K, C} <- C0],
         mod_deps = purity_utils:rev_mod_deps(T1),
         checksums = [CS || {F, _C} = CS <- CS0, not sets:is_element(F, FS)]}.

