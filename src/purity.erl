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
%%% @doc Pureness analysis of Erlang functions.
%%%

% FIXME:
% - Add separate predefined values for termination.
% - Characterise higher order function arguments as remote/local.

% TODO


-module(purity).

-define(collect, purity_collect).
-define(analyse, purity_analyse).
-define(utils, purity_utils).
-define(plt, purity_plt).


-export([module/1, files/1, pfiles/1]).

-export([propagate/2, propagate/3]).

-export([module/2, is_pure/2, find_missing/1, analyse_changed/3]).

-export_type([pure/0]).


-type plt()     :: purity_plt:plt().
-type pure()    :: purity_analyse:pure().
-type options() :: purity_utils:options().


-spec module(cerl:c_module()) -> dict().

module(Core) ->
    ?collect:module(Core).

-spec files([string()]) -> dict().

files(Filenames) ->
    ?collect:files(Filenames).

-spec pfiles([string()]) -> dict().

pfiles(Filenames) ->
    ?collect:pfiles(Filenames).


-spec propagate(dict(), options()) -> dict().

propagate(Tab, Opts) ->
    ?analyse:propagate(Tab, Opts).


-spec propagate(dict(), purity_plt:plt(), options()) -> dict().

propagate(Tab, Plt, Opts) ->
    ?analyse:analyse(Tab, Plt, Opts).


%% @doc Simple purity test, only distinguishes between pure and impure.
%% Any function missing from the lookup table is also considered impure.
-spec is_pure(mfa(), dict()) -> boolean().

is_pure({_,_,_} = MFA, Table) ->
    case dict:find(MFA, Table) of
        {ok, {p, []}} ->
            true;
        _ ->
            false
    end.

%% @doc Analyse a module and return a lookup table of concrete results,
%% indexed by `{Module, Function, Arity}'.
%%
%% Analysis starts from parsed core erlang terms.
%%
%% @see is_pure/2
%% @see module/1
%% @see propagate/3
-spec module(cerl:c_module(), options()) -> dict().

module(Core, Options) ->
    Tab = module(Core),
    Plt = load_plt_no_errors(Options),
    % TODO: Maybe update and save PLT as well.
    propagate(Tab, Plt, Options).


%% @doc Load a PLT from the provided options. If no PLT is found, or
%% there are errors, return a new PLT.
load_plt_no_errors(Opts) ->
    File = ?utils:option(plt, Opts, ?plt:default_path()),
    Check = not ?utils:option(no_check, Opts, false),
    case ?plt:load(File) of
        {error, _Type} ->
            ?plt:new();
        {ok, Plt} when Check ->
            case ?plt:verify(Plt) of
                ok -> Plt;
                _F -> ?plt:new()
            end;
        {ok, Plt} -> % No checks, unwise.
            Plt
    end.


%% @doc Return a list of MFAs and a list of primops for which we have no
%% pureness information.

-spec find_missing(dict()) -> {[mfa()], [purity_utils:primop()]}.

find_missing(Table) ->
    Set1 = sets:from_list(?utils:dependencies(Table, fun ?utils:is_mfa/1)),
    Set2 = sets:from_list(dict:fetch_keys(Table)),
    Funs = sets:subtract(Set1, Set2),
    Set3 = sets:from_list(?utils:dependencies(Table, fun ?utils:is_primop/1)),
    Prim = sets:subtract(Set3, Set2),
    {sets:to_list(Funs), sets:to_list(Prim)}.



%% @doc Remove any files with errors from the PLT, and re-analyse
%% changed files, as well as any dependencies thereof.

-spec analyse_changed({[file:filename()], [file:filename()]},
                      options(), plt()) -> plt().

analyse_changed({Changed, Errors}, _Options, Plt) ->
    Combined = Changed ++ Errors,
    %% First strip the table of both changed and removed files, so that
    %% there are no left-over MFAs, e.g. when removing a function from a module.
    T1 = ?utils:delete_modules(?plt:info_table(Plt), to_modules(Combined)),
    %% Determine which modules should be re-analysed: Dependent -- Missing.
    DM = ?plt:dependent_modules(Plt, Combined) -- to_modules(Errors),
    %% We need the filenames of these modules. Since we cannot map a module to
    %% a specific filename, figure this out by the list of filenames stored in
    %% the PLT. It's a given that true == subset(DM, to_modules(Files)).
    Files = ?plt:filenames(Plt) -- Errors,
    Map = dict:from_list([{?utils:filename_to_module(F), F} || F <- Files]),
    DF = [dict:fetch(M, Map) || M <- DM],
    %% Collect information on these modules, and create a new PLT. Naturally
    %% any cached result tables are dismissed.
    ?plt:new(?utils:dict_update(T1, pfiles(DF)), Files).

to_modules(Filenames) ->
    [?utils:filename_to_module(F) || F <- Filenames].

