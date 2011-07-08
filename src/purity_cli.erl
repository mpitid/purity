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
%%% @doc Command line interface to `purity'.
%%%

-module(purity_cli).

-export([main/0]).


-define(plt, purity_plt).
-define(utils, purity_utils).

-import(?utils, [fmt_mfa/1, str/2]).

%% @doc Parse any command line arguments, analyse all supplied files
%% and print the results of the analysis to standard output.

-spec main() -> no_return().

main() ->
    T0 = get_time(),
    {Options, Files0} = parse_args(),

    with_option(version, Options, fun(true) ->
                io:format("Purity Analyzer for Erlang, version ~s~n", [?VSN]),
                halt(0) end),
    Files =
      case option(apps, Options) of
        false ->
            Files0;
        Libs ->
            Files0 ++ expand_libs(Libs)
      end,

    case {Files, option(no_check, Options)} of
        {[], true} ->
            io:format("You have to specify at least one file to analyse.~n"),
            halt(1);
        _ ->
            ok
    end,

    with_option(verbose, Options, fun(true) ->
                io:format("Analyzing the following files:~n"),
                lists:foreach(fun(F) -> io:format("\t~s~n", [F]) end, Files) end),

    Plt = case option(build_plt, Options) of
        true ->
            ?plt:new();
        false ->
            timeit("Loading PLT", fun() -> load_plt(Options) end)
    end,
    {Table, Final} = do_analysis(Files, Options, ?plt:table(Plt, Options)),

    %io:format("sizeof(Table): ~p, ~p~n", [erts_debug:size(Table), erts_debug:flat_size(Table)]),
    %io:format("sizeof(Final): ~p, ~p~n", [erts_debug:size(Final), erts_debug:flat_size(Final)]),

    %% An obvious problem with this approach is that we cannot close
    %% the opened file, but this is not important since the application
    %% exits soon after.
    Print = case option(output, Options) of
        false ->
            fun io:format/2;
        Filename ->
            case file:open(Filename, [write]) of
                {ok, Io} ->
                    fun(Fmt, Args) -> io:format(Io, Fmt, Args) end;
                {error, Reason} ->
                    io:format("Could not open file ~p for writing (~p)~n", [
                            Filename, Reason]),
                    fun io:format/2
            end
    end,

    Modules = [?utils:filename_to_module(M) || M <- Files],
    case option(quiet, Options) of
        false -> % Print results.
            Requested = sets:from_list(Modules),
            Print("Results:~n", []),
            lists:foreach(fun(A) -> pretty_print(Print, A) end, lists:sort(
                    [V || {{M,_,_}=MFA, _} = V <- dict:to_list(Final),
                        sets:is_element(M, Requested),
                        not ?utils:internal_function(MFA)]));
        true ->
            ok
    end,

    %% Optionally:
    %% Print functions for which we lack purity information.
    with_option(print_missing, Options, fun(true) ->
                print_missing(Print, Final) end),
    %% Write statistics to file.
    with_option(stats, Options, fun(Filename) ->
                do_stats(Filename, Modules, Final) end),

    case option(build_plt, Options) orelse option(add_to_plt, Options) of
        true ->
            PltIn = option(plt, Options, ?plt:default_path()),
            PltOut = option(output_plt, Options, PltIn),
            ok = timeit("Updating PLT", fun() ->
              {ok, Plt1} = ?plt:update(Plt, Options, {Files, Table, Final}),
              %Plt1 = purity_plt:update(Plt, Files, Table, Final, Options),
              ?plt:save(Plt1, PltOut) end);
        false ->
            ok
    end,
    io:format("Analysis completed in ~s~n", [format_elapsed(T0, get_time())]),
    init:stop().


do_stats(Filename, Modules, Table) ->
    ok = timeit("Generating statistics",
        fun() -> purity_stats:write(Filename,
                    purity_stats:gather(Modules, Table)) end).

do_analysis(Files, Options, Initial) ->
    Table = timeit("Traversing AST", fun() ->
                purity:pmodules(Files, Options, Initial) end),
    Final = timeit("Propagating values", fun() ->
                purity:propagate(Table, Options) end),
    {Table, Final}.


with_option(Opt, Options, Action) ->
    case option(Opt, Options) of
        false ->
            ok;
        Value ->
            Action(Value)
    end.

load_plt(Opts) ->
    Fn = option(plt, Opts, ?plt:default_path()),
    DoCheck = not option(no_check, Opts),
    case ?plt:load(Fn) of
        {error, Type} ->
            ?utils:emsg("Could not load PLT file '~s': ~p", [Fn, Type]),
            ?plt:new();
        {ok, Plt} when DoCheck ->
            case ?plt:verify(Plt) of
                incompatible_version ->
                    ?utils:emsg("PLT is out of date, create a new one"),
                    {fatal, incompatible_version};
                {changed_files, Failing} ->
                    io:format("PLT will be updated because the following "
                              "modules have changed:~n~s",
                              [string:join(format_changed(Failing),"\n")]),
                    New = purity:analyse_changed(Failing, Opts, Plt),
                    ok = ?plt:save(New, Fn),
                    New;
                ok ->
                    Plt
            end;
        {ok, Plt} ->
            Plt
    end.

format_changed({Mismatch, Errors}) ->
    [str(" M ~s", [F]) || F <- Mismatch] ++
    [str(" E ~s", [F]) || F <- Errors].


parse_args() ->
    Spec = [
        {purelevel, [
                "-l", "--level",
                {type, {intchoice, [1,2,3]}},
                {help, "Select one of three progressively stricter purity levels"}]},
        {with_reasons, [
                "--with-reasons",
                {type, bool},
                {help, "Print why each function is impure"}]},
        {both, [
            "--both",
            {type, bool},
            {help, "Perform both purity and termination analysis"}]},
        {termination, [
                "-t", "--termination",
                {type, bool},
                {help, "Perform termination analysis instead"}]},
        {output, [
                "-o", "--output",
                {help, "Write output to specified filename"}]},
        {build_plt, [
                "-b", "--build-plt",
                {type, bool},
                {help, "Create new PLT from the results of the analysis"}]},
        {no_check, [
                "-n", "--no-check",
                {type, bool},
                {help, "Don't check PLT"}]},
        {add_to_plt, [
                "--add-to-plt",
                {type, bool},
                {help, "Update PLT with any results from this analysis"}]},
        {plt, [
                "-p", "--plt",
                {help, "Use specified file as PLT instead of the default"}]},
        {output_plt, [
                "--output-plt",
                {help, "Store the PLT at the specified location"}]},
        {apps, [
                "--apps",
                {type, multiple},
                {help, "Analyse library applications"}]},
        {print_missing, [
                "-m", "--missing",
                {type, bool},
                {help, "Print functions with no purity information"}]},
        {stats, [
                "-s", "--stats",
                {help, "Write statistical information to file"}]},
        {quiet, [
                "-q", "--quiet",
                {type, bool},
                {help, "Don't print analysis results"}]},
        {verbose, [
                "-v", "--verbose",
                {type, bool},
                {help, "Generate more messages"}]},
        {version, [
                "--version",
                {type, bool},
                {help, "Print version information and exit"}]}
    ],
    Extra = [only_keep_last, {override, [{termination, purelevel}]}],
    cl_parser:parse_args(Spec, "usage: purity [options] file(s)", Extra).


option(Name, Options) ->
    proplists:get_value(Name, Options, false).


option(Name, Options, Default) ->
    proplists:get_value(Name, Options, Default).


pretty_print(Print, {MFA, Result}) ->
    Print("~s ~s.~n", [fmt_mfa(MFA), fmt(Result)]).


-spec print_missing(fun((_,_) -> ok), dict()) -> ok.

print_missing(Print, Table) ->
    {Funs, Primops} = purity:find_missing(Table),
    Print("Try analysing the following modules:~n", []),
    lists:foreach(fun(M) -> Print("  ~s~n", [M]) end,
        lists:usort([M || {M,_,_} <- Funs])),
    Print("Missing ~p functions:~n", [length(Funs)]),
    lists:foreach(fun(F) -> Print("    ~s~n", [fmt_mfa(F)]) end, Funs),
    Print("Missing ~p primops:~n", [length(Primops)]),
    lists:foreach(fun(F) -> Print("    ~s~n", [fmt_mfa(F)]) end, Primops).


%% @doc Consistent one-line formatting of purity results. Helps
%% produce cleaner diffs of the output.

-spec fmt(purity:pure()) -> string().

fmt({P, []}) ->
    fmt(P);
fmt({P, D}) when is_list(D) ->
    str("~s ~w", [fmt(P), simplify_deps(D)]);
fmt({at_least, P}) ->
    str(">= ~s", [P]);
fmt(P) when is_atom(P) ->
    atom_to_list(P).

simplify_deps(Ds) ->
    [simplify_dep(D) || D <- Ds].

simplify_dep({arg, N}) ->
    N;
simplify_dep({Type, Fun, Args}) ->
    {Type, Fun, unclutter(Args)};
simplify_dep({free, {F, Args}}) ->
    case unclutter(Args) of
        [] -> {free, F};
        As -> {free, {F, As}}
    end;
simplify_dep(Dep) ->
    Dep.

unclutter(Args) -> [A || A <- Args, not is_clutter(A)].

is_clutter({arg, {_, _}}) -> true;
is_clutter({sub, _}) -> true;
is_clutter(_) -> false.



%% @doc Execute Fun and print elapsed time.
timeit(Msg, Fun) ->
    io:format("~-22s... ", [Msg]),
    T1 = get_time(),
    Result = Fun(),
    T2 = get_time(),
    io:format("done in ~s~n", [format_elapsed(T1, T2)]),
    Result.

format_elapsed(T1, T2) ->
    Time = T2 - T1,
    M = Time div 60000,
    S = (Time rem 60000) / 1000,
    str("~bm~5.2.0fs", [M, S]).

get_time() ->
    {T0, _} = statistics(wall_clock),
    T0.


%% @doc Given a list of application names, return a list of the corresponding
%% BEAM files.
expand_libs(Libs) ->
    flatten1(
        [filelib:wildcard(filename:join(L, "*.beam")) || L <- get_lib_dirs(Libs),
            filelib:is_dir(L)]).

get_lib_dirs(Libs) ->
    [filename:absname(get_lib_dir(list_to_atom(L))) || L <- Libs].

get_lib_dir(erts) ->
    filename:join([code:root_dir(), "erts", "preloaded", "ebin"]);
get_lib_dir(Lib) ->
    case code:lib_dir(Lib, ebin) of
        {error, bad_name} ->
            atom_to_list(Lib);
        LibDir ->
            LibDir
    end.

flatten1(L) ->
    lists:foldl(fun lists:append/2, [], L).
