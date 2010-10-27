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

-module(runtest).

-export([main/1]).

-export([build_filters/2, apply_filters/2]).
-export([dump_term/2]).

-export([filter_module/1, filter_reasons/1, filter_nested/1,
        filter_args/1, filter_binaries/1, filter_pretty/1]).

-import(purity_utils, [str/2, internal_function/1]).


-spec
main([file:filename()]) -> no_return().
main([File1, File2]) ->
    main([File1, File2, "."]);
main([File1, File2, DumpDir]) ->
    {Opts, Exp1} = parse_test_file(File2),
    {Topts, Popts} = parse_test_opts(Opts),
    Tab1 = run_analysis(File1, Popts, Topts),
    put(module, purity_utils:filename_to_module(File1)),
    Filters = build_filters(standard_filters(), Topts),
    Tab2 = apply_filters(dict:to_list(Tab1), Filters),
    Exp2 = apply_filters(Exp1, Filters),
    case Tab2 =:= Exp2 of
        true -> halt(0);
        false ->
            io:format("TEST FAILED: ~s ~s~n", [File1, File2]),
            F1 = outfile(DumpDir, File2, ".org"),
            F2 = outfile(DumpDir, File2, ".exp"),
            dump_term(F1, Tab2),
            dump_term(F2, Exp2),
            %io:format("Diff: ~p~n",[diff(Tab2,Exp2)]),
            io:format("vimdiff -R '~s' '~s'~n", [F1, F2]),
            halt(1)
    end.

%diff(A, B) ->
%    S1 = lists:usort(A), S2 = lists:usort(B),
%    ordsets:subtract(ordsets:union(S1, S2), ordsets:intersection(S1, S2)).

run_analysis(File, Popts, Topts) ->
    Tab = purity:modules([File], Popts, dict:new()),
    case option(traverse_only, Topts) of
        true -> Tab;
        false -> purity:propagate(Tab, Popts) end.


parse_test_file(Filename) ->
    {Opts, Vals} = read_term(Filename),
    {Opts, Vals}.

%% @doc Separate test-related options from purity-related ones.
parse_test_opts(Opts) ->
    {T, P} = lists:partition(fun is_test_option/1, Opts),
    {[element(2,O)||O <- T], P}.


is_test_option({test,{_,_}}) -> true;
is_test_option({test,A}) when is_atom(A) -> true;
is_test_option(_) -> false.

outfile(Dir, File, Ext) ->
    filename:absname_join(
        filename:absname(Dir),
        filename:basename(File) ++ Ext).


%%% Filters %%%

standard_filters() ->
    [{unless, everything, filter_module}
    ,{unless, with_nested, filter_nested}
    ,{unless, with_reasons, filter_reasons}
    ,{unless, with_args, filter_args}
    ,filter_binaries
    ].

build_filters([{unless,Opt,F}|Fs], Opts) ->
    case option(Opt, Opts) of
        true -> build_filters(Fs, Opts);
        false -> [make_filter(F)|build_filters(Fs, Opts)] end;
build_filters([F|Fs], Opts) when is_atom(F) ->
    [make_filter(F)|build_filters(Fs, Opts)];
build_filters([], _) -> [].

make_filter(F) -> erlang:make_fun(?MODULE, F, 1).

apply_filters(Tab, Filters) ->
    lists:foldl(fun(F, T) -> F(T) end, lists:sort(Tab), Filters).


-type
tab() :: [{any(),any()}].

-spec
filter_module(tab()) -> tab().
filter_module(Tab) ->
    Mod = get(module),
    true = Mod =/= undefined,
    [Val || {K,_}=Val <- Tab, in_module(Mod, K), not internal_function(K)].

in_module(M, {M,_,_}) -> true;
in_module(_, _) -> false.

-spec
filter_args(tab()) -> tab().
filter_args(Tab) ->
    [{K, filter_args1(V)} || {K, V} <- Tab].

filter_args1(C) when is_list(C) -> [filter_args2(D) || D <- C];
filter_args1(Val) -> Val.

filter_args2({Type,Fun,Args}) when is_list(Args) ->
    {Type,Fun,[A || A <- Args, not unwanted_arg(A)]};
filter_args2(Arg) -> Arg.

unwanted_arg({arg,{_,_}}) -> true;
unwanted_arg({sub,_}) -> true;
unwanted_arg(_) -> false.

-spec
filter_nested(tab()) -> tab().
filter_nested(Tab) ->
    %% This can only be approximate and rough.
    {ok, Pat} = re:compile("_[0-9]-[0-9]+$"),
    [Val || {K, _}=Val <- Tab, not nested(K, Pat)].

nested({_,F,_}, Pat) when is_atom(F) ->
    nomatch =/= re:run(atom_to_list(F), Pat);
nested(_, _) -> false.

%% Convert binaries to lists to make sure the table comparison works.
-spec
filter_binaries(tab()) -> tab().
filter_binaries(Tab) ->
    [{K, b2l(V)} || {K, V} <- Tab].

b2l({false, R}) when is_binary(R) ->
    {false, binary_to_list(R)};
b2l(V) -> V.

-spec
filter_reasons(tab()) -> tab().
filter_reasons(Tab) ->
    [{K, strip_reason(V)} || {K, V} <- Tab].

strip_reason({false,_}) -> false;
strip_reason(V) -> V.

-spec
filter_pretty(tab()) -> string().
filter_pretty(Tab) -> string:join([format(I) || I <- Tab], "\n").

format({K, V}) -> str("~s ~s", [format_key(K), format_val(V)]).

format_key({M,F,A}) when is_integer(A) -> str("~s:~s/~b", [M,F,A]);
format_key({P,A}) when is_atom(P), is_integer(A) -> str("~s/~b", [P,A]);
format_key(K) -> str("~p",[K]).

format_val(true) -> "pure";
format_val(undefined) -> "undefined";
format_val(false) -> "impure";
format_val({false,Rsn}) -> str("impure(~s)",[Rsn]);
format_val(C) when is_list(C) -> str("~w",[C]);
format_val(V) -> str("~p",[V]).


%%% Other Helpers %%%

%% @doc Read an Erlang term from a file.
read_term(Filename) ->
    {ok, Fd} = file:open(Filename, [read]),
    {ok, Term} = io:read(Fd, ''),
    ok = file:close(Fd),
    Term.

dump_term(Filename, Term) ->
    case filelib:is_file(Filename) of
        true -> throw({file_exists,Filename});
        false ->
            {ok, Fd} = file:open(Filename, [write]),
            ok = io:format(Fd, "~s~n", [filter_pretty(Term)]),
            ok = file:close(Fd) end.

option(Key, Val) ->
    proplists:get_value(Key, Val, false).

