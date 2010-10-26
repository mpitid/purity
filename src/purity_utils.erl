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
%%% @doc Various utility functions for `purity'.
%%%

-module(purity_utils).

-export([get_core/1, get_core/2, get_abstract_code_from_beam/1]).
-export([str/2, fmt_mfa/1]).
-export([filename_to_module/1, delete_modules/2]).
-export([internal_function/1]).
-export([rev_deps/1, rev_mod_deps/1]).
-export([collect_dependencies/1, is_concrete_fun/1, is_primop/1]).
-export([dict_cons/3]).

-export([remove_args/1]).
-export([count/1]).

-export([pmap/4]).
-export([emsg/1, emsg/2]).

-export_type([emfa/0, primop/0, options/0]).


%% @doc Remove argument annotations from any context values.
-spec remove_args(any()) -> any().
remove_args(Ctx) when is_list(Ctx) ->
    %% usort to remove any duplicate dependencies after cleanup.
    lists:usort([remove_arg(C) || C <- Ctx]);
remove_args(Val) ->
    Val.

remove_arg({Type, MFA, Args}) ->
    {Type, MFA, lists:filter(fun is_not_arg/1, Args)};
remove_arg({free, {Var, Args}}) ->
    {free, {Var, lists:filter(fun is_not_arg/1, Args)}};
remove_arg(Val) ->
    Val.

is_not_arg({arg, _}) ->
    false;
is_not_arg(_) ->
    true.


%% Extended MFA, with support for variable modules/functions.
-type emfa()    :: {module() | {var, atom()}, atom() | {var, atom()}, arity()}.
-type primop()  :: {atom(), arity()}.

-type options() :: [atom() | {atom(), any()}].


%% @doc Return a mapping of modules to a list of modules that
%% may have dependencies on them.

-spec rev_mod_deps(dict()) -> dict().

rev_mod_deps(Table) ->
    dict:map(
        fun(_K, Mods) -> lists:usort(Mods) end,
        dict:fold(fun rev_mod_deps/3, dict:new(), Table)).

rev_mod_deps({M,_,_}, Val, Deps) ->
    lists:foldl(
        fun({K,_,_}, D) -> dict_cons(K, M, D) end,
        Deps,
        [F || F <- collect_dependencies(Val), is_concrete_fun(F)]);
rev_mod_deps(_NonMFA, _Val, Deps) ->
    Deps.


%% @doc Return a mapping of functions or primops to a list of
%% functions their purity depends on.
-spec rev_deps(dict()) -> dict().

rev_deps(Table) ->
    dict:map(
        fun(_Key, Vals) -> lists:usort(Vals) end,
        dict:fold(fun rev_deps/3, dict:new(), Table)).

rev_deps(Key, Val, Deps) when is_list(Val) ->
    %% Only collect dependencies of concrete MFAs and erlang
    %% expressions like `catch' and `receive'. The latter
    %% should only have special dependencies.
    case is_mfa(Key) orelse is_primop(Key) orelse is_expr(Key) of
        true ->
            lists:foldl(
                fun(Dep, D) -> dict_cons(Dep, Key, D) end,
                Deps,
                %% Don't collect dependencies from arguments, they
                %% should be handled by call-site analysis instead.
                [F || F <- collect_dependencies(Val, false),
                    is_mfa(F) orelse is_expr(F) orelse
                    is_primop(F) orelse is_special(F)]);
        false ->
            Deps
    end;
rev_deps(_NonMFA, _orNonCtx, Deps) ->
    Deps.


%% @doc Return a list of functions, variables or primops,
%% that appear on the context list.
-spec collect_dependencies([term()]) -> [emfa() | primop()].

collect_dependencies(Val) ->
    collect_dependencies(Val, true).

collect_dependencies(Val, All) when is_list(Val) ->
    L1 = [Fun || {_Type, Fun, _Args} <- Val]
      ++ [S || S <- Val, is_special(S) orelse is_expr(S)],
    case All of
        false ->
            L1;
        true ->
            %% Collect functions that occur in the argument list as well.
            L2 = [Fun || {_Type, _Fun, Args} <- Val, {_, Fun} <- Args],
            lists:reverse(L2, L1)
    end;
collect_dependencies(_NonCtx, _) ->
    [].


-spec is_mfa(term()) -> boolean().

is_mfa({M,F,A}) when is_atom(M), is_atom(F), A >= 0, A =< 255 ->
    true;
is_mfa(_) ->
    false.

-spec is_expr(term()) -> boolean().

is_expr({erl, _Expr}) ->
    true;
is_expr(_) ->
    false.

-spec is_concrete_fun(term()) -> boolean().

is_concrete_fun({M, F, _}) when is_atom(M), is_atom(F) ->
    true;
is_concrete_fun(_) ->
    false.

-spec is_primop(term()) -> boolean().

is_primop({P, A}) when is_atom(P), is_integer(A), A >= 0 ->
    true;
is_primop(_) ->
    false.

-spec is_special(term()) -> boolean().

is_special(side_effects) ->
    true;
is_special(non_determinism) ->
    true;
is_special(exceptions) ->
    true;
is_special(_) ->
    false.


%% Faster than dict:append, in case order is not important.

-spec dict_cons(term(), term(), dict()) -> dict().

dict_cons(Key, Val, Dict) ->
    dict:update(Key, fun(Old) -> [Val|Old] end, [Val], Dict).


%%% Core Erlang manipulation utilities:
%%% ___________________________________


%% @spec get_core(file:filename()) -> Ret
%% where
%%    Ret = {ok, Core::cerl:c_module()} | {error, Reason::string()}
%% @doc Compile to Core Erlang and return the parsed core tree.

-type get_core_ret() :: {ok, cerl:c_module()} | {error, string()}.
-spec get_core(file:filename()) -> get_core_ret().

get_core(Filename) ->
    get_core(Filename, []).

%% @spec get_core(file:filename(), [atom()]) -> Ret
%% where
%%    Ret = {ok, Core::cerl:c_module()} | {error, Reason::string()}
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


-spec str(string(), [any()]) -> string().

str(Format, Args) ->
    lists:flatten(io_lib:format(Format, Args)).


%% @doc Return the various representations of functions/primops as a string.

-spec fmt_mfa(emfa() | primop()) -> string().

fmt_mfa({M, F, A}) ->
    str("~p:~p/~p", [M, F, A]);
fmt_mfa({F, A}) ->
    str("primop ~s/~B", [F, A]).


%% @doc Remove any functions belonging to Modules from the Table.

-spec delete_modules(dict(), [module()]) -> dict().

delete_modules(Table, []) ->
    Table;
delete_modules(Table, Modules) ->
    S = sets:from_list(Modules),
    dict:filter(
        fun({M,_,_}, _Val) -> not sets:is_element(M, S); (_K, _V) -> true end,
        Table).


%% @doc Return what should correspond to the Erlang module for the
%% specified filename.
-spec filename_to_module(file:filename()) -> atom().

filename_to_module(Filename) ->
    list_to_atom(filename:basename(filename:rootname(Filename))).


-spec internal_function(term()) -> boolean().

internal_function({_, module_info, 0}) ->
    true;
internal_function({_, module_info, 1}) ->
    true;
internal_function({_, record_info, 2}) ->
    true;
internal_function(_) ->
    false.

%% @doc Simple stateful acculumator for quick testing.
-spec count(any()) -> pos_integer().

count(Name) ->
    Key = {count, Name},
    case get(Key) of
        undefined ->
            put(Key, 2),
            1;
        N when is_integer(N) ->
            put(Key, N + 1)
    end.



%% @doc Variation of the rpc:pmap/3 function which limits the number of
%% active processes. This can prove useful when each process requires
%% lots of memory.

-spec pmap({module(), atom()}, [any()], [any()], pos_integer()) -> [any()].

pmap({M, F}, Extra, List, N) ->
    Funs = [fun() -> apply(M, F, [Arg|Extra]) end || Arg <- List],
    pmap_init(Funs, N).

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


-spec emsg(string()) -> ok.
emsg(Msg) ->
    io:format(standard_error, "ERROR: ~p~n", [Msg]).

-spec emsg(string(), [any()]) -> ok.
emsg(Msg, Args) ->
    io:format(Msg ++ "~n", Args).

