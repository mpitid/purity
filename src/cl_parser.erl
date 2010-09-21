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
%%% @doc Configurable command line argument parser.
%%%
%%% This module is loosely modeled after the `optparse' Python module,
%%% but is significantly more limited.
%%%

-module(cl_parser).

-export([parse_args/2]).

-type desc()        :: [{atom(), [any()]}].
-type options()     :: [atom() | {atom(), any()}].
-type arguments()   :: [string()].

%% A reference to the finalized description in it's original form
%% is preserved in `desc', for use with pretty_print/2.
-record(spec, {names    = dict:new() :: dict(),
               types    = dict:new() :: dict(),
               help     = dict:new() :: dict(),
               defaults = dict:new() :: dict(),
               desc     = []         :: desc()}).


%% @spec parse_args(desc(), string()) -> {options(), arguments()}
%%
%% @doc Parse the command line and return a 2-tuple of options
%% and plain arguments.
%%
%% Desc is a list of tuples, describing the command line arguments, e.g.
%%
%% `[{help,
%%     ["-h", "--help", {type, bool}, {help, "Produce this help message"}],'
%%
%%  `{conf,
%%     ["-c", "--conf", {type, string}, {help, "Path to configuration file"}]}]'
%%
%% The help option is added by default. The default type is `string',
%% which expects one argument, and can be omitted from the description.
%% It's not necessary to specify both short and long options.
%%
%% Options is a list of atoms or tuples of atoms and values, depending
%% on the type. In our example, if `-h' and `-c test.cnf' was specified it
%% would be `[help,{conf,"test.cnf"}]'.

-spec parse_args(desc(), string()) -> {options(), arguments()}.

parse_args(Desc, Usage) ->
    Specs = build_specs(Desc),
    Args = init:get_plain_arguments(),
    try parse(Args, Specs) of
        {Opts, _Rest} = Ret ->
            case lists:member(help, Opts) of
                true ->
                    pretty_print(Usage, Specs),
                    init:stop();
                false ->
                    Ret
            end
    catch
        throw:{parser_error, Msg} ->
            io:format("Parser error: ~s.~n", [Msg]),
            init:stop(1)
    end.


build_specs(Descriptions) ->
    PrepDesc = add_if_missing(
        {help, ["-h", "--help", {type,bool}, {help,"Print this help message"}]},
        [prepare(D) || D <- Descriptions]),
    lists:foldl(
        fun({Name, Desc}, Spec) ->
                lists:foldl(fun(D, S) -> build_spec(Name, D, S) end, Spec, Desc)
        end,
        #spec{desc = PrepDesc},
        PrepDesc).

prepare({Name, Desc}) ->
    Desc1 = add_if_missing({type, string}, Desc),
    Desc2 = add_if_missing({help, "Undocumented"}, Desc1),
    {Name, Desc2}.

add_if_missing({Key, _} = Value, Desc) ->
    case lists:keysearch(Key, 1, Desc) of
        {value, _} ->
            Desc;
        false ->
            [Value|Desc]
    end.


build_spec(Name, "--" ++ Long, #spec{names = Names} = Spec) ->
    Spec#spec{names = dict:store(Long, Name, Names)};
build_spec(Name, "-" ++ Short, #spec{names = Names} = Spec) ->
    Spec#spec{names = dict:store(Short, Name, Names)};
build_spec(Name, {type, Type}, #spec{types = Types} = Spec) ->
    Spec#spec{types = dict:store(Name, Type, Types)};
build_spec(Name, {help, Msg}, #spec{help = Help} = Spec) ->
    Spec#spec{help = dict:store(Name, Msg, Help)};
build_spec(Name, {default, Value}, #spec{defaults = Defaults} = Spec) ->
    Spec#spec{defaults = dict:store(Name, Value, Defaults)}.


parse(Arguments, #spec{defaults = D} = Spec) ->
    {Options0, Rest} = parse(Arguments, Spec, [], []),
    Options1 = dict:fold(fun add_default/3, Options0, D),
    {Options1, lists:reverse(Rest)}.

add_default(Opt, Value, Opts) ->
    case proplists:get_value(Opt, Opts) of
        undefined ->
            opt_add(Opts, Opt, Value);
        _ ->
            Opts
    end.

parse([], _, Options, Rest) ->
    {Options, Rest};
parse(["--"|T], _Spec, Options, Rest) ->
    %% Stop interpreting options.
    {Options, T ++ Rest};
parse(["-" ++ _ = Option|T], Spec, Options, Rest) ->
    OptName = strip_dashes(Option),
    assert_valid_option(Option, Spec),
    Name = opt_name(OptName, Spec),
    {Remaining, NewOptions} = case opt_type(Name, Spec) of
        bool ->
            {T, opt_add(Options, Name)};
        int ->
            {Rem, [Value]} = opt_take(T, 1, OptName),
            {Rem, opt_add(Options, Name, list_to_integer(Value))};
        {intchoice, Choices} ->
            {Rem, [SValue]} = opt_take(T, 1, OptName),
            IValue = list_to_integer(SValue),
            case lists:member(IValue, Choices) of
                true ->
                    {Rem, opt_add(Options, Name, IValue)};
                false ->
                    opt_error("Invalid choice, pick one between ~p", [Choices])
            end;
        multiple ->
            case T of
                [] ->
                    opt_error("Option ~p expects at least one argument", [OptName]);
                _ ->
                    {Rem, Values} = opt_take_all(T, []),
                    {Rem, opt_add(Options, Name, Values)}
            end;
        string ->
            {Rem, [Value]} = opt_take(T, 1, OptName),
            {Rem, opt_add(Options, Name, Value)}
    end,
    parse(Remaining, Spec, NewOptions, Rest);
parse([Arg|T], Spec, Options, Rest) ->
    parse(T, Spec, Options, [Arg|Rest]).


opt_add(Options, Opt) ->
    [Opt|Options].

opt_add(Options, Opt, Value) ->
    [{Opt, Value}|Options].

opt_name(Opt, #spec{names = Names}) ->
    dict:fetch(Opt, Names).

opt_type(Opt, #spec{types = Types}) ->
    dict:fetch(Opt, Types).

opt_take([], N, Name) when N > 0 ->
    opt_error("Option ~p expects ~p more argument(s)", [Name, N]);
opt_take([Val|Options], N, Name) when N > 0 ->
    {Remaining, Values} = opt_take(Options, N-1, Name),
    {Remaining, [Val | Values]};
opt_take(Options, 0, _) ->
    {Options, []}.

%% @doc Collect any non-option argument until none is left, or
%% an option is encountered.
opt_take_all([], Acc) ->
    {[], Acc};
opt_take_all(["-"++_|_]=Remaining, Acc) ->
    {Remaining, lists:reverse(Acc)};
opt_take_all([Val|Opts], Acc) ->
    opt_take_all(Opts, [Val|Acc]).


opt_error(Msg, Args) ->
    erlang:throw({parser_error, io_lib:format(Msg, Args)}).

assert_valid_option(Opt, #spec{names = Names}) ->
    case dict:find(strip_dashes(Opt), Names) of
        {ok, _} ->
            ok;
        error ->
            opt_error("Unrecognised option ~p", [Opt])
    end.

strip_dashes("-" ++ Rest) ->
    strip_dashes(Rest);
strip_dashes(Rest) ->
    Rest.


pretty_print(Usage, #spec{desc = Desc}) ->
    io:format("~s~n~n", [Usage]),
    lists:foreach(fun pretty_print/1, Desc).

pretty_print({_, Desc}) ->
    Flag1 = string:join([Opt || [$-|_] = Opt <- Desc], "|"),
    Flag2 = string:join([Flag1 | ["VALUE" || {type, string} <- Desc]], "="),
    {help, Msg} = lists:keyfind(help, 1, Desc),
    io:format("  ~s~n\t\t~s~n", [Flag2, Msg]).

