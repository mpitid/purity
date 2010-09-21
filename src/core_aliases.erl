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
%%% @doc Locate aliases to variables in core erlang expressions.
%%%

-module(core_aliases).

-export([scan/1]).

-type name() :: cerl:var_name().

%% @doc Scan a core erlang function and return a mapping of alias names to
%% the corresponding variables names.
%%
%% We are only interested in the reverse mapping of variable aliases,
%% which should also be unique, so the expression
%% `case <cor1, cor2> of
%%   <Pred, List> -> ...
%%   <Pred, cor3> -> ...
%%   <cor1, cor2> when true -> match_fail'
%% will produce a mapping of `{Pred, cor1}', `{List, cor2}' and `{cor3, cor2}'.

-spec scan(cerl:c_fun()) -> dict().

scan(Fun) ->
    true = cerl:is_c_fun(Fun),
    Map = cerl_trees:fold(fun collect_aliases/2, [], cerl:fun_body(Fun)),
    reverse_map(lists:flatten(Map)).


%% @doc Collect viariable aliases from case expressions.
%%
%% XXX: Relies on current implementation of the core erlang generator,
%% where each function has unique variable names.

-spec collect_aliases(cerl:cerl(), [{name(), name()}]) -> [{name(), name()}].

collect_aliases(Tree, VarMap) ->
    case cerl:type(Tree) of
        'case' ->
            %% We are only interested in arguments that are variables,
            %% lists, or tuples.
            %% TODO: Binaries could be supported as well.
            Arg = cerl:case_arg(Tree),
            Clauses = cerl:case_clauses(Tree),
            New = case cerl:type(Arg) of
                var ->
                    {ok, Name} = var_name(Arg),
                    threefold(fun get_var_aliases/3, Name, Clauses);
                values ->
                    Nodes = cerl:values_es(Arg),
                    threefold(fun get_tuple_aliases/3, Nodes, Clauses);
                cons ->
                    Values = flatten_cons(Arg),
                    threefold(fun get_list_aliases/3, Values, Clauses);
                _ ->
                    []
            end,
            [New | VarMap];
        _ ->
            VarMap
    end.


%% @doc Return a reverse mapping of the associative list KeyVals.
%% Any elements which have multiple associations, are omitted.

-spec reverse_map([{name(), name()}]) -> dict().

reverse_map(KeyVals) ->
    Acc = {dict:new(), []},
    {Dict, ToPurge} = lists:foldl(fun add_rev_unique/2, Acc, KeyVals),
    lists:foldl(fun(K, D) -> dict:erase(K, D) end, Dict, ToPurge).


-spec add_rev_unique({name(), name()}, {dict(), [name()]}) -> {dict(), [name()]}.

add_rev_unique({Key, Key}, Acc) ->
    Acc;
add_rev_unique({Value, Key}, {Dict, ToPurge} = Acc) ->
    case dict:find(Key, Dict) of
        {ok, Value} ->
            Acc;
        {ok, _} ->
            %% Same name aliased to different variable across clauses.
            %% Can't handle it in a meaningful way, so schedule it for
            %% removal.
            {Dict, [Key|ToPurge]};
        error ->
            {dict:store(Key, Value, Dict), ToPurge}
    end.


threefold(Fun, Extra, List) ->
    lists:foldl(fun(Elem, Acc) -> Fun(Extra, Elem, Acc) end, [], List).


get_var_aliases(Name1, Clause, Map) ->
    case cerl:clause_pats(Clause) of
        [Pattern] ->
            case var_name(Pattern) of
                {ok, Name2} ->
                    [{Name1, Name2} | Map];
                _ ->
                    Map
            end;
        _ ->
            Map
    end.


get_tuple_aliases(Values, Clause, Map) ->
    Patterns = cerl:clause_pats(Clause),
    [all_or_nothing(Values, Patterns) | Map].


get_list_aliases(Values, Clause, Map) ->
    [Pattern] = cerl:clause_pats(Clause),
    [all_or_nothing(Values, flatten_cons(Pattern)) | Map].


%% @doc Return any subtrees in a cons tree as a flat list. Works
%% for improper lists as well.
flatten_cons(Node) ->
    case cerl:type(Node) of
        cons ->
            [cerl:cons_hd(Node) | flatten_cons(cerl:cons_tl(Node))];
        _ ->
            [Node]
    end.


%% @doc Map names in `L1' to names in `L2', only if all elements
%% of both lists represent variables or aliases.

-spec all_or_nothing([cerl:cerl()], [cerl:cerl()]) -> [{name(), name()}].

all_or_nothing(L1, L2) ->
    all_or_nothing(L1, L2, []).

all_or_nothing([V1|T1], [V2|T2], Acc0) ->
    Acc1 = case {var_name(V1), var_name(V2)} of
        %% Only return variable/aliases, literals etc are not interesting.
        {{ok, N1}, {ok, N2}} ->
            [{N1, N2} | Acc0];
        _ ->
            Acc0
    end,
    all_or_nothing(T1, T2, Acc1);
all_or_nothing([], [], Acc) ->
    Acc;
%% Lists lengths don't match, ignore anything found so far, and return nothing.
all_or_nothing(_, _, _) ->
    [].


%% @doc Return the name of a term if it represents a variable or alias.

-spec var_name(cerl:cerl()) -> error | {ok, cerl:var_name()}.

var_name(Tree) ->
    case cerl:type(Tree) of
        var ->
            {ok, cerl:var_name(Tree)};
        alias ->
            {ok, cerl:var_name(cerl:alias_var(Tree))};
        _ ->
            error
    end.

