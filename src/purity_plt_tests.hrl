
-include_lib("eunit/include/eunit.hrl").

%-spec reachlist([{any(),any()}]|dict()) -> [{any(),any()}].
reachlist(M) when is_list(M) ->
    reachlist(dict:from_list(M));
reachlist(M) -> % assume dict...
    lists:sort(dict:to_list(dict_map(fun sort/1, reachable(M)))).

sort(S) ->
    lists:sort(sets:to_list(S)).


reachable_test_() ->
    [?_assertMatch([ {a, [a,b,c,d]}, {b, [a,b,c,d]} ],
            reachlist([ {a, [b,c]}, {b, [d,a]} ]))
    ,?_assertMatch([ {a, [b,c,d]}, {b, [c,d]}, {c, [d]} ],
            reachlist([ {a, [b]}, {b, [c]}, {c, [d]} ]))
    ].

