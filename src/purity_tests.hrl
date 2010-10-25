
-include_lib("eunit/include/eunit.hrl").

find_matching_args_test_() ->
    [?_assertMatch(none, find_matching_args([{arg,1}], [{2,hit}]))
    ,?_assertMatch({all, [hit]}, find_matching_args([{arg,1}], [{1,hit}]))
    ,?_assertMatch({some, [hit]}, find_matching_args([{arg,1},{arg,2}], [{2,hit}]))
    %% Should not stop when encountering uninteresting DepArg values.
    ,?_assertMatch({all, [a,c]}, find_matching_args([{arg,1},{arg,3}], [{1,a},b,{3,c}]))
    ,?_assertMatch({all, [a,c]}, find_matching_args([{arg,1},{arg,3}], [{1,a},{2,b},{3,c}]))
    %% Arguments should be sorted, so this just checks the robustness
    %% of the new implementation.
    ,?_assertMatch({all, _}, find_matching_args([{arg,3},{arg,1}], [{1,a},{3,b}]))
    ].


pick_only_concrete_test_() ->
    [?_assertMatch(pure, pick_only_concrete([{ok,true},{ok,[]},{ok,true}]))
    ,?_assertMatch(impure, pick_only_concrete([{ok,true},{ok,[]},{ok,false}]))
    ,?_assertMatch(impure, pick_only_concrete([{ok,[]},{ok,{false,"impure"}}]))
    ,?_assertMatch(other, pick_only_concrete([{ok,true},error,{ok,true}]))
    ,?_assertMatch(other, pick_only_concrete([{ok,[not_empty]}]))
].

