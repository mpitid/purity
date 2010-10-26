
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

%%% Variable Subsets
all_subsets_test_() ->
    [?_assert(all_subsets([[{sub,1}], [{sub,1}], [{sub,1},{arg,2},{arg,3}]]))
    ,?_assertNot(all_subsets([[{sub,1}], [], [{sub,2}]]))
    ,?_assertNot(all_subsets([]))
].

no_high_callsite_test_() ->
    [?_assert(no_high_callsite([[{sub,1}], [{sub,1},{arg,2},{arg,3}]]))
    ,?_assertNot(no_high_callsite([[], [{1,{r,g,1}}]]))
].

without_subset_recursion_test_() ->
    [?_assertMatch([],
        without_subset_recursion(f, [{l,f,[{sub,1}]}, {r,f,[{arg,{1,2}},{arg,3},{sub,1}]}]))
    ,?_assertMatch([{l,f,[]}],
        without_subset_recursion(f, [{l,f,[{sub,1}]}, {l,f,[]}, {l,f,[{sub,2}]}]))
    %% Not self-recursion, only clear subsets (not currently possible but still).
    ,?_assertMatch([{arg,2},{r,g,[]},{r,g,[{1,{r,a,1}}]}], %% Should be sorted!
        without_subset_recursion(f, [{arg,2}, {r,g,[{sub,1},{1,{r,a,1}}]}, {r,g,[{sub,1}]}]))
    %% high_callsite, so no removal.
    ,?_assertMatch([{r,f,[{1,{r,g,2}}]}],
        without_subset_recursion(f, [{r,f,[{1,{r,g,2}},{sub,1}]}]))
    ,?_assertMatch(v, without_subset_recursion(f, v))
].

clear_sub_test_() ->
    [?_assertMatch([], clear_sub([]))
    ,?_assertMatch([{r,f,[]}], clear_sub([{r,f,[{sub,1},{sub,2}]}]))
    ,?_assertMatch([{r,f,[]},{arg,1}], clear_sub([{r,f,[{sub,1},{sub,2}]},{arg,1}]))
    ,?_assertMatch([{arg,1},{arg,2}], clear_sub([{arg,1},{arg,2}]))
    ,?_assertMatch([{r,f,[{arg,1},{arg,1,2}]}],
        clear_sub([{r,f,[{arg,1},{sub,1},{arg,1,2}]}]))
].
