
-include_lib("eunit/include/eunit.hrl").

opts_cmp_test_() ->
    [?_assert(opts_cmp({key, 1}, {key, 1}))
    ,?_assert(opts_cmp({key, 1}, {key, 2}))
    ,?_assert(opts_cmp({k1, 1}, {k2, 2}))
    ,?_assertNot(opts_cmp({k3, 3}, {k2, 3}))
    ,?_assertNot(opts_cmp(b, a))
    ,?_assertMatch([b,{a,1}], lists:usort(fun opts_cmp/2, [{a,1},b,{a,3}]))
    ].

matching_opt_test_() ->
    [?_assert(matching_opt(key, key))
    ,?_assert(matching_opt(key, {key, val}))
    ,?_assertNot(matching_opt(key, val))
    ,?_assertNot(matching_opt(key, {val, key}))
    ].

override_test_() ->
    [?_assertMatch([b,a], override(a, c, [c,b,c,a]))
    ,?_assertMatch([c,b,c], override(a, c, [c,b,c]))
    ,?_assertMatch([a,b], override(a, c, [a,{c,1},b,{c,2},c]))
    ,?_assertMatch([a,b,c,c], override(a, d, [a,b,c,c]))
    ,?_assertMatch([b,{a,1}], override(a, c, [b,{a,1},{c,2}]))
    ].

postprocess_test_() ->
    [?_assertMatch([b,a], postprocess({override, [{a,c},{b,d}]}, [c,b,{d,42},a]))
    ,?_assertMatch([b,{a,3}], postprocess(only_keep_last, [{a,1},b,{a,3}]))
    %% Postprocessing order should not be important for these operations:
    ,?_assertMatch([q,t,{c,2}], postprocess(only_keep_last,
            postprocess({override, [{t,p}, {t,b}]},
                [{c,1},{p,1},q,t,{p,2},{c,2}])))
    ,?_assertMatch([q,t,{c,2}], postprocess({override, [{t,p}, {t,b}]},
            postprocess(only_keep_last,
                [{c,1},{p,1},q,t,{p,2},{c,2}])))
    ].

