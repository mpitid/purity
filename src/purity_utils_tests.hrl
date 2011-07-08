
-include_lib("eunit/include/eunit.hrl").

dl(D) ->
    lists:sort(dict:to_list(D)).

ld(L) ->
    dict:from_list(make_mfas(L)).

make_mfas(L) ->
    [{mock_mfa(M), mock_deps(Ds)} || {M, Ds} <- L].

mock_mfa(M) -> {M,f,1}.

mock_deps(Ds) -> {p, [{remote, mock_mfa(D), []} || D <- Ds]}.

module_rmap_test_() ->
    [?_assertMatch([ {a, [b, c]}, {b, [a]}, {c, [a]}, {d, [b]}, {e, [b]} ],
            dl(module_rmap(ld( [ {a, [b,c]}, {b, [a, d, e]}, {c, [a]} ] ))))
    ].

