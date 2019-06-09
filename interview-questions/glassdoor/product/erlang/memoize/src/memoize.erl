-module(memoize).
-include_lib("eunit/include/eunit.hrl").
-record(node,   {key=root, value=nil, lc=nil, rc=nil}).
-record(graph,  {root=[nil], fx, dict=dict:new()}).

%% API exports
-export([main/1, mult/1, multm/1]).

%%====================================================================
%% API functions
%%====================================================================

%% escript Entry point
main(Args) ->
    io:format("Args: ~p~n", [Args]),
    erlang:halt(0).

mult([]) ->
    [];
mult(L) when is_list(L) ->
    %%----------------------------------------------------------
    %% Given an array of numbers, replace each number with the 
    %% product of all the numbers in the array except the number 
    %% itself *without* using division.
    %%
    %% This solution is elegant, but suffers from the fact that
    %% it re-calculates the entire graph - 1 elements for each
    %% element in the list.
    %%----------------------------------------------------------
    [lists:foldl(fun(A,B) -> multiply(A, B) end, 1, Z) || Z <- replacements(L)].

multm([]) ->
    [];
multm(L) when is_list(L) andalso length(L) > 0->
    %%----------------------------------------------------------
    %% This is a memoized version of mult.
    %%----------------------------------------------------------
    M = memom(L),
    [fetch(K, M) || K <- replacements(L)].

replacements(L) ->
    lists:filter(fun(A) -> length(A) > 0 end, [L -- [X] || X <- L]).

%%====================================================================
%% Internal functions
%%====================================================================

memom(L) ->
    memo(lists:reverse(L), #graph{fx=fun(A,B) -> multiply(A,B) end}).

memo([H|T], G) when is_record(G, graph) andalso is_number(H) ->
    N = #node{key=[H], value=H},
    G1 = add_root(N, G),
    dump_graph(G1),
    memo(T, G1);
memo([], G) -> G.

add_root(N, G) when is_record(N, node) andalso is_record(G, graph) ->
    G1 = G#graph{dict=dict:store(N#node.key, N, G#graph.dict)},
    [H|_] = G#graph.root,
    G2 = add_child_by_key(N#node.key, H, G1),
    G2#graph{root=[N#node.key|G#graph.root]}.

add_child_by_key(_, nil, G) ->
    G;
add_child_by_key(K1, K2, G) ->
    dump_graph(G),
    LHS = dict:fetch(K1, G#graph.dict),
    RHS = dict:fetch(K2, G#graph.dict),
    add_child(LHS, RHS, G).

add_child(N1, nil, G) when is_record(N1, node) andalso is_record(G, graph) -> G;
add_child(nil, N2, G) when is_record(N2, node) andalso is_record(G, graph) -> G;
add_child(nil, nil, G) when is_record(G, graph) -> G;
add_child(N1, N2, G) when is_record(N1, node) andalso is_record(N2, node) andalso is_record(G, graph) ->
    Child = child(N1, N2, G),
    D = G#graph.dict,
    D1 = dict:store(Child#node.key, Child, D),
    D2 = dict:update(N1#node.key, fun(Old) -> Old#node{rc=Child#node.key} end, D1),
    D3 = dict:update(N2#node.key, fun(Old) -> Old#node{lc = Child#node.key} end, D2),
    G1 = G#graph{dict=D3},
    add_child_by_key(Child#node.key, N2#node.rc, G1).

child(N1,N2,G) when is_record(N1, node) andalso 
                    is_record(N2, node) andalso 
                    is_record(G, graph) ->
    F = G#graph.fx,
    [RootKey|_] = N1#node.key,
    RootNode = dict:fetch([RootKey], G#graph.dict),
    V1 = RootNode#node.value,
    V2 = N2#node.value,
    R = F(V1, V2),
    K = RootNode#node.key ++ N2#node.key,
    #node{key=K, value=R}.

fetch(K, G) when is_record(G, graph) ->
    case dict:is_key(K,G#graph.dict) of
        true -> 
            N = dict:fetch(K, G#graph.dict),
            N#node.value;
        false ->
            L = length(K),
            HL = L div 2,
            {K1, K2} = lists:split(HL, K),
            F = G#graph.fx,
            F(fetch(K1, G), fetch(K2, G))
    end.

multiply(A,B) when is_number(A) andalso is_number(B) -> 
    %% TODO: put counters in here for metrics
    A*B.


dump_graph(G) when is_record(G, graph) ->
%    Start = "~nGraph START--------------------------------~n",
%    Middle = "root: ~w~nfx: ~p~ndict:~n",
%    End = "~nGraph END----------------------------------~n",
%    D = format_dict(G#graph.dict),
%    ?debugFmt(Start ++ Middle ++ D ++ End, [G#graph.root, G#graph.fx ]).
    ok.

%format_dict(D) ->
%    string:join([lists:flatten(io_lib:format("key: ~w, value: ~w", [Key, Value])) || {Key,Value} <- dict:to_list(D)], "\n").


%%====================================================================
%% Eunit tests
%%====================================================================

mult_1_test_() ->
    [
     ?_assertEqual(mult([]), []),
     ?_assertEqual(mult([1]), []),
     ?_assertEqual(mult([1,2]), [2,1]),
     ?_assertEqual(mult([1,2,3]), [6,3,2]),
     ?_assertEqual(mult([4,99,20,6]), [99*20*6, 4*20*6, 4*99*6, 4*99*20])
    ].

multm_1_test_() ->
    [
     ?_assertEqual(multm([]), []),
     ?_assertEqual(multm([1]), []),
     ?_assertEqual(multm([1,2]), [2,1]),
     ?_assertEqual(multm([1,2,3]), [6,3,2]),
     ?_assertEqual(multm([4,99,20,6]), [99*20*6, 4*20*6, 4*99*6, 4*99*20])
    ].

memom_1_test_() ->
    [
     ?_assertEqual(fetch([1], memom([1])), 1),
     ?_assertEqual(fetch([2], memom([2])), 2),
     ?_assertEqual(fetch([3], memom([3])), 3),
     ?_assertEqual(fetch([999], memom([999])), 999)
    ].

memom_2_test_() ->
    M = memom([2,3]),
    [
     ?_assertEqual(fetch([2], M), 2),
     ?_assertEqual(fetch([3], M), 3),
     ?_assertEqual(fetch([2,3], M), 6)
    ].

memom_3_test_() ->
    M = memom([8,9,2]),
    [
     ?_assertEqual(fetch([8], M), 8),
     ?_assertEqual(fetch([9], M), 9),
     ?_assertEqual(fetch([2], M), 2),
     ?_assertEqual(fetch([8,9], M), 8*9),
     ?_assertEqual(fetch([9,2], M), 9*2),
     ?_assertEqual(fetch([8,9,2], M), 8*9*2)
    ].


memom_4_test_() ->
    M = memom([8,9,2,100]),
    [
     ?_assertEqual(fetch([8], M), 8),
     ?_assertEqual(fetch([9], M), 9),
     ?_assertEqual(fetch([2], M), 2),
     ?_assertEqual(fetch([8,9], M), 8*9),
     ?_assertEqual(fetch([9,2], M), 9*2),
     ?_assertEqual(fetch([2,100], M), 2*100),
     ?_assertEqual(fetch([8,9,2], M), 8*9*2),
     ?_assertEqual(fetch([9,2,100], M), 9*2*100)
    ].
