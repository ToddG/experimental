-module(memoize).
-include_lib("eunit/include/eunit.hrl").
-record(node,   {key=root, value=nil, lc=nil, rc=nil}).
-record(graph,  {root=[], fx, dict=dict:new()}).

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
    [lists:foldl(fun(A,B) -> A*B end, 1, Z) || Z <- [L --[X] || X <- L]].

multm([]) ->
    [];
multm(L) when is_list(L) ->
    %%----------------------------------------------------------
    %% This is a memoized version of mult.
    %%----------------------------------------------------------
    M = memom(L),
    [fetch(K, M) || K <- [L --[X] || X <- L]].

%%====================================================================
%% Internal functions
%%====================================================================

memom(L) ->
    memo(lists:reverse(L), #graph{fx=fun(A,B) -> multiply(A,B) end}).

memo([H|T], G) when is_record(G, graph)->
    N = #node{key=[H], value=H},
    memo(T, add(N, G));
memo([], G) -> G.

add(N, G) when is_record(N, node) andalso 
               is_record(G, graph) ->
    G1 = G#graph{dict=dict:store(N#node.key, N, G#graph.dict)},
    ?debugFmt("~nadded node: ~p, graph: ~p~n", [N, dict:fetch_keys(G1#graph.dict)]),
    case G1#graph.root of
        [] -> G1#graph{root=[N]};
        [Sib|_] -> 
            G2 = G1#graph{root=[N|G1#graph.root]},
            create_child(N, Sib, G2)
    end.

create_child(nil, nil, G) when is_record(G, graph) ->
    G;
create_child(nil, N2, G) when is_record(N2, node) andalso 
                             is_record(G, graph) ->
    G;
create_child(N1, nil, G) when is_record(N1, node) andalso 
                             is_record(G, graph) ->
    G;
create_child(N1, N2, G) when is_record(N1, node) andalso 
                             is_record(N2, node) andalso 
                             is_record(G, graph) ->
    ?debugFmt("~ncreate child n1: ~p, n2: ~p, graph: ~p~n", [N1, N2, dict:fetch_keys(G#graph.dict)]),
    Child = child(N1, N2, G),
    ?debugFmt("~nChild: ~p~n", [Child]),
    D = G#graph.dict,
    D1 = dict:store(Child#node.key, Child, D),
    D2 = dict:update(N1#node.key, fun(Old) -> Old#node{rc=Child#node.key} end, #node{}, D1),
    D3 = dict:update(N2#node.key, fun(Old) -> Old#node{lc = Child#node.key} end, #node{}, D2),
    create_child(N1, N2#node.rc, G#graph{dict=D3}).

child(N1,N2,G) when is_record(N1, node) andalso 
                    is_record(N2, node) andalso 
                    is_record(G, graph) ->
    F = G#graph.fx,
    V1 = N1#node.value,
    V2 = N2#node.value,
    R = F(V1, V2),
    K = N1#node.key ++ N2#node.key,
    #node{key=K, value=R}.

fetch(K, G) when is_record(G, graph) ->
    N = dict:fetch(K, G#graph.dict),
    N#node.value.

multiply(A,B) when is_number(A) andalso is_number(B) -> 
    ?debugFmt("~nA: ~p, B: ~p~n", [A, B]),
    A*B.

%%====================================================================
%% Eunit tests
%%====================================================================

memo_0_test_() ->
    [
     ?_assertEqual(fetch([1], memom([1])), 1),
     ?_assertEqual(fetch([2], memom([2])), 2),
     ?_assertEqual(fetch([3], memom([3])), 3),
     ?_assertEqual(fetch([999], memom([999])), 999)
    ].

memo_1_test_() ->
    M = memom([2,3]),
    [
     ?_assertEqual(fetch([2], M), 2),
     ?_assertEqual(fetch([3], M), 3),
     ?_assertEqual(fetch([2,3], M), 6)
    ].

