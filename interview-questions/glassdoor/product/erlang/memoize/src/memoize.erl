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

memo([H|T], G) when is_record(G, graph) andalso is_number(H) ->
    dump_graph(G),
    N = #node{key=[H], value=H},
    G1 = add(N, G),
    dump_graph(G1),
    memo(T, G1);
memo([], G) -> G.

add(N, G) when is_record(N, node) andalso 
               is_record(G, graph) ->
    D0 = G#graph.dict,
    D1 = dict:store(N#node.key, N, D0),
    G1 = G#graph{dict=D1},
    ?debugFmt("~nadded node: ~p~n",[N]),
    %dump_graph(G1),
    case G1#graph.root of
        [Sib|_] ->
            G2 = create_child(N, Sib, G1),
            G2#graph{root=[N|G2#graph.root]};
        [] -> 
            G1#graph{root=[N|G1#graph.root]}
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
    ?debugFmt("~ncreate child n1: ~p, n2: ~p~n", [N1, N2]),
    %dump_graph(G),
    Child = child(N1, N2, G),
    ?debugFmt("~nChild: ~p~n", [Child]),
    D = G#graph.dict,
    D1 = dict:store(Child#node.key, Child, D),
    D2 = dict:update(N1#node.key, fun(Old) -> Old#node{rc=Child#node.key} end, #node{}, D1),
    D3 = dict:update(N2#node.key, fun(Old) -> Old#node{lc = Child#node.key} end, #node{}, D2),
    G1 = G#graph{dict=D3},
    ?debugFmt("~nadded child: ~p~n", [Child]),
    %dump_graph(G1),
    case N2#node.rc of
        nil -> 
            G1;
        NextSibKey ->
            NextSib = dict:fetch(NextSibKey, G1#graph.dict),
            create_child(N1, NextSib, G1)
    end.


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
    ?debugFmt("~nmultiply ~w * ~w ~n", [A, B]),
    A*B.

dump_graph(G) when is_record(G, graph) ->
    ?debugFmt("~nGraph START--------------------------------~n\troot: ~p~n\tfx: ~p~n\tdict: ~n~w~nGraph END----------------------------------", [G#graph.root, G#graph.fx, dict:to_list(G#graph.dict)]).

%%====================================================================
%% Eunit tests
%%====================================================================

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

%memom_3_test_() ->
%    M = memom([8,9,2]),
%    [
%     ?_assertEqual(fetch([8], M), 8),
%     ?_assertEqual(fetch([9], M), 9),
%     ?_assertEqual(fetch([2], M), 2),
%     ?_assertEqual(fetch([8,9], M), 8*9),
%     ?_assertEqual(fetch([9,2], M), 9*2),
%     ?_assertEqual(fetch([8,9,2], M), 8*9*2)
%    ].
%%
%
%memo_2_test_() ->
%    M = memom([2,3,1,0,100,9]),
%    [
%     ?_assertEqual(fetch([2], M), 2),
%     ?_assertEqual(fetch([3], M), 3),
%     ?_assertEqual(fetch([2,3], M), 6),
%     ?_assertEqual(fetch([2,3,1,0], M), 0),
%     ?_assertEqual(fetch([2,3,1], M), 6),
%     ?_assertEqual(fetch([100,9], M), 900)
%    ].
