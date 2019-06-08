-module(memoize).
-include_lib("eunit/include/eunit.hrl").
-record(node,   {key=root, value=nil, cl=nil, cr=nil}).
-record(graph,  {root=nil, func, dict=dict:new()}).

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
    %% In
    %%----------------------------------------------------------
    %D = level(init(L)),
    %% All pairs have been processed in the level and init
    %% functions above. All that remains is to query the dict
    %% for the results.
    %[dict:fetch(key(K), D) || K <- [L --[X] || X <- L]].
%    G = graph(multiply),
%    [ X || X <- L]
    G = memo(L, multiply),
    [fetch(K, G) || K <- [L --[X] || X <- L]].

%%====================================================================
%% Internal functions
%%====================================================================

%key(A) ->
%    #node{value=A}.
%key(F,A,B) when is_record(node, A) andalso is_record(node, B)->
%    #node{value=F(A#node.value, B#node.value), lhs=A, rhs=B}.

memo(L, F) ->
    memoize(L, graph(F)).
memoize([H|T], G) when is_record(G, graph)->
    N = #node{key=[H], value=H},
    memoize(T, add(N, G));
memoize([], G) -> G.

graph(F) -> #graph{func=F}.

add(N, G) when is_record(N, node) andalso 
               is_record(G, graph) ->
    G1 = G#graph{dict=dict:store(N#node.key, N, G#graph.dict)},
    case G1#graph.root of
        nil -> G1#graph{root=N#node.key};
        Sib -> create_child(N, Sib, G1)
    end.

create_child(nil, N2, G) when is_record(N2, node) andalso 
                             is_record(G, graph) ->
    G;
create_child(N1, nil, G) when is_record(N1, node) andalso 
                             is_record(G, graph) ->
    G;
create_child(N1, N2, G) when is_record(N1, node) andalso 
                             is_record(N2, node) andalso 
                             is_record(G, graph) ->
    Child = child(N1, N2, G),
    D = G#graph.dict,
    D1 = dict:store(Child#node.key, Child, D),
    D2 = dict:update(N1#node.key, fun(Old) -> Old#node{cr=Child#node.key} end, #node{}, D1),
    D3 = dict:update(N2#node.key, fun(Old) -> Old#node{cl = Child#node.key} end, #node{}, D2),
    G1 = create_child(Child, N2#node.cr, G#graph{dict=D3}),
    create_child(Child, N1#node.cl, G1).

child(N1,N2,G) when is_record(N1, node) andalso 
                    is_record(N2, node) andalso 
                    is_record(G, graph) ->
    F = G#graph.func,
    V = F(N1#node.value, N2#node.value),
    K1 = N1#node.key,
    K2 = N2#node.key,
    [H|K1T] = lists:reverse(K1),
    [H|K2T] = lists:reverse(K2),
    K3 = lists:reverse(K1T) ++ lists:reverse(K2T),
    #node{key=K3, value=V}.

fetch(K, G) when is_record(G, graph) ->
    dict:fetch(K, G#graph.dict).

multiply(A,B) -> A*B.

%%====================================================================
%% Eunit tests
%%====================================================================




%init(L) ->
%    %%----------------------------------------------------------
%    %% Returns a list of root level keys and a dictionary
%    %% populated with the root level keys, and that looks like
%    %% this:
%    %%      root keys : [{key, [1]},{key, [2]},...]
%    %%      dict:       {{key, [1]}:1, {key, [2]}:2, ... }
%    %%----------------------------------------------------------
%    Root=[key(X) || X <- L],
%    {Root, dict:from_list(lists:zip(Root, L))}.

%level({R,D}) ->
%    level(R, D).
%
%level(R, D) ->
%    level(R, D, []).
%
%level([_], D, Acc) ->
%    level([], D, Acc);
%level([A,B|T], D, Acc) ->
%    %%----------------------------------------------------------
%    %% Multiplies items (A*B) and pushes K,V into dict store.
%    %% Once we have connsumed all items at a given level, then
%    %% we proceed up to the next level until there are no more
%    %% items in the current level to process.
%    %%
%    %% L1 = [1,2,3,4]
%    %% L2 = [{1,2}, {2,3}, {3,4}]
%    %% L3 = [{1,2,3}, {2,3,4}]
%    %% L4 = [{1,2,3,4}]
%    %% L5 = []
%    %%
%    %% Because the `mult` operation is multiplicative, the order
%    %% doesn't matter, and we can sort the keys to normalize
%    %% lookup in the dictionary.
%    %%----------------------------------------------------------
%    ?debugFmt("~nLevel: ~p~p~p~nDictKeys: ~p, Acc: ~p~n", [A,B,T,dict:fetch_keys(D), Acc]),
%    AVal = dict:fetch(A, D),
%    BVal = dict:fetch(B, D),
%    Res = AVal * BVal,
%    Key = key(A, B),
%    D1 = dict:store(Key, Res, D),
%    ?debugFmt("~nStore Key: ~p, Val: ~p~n", [Key, Res]),
%    level([B|T], D1, [Key|Acc]);
%level([], D, []) -> 
%    %% termination, return the Dict.
%    D;
%level([], D, Acc) ->
%    %% process the next level, as stored in Acc
%    level(Acc, D, []).
%
%%====================================================================
%% Eunit tests
%%====================================================================
%key_test_() ->
%    [
%     ?_assertEqual({key, [[]]},             key([])),
%     ?_assertEqual({key, [1]},              key(1)),
%     ?_assertEqual({key, [1,2,3]},          key([3,2,1])),
%     ?_assertEqual({key, [1, 2]},           key({key, [1]}, {key, [2]})),
%     ?_assertEqual({key, [1,2,3,7,8,9]},    key({key, [1,2,3]}, {key, [9,8,7]}))
%    ].
%
%mult_test_() ->
%    [
%     ?_assertEqual([],      mult([])),
%     ?_assertEqual([1],     mult([1])),
%     ?_assertEqual([2,1],   mult([1,2])),
%     ?_assertEqual([6,3,2], mult([1,2,3]))
%    ].
%
%multm_test_() ->
%    [
%     ?_assertEqual([],      multm([])),
%     ?_assertEqual([1],     multm([1])),
%     ?_assertEqual([2,1],   multm([1,2])),
%     ?_assertEqual([6,3,2], multm([1,2,3]))
%    ].
%
%mult_multm_test_() ->
%    [
%    ?_assert(multm([]) =:= mult([])),
%    ?_assert(multm([1]) =:= mult([1])),
%    ?_assert(multm([1,2]) =:= mult([1,2])),
%    ?_assert(multm([1,2,3]) =:= mult([1,2,3]))
%    ].

%init_empty_test_() ->
%    {R, D} = init([]),
%    [
%    ?_assertEqual(length(R), 0),
%    ?_assertEqual(length(dict:fetch_keys(D)), 0)
%    ].
%
%init_one_test_() ->
%    {R, D} = init([1]),
%    [
%    ?_assertEqual(length(R), 1),
%    ?_assertEqual(length(dict:fetch_keys(D)), 1),
%    ?_assertEqual(R, [[1]]),
%    ?_assertEqual(dict:fetch([1], D), 1)
%    ].
%
%init_two_test_() ->
%    {R, D} = init([1,2]),
%    [
%    ?_assertEqual(length(R), 2),
%    ?_assertEqual(length(dict:fetch_keys(D)), 2),
%    ?_assertEqual(dict:fetch([1], D), 1),
%    ?_assertEqual(dict:fetch([2], D), 2)
%    ].
%
%level_termination_test() ->
%    D = dict:from_list([{1,1}]),
%    D1 = level([], D, []),
%    ?_assertEqual(dict:to_list(D), dict:to_list(D1)).
%
%level_0_test_() ->
%    L = [1,2,3,4],
%    {R,D} = init(L),
%    [
%    ?_assertEqual([[1],[2],[3],[4]], lists:sort(R)),
%    [?_assert(dict:is_key([X], D)) || X <- L]
%    ].
%
%level_1_test_() ->
%    L = [1,2,3,4],
%    R = [[1],[2],[3],[4]],
%    D = dict:from_list([{[1],1}, {[2],2}, {[3],3}, {[4],4}]), 
%    D1 = level(R, D),
%    ?debugVal(D1),
%    ?debugVal(dict:fetch_keys(D1)),
%    [
%    ?_assertEqual(dict:fetch([1], D1), 1),
%    ?_assertEqual(dict:fetch([2], D1), 2),
%    ?_assertEqual(dict:fetch([3], D1), 3),
%    ?_assertEqual(dict:fetch([4], D1), 4),
%    ?_assertEqual(dict:fetch([1,2], D1), 2),
%    ?_assertEqual(dict:fetch([1,2,3], D1), 6),
%    ?_assertEqual(dict:fetch([2,3], D1), 6),
%    ?_assertEqual(dict:fetch([2,3,4], D1), 24),
%    ?_assert(not dict:is_key([1,2,3,4]))
%    ].
