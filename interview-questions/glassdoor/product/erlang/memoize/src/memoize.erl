-module(memoize).
-include_lib("eunit/include/eunit.hrl").


%% API exports
-export([main/1, mult/1, multm/1]).

%%====================================================================
%% API functions
%%====================================================================

%% escript Entry point
main(Args) ->
    io:format("Args: ~p~n", [Args]),
    erlang:halt(0).

mult(L) ->
    %%----------------------------------------------------------
    %% Given an array of numbers, replace each number with the 
    %% product of all the numbers in the array except the number 
    %% itself *without* using division.
    %%
    %% This solution is elegant, but suffers from the fact that
    %% it re-calculates the entire graph - 1 elements for each
    %% element in the list.
    %%----------------------------------------------------------
    [lists:foldl(fun(A,B) -> A*B end,1, Z) || Z <- [L --[X] || X <- L]].

multm(L) ->
    %%----------------------------------------------------------
    %% This is a memoized version of mult.
    %% In
    %%----------------------------------------------------------
    D = level(init(L)),
    %% All pairs have been processed in the level and init
    %% functions above. All that remains is to query the dict
    %% for the results.
    [dict:fetch(lists:sort(K), D) || K <- [L --[X] || X <- L]].



%%====================================================================
%% Internal functions
%%====================================================================
init(L) ->
    %%----------------------------------------------------------
    %% Returns a list of root level keys and a dictionary
    %% populated with the root level keys, and that looks like
    %% this:
    %%      root keys : [[1],[2],...]
    %%      dict:       {[1]:1, [2]:2, [3]:3 ... }
    %%----------------------------------------------------------
    Root=[[X] || X <- L],
    {Root, dict:from_list(lists:zip(Root, L))}.

level({R,D}) ->
    level(R, D).

level(R, D) ->
    level(R, D, []).

level([_], D, Acc) ->
    %% not storing the top level item, forward on to the termination
    level([], D, Acc);
level([A,B|T], D, Acc) ->
    %%----------------------------------------------------------
    %% Multiplies items (A*B) and pushes K,V into dict store.
    %% Once we have connsumed all items at a given level, then
    %% we proceed up to the next level until there are no more
    %% items in the current level to process.
    %%
    %% L1 = [1,2,3,4]
    %% L2 = [{1,2}, {2,3}, {3,4}]
    %% L3 = [{1,2,3}, {2,3,4}]
    %% L4 = [{1,2,3,4}]
    %% L5 = []
    %%
    %% Because the `mult` operation is multiplicative, the order
    %% doesn't matter, and we can sort the keys to normalize
    %% lookup in the dictionary.
    %%----------------------------------------------------------
    AVal = dict:fetch(A, D),
    BVal = dict:fetch(B, D),
    Res = AVal * BVal,
    Key = lists:sort(A ++ B),
    D1 = dict:store(Key, Res, D),
    level(T, D1, [Key|Acc]);
level([], D, []) -> 
    %% termination, return the Dict.
    D;
level([], D, Acc) ->
    %% process the next level, as stored in Acc
    level(Acc, D, []).

%%====================================================================
%% Eunit tests
%%====================================================================

init_empty_test() ->
    {R, D} = init([]),
    ?_assert(length(R) =:= 0),
    ?_assert(length(dict:fetch_keys(D)) =:= 0).

init_one_test() ->
    {R, D} = init([1]),
    ?_assert(length(R) =:= 1),
    ?_assert(length(dict:fetch_keys(D)) =:= 1),
    ?_assert(R =:= [[1]]),
    ?_assert(dict:fetch([1], D) =:= 1).

init_two_test() ->
    {R, D} = init([1,2]),
    ?_assert(length(R) =:= 2),
    ?_assert(length(dict:fetch_keys(D)) =:= 2),
    ?_assert(dict:fetch([1], D) =:= 1),
    ?_assert(dict:fetch([2], D) =:= 2).

level_termination_test() ->
    D = dict:from_list([{1,1}]),
    D1 = level([], D, []),
    ?_assert(dict:to_list(D) =:= dict:to_list(D1)).

level_0_test() ->
    L = [1,2,3,4],
    {R,D} = init(L),
    ?_assert([[1],[2],[3],[4]] =:= lists:sort(R)),
    [?_assert(dict:is_key([X], D)) || X <- L].

level_1_test() ->
    L = [1,2,3,4],
    R = [[1],[2],[3],[4]],
    D = dict:from_list([{[1],1}, {[2],2}, {[3],3}, {[4],4}]), 
    D1 = level(R, D),
    %% assert prev keys are present
    [?_assert(dict:is_key([X], D1)) || X <- L],
    Keys = [lists:sort(Z) || Z <- [L -- [X] || X <- L]],
    %% assert that new keys are present
    [?_assert(dict:is_key(K, D1)) || K <- Keys].
