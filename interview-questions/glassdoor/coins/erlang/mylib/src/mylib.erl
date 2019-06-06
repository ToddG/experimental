-module(mylib).
-include_lib("eunit/include/eunit.hrl").

%% API exports
-export([main/1, repeat/2, divisible_table/2, partition_table/1]).

%%====================================================================
%% API functions
%%====================================================================

%% escript Entry point
main(Args) ->
    io:format("Args: ~p~n", [Args]),
    erlang:halt(0).

partition_table(T) ->
    {Heads, Tails} = lists:partition(fun(A) -> A =:= heads end, T),
    LenHeads = length(Heads),
    LenTails = length(Tails),
    HalfLenHeads = trunc(LenHeads / 2),
    HalfLenTails = trunc(LenTails / 2),
    H1 = lists:sublist(Heads, HalfLenHeads),
    H2 = lists:sublist(Heads, HalfLenHeads + 1, LenHeads),
    T1 = lists:sublist(Tails, HalfLenTails),
    T2 = lists:sublist(Tails, HalfLenTails + 1, LenTails),
    {H1 ++ T1, H2 ++ T2}.

%%====================================================================
%% Internal functions
%%====================================================================
random_table(NumHeads, NumTails) when NumHeads >= 0, 
				      NumTails >= 0 ->
    Heads = repeat(heads, NumHeads),
    Tails = repeat(tails, NumTails),
    L = Heads ++ Tails,
    [X || {_,X} <- lists:sort([{rand:uniform(), N} || N <- L])].

divisible_table(NumHeads, NumTails) when NumHeads >= 0, 
					 NumTails >= 0, 
					 NumHeads rem 2 == 0, 
					 NumTails rem 2 == 0 -> 
    random_table(NumHeads, NumTails).


repeat(Value, Length) when is_integer(Length), Length > 0 ->
    [Value || _ <- lists:seq(1, Length)];
repeat(_, _) ->
    [].

%%====================================================================
%% Eunit tests
%%====================================================================

partition_table_test() ->
    ?_assert(partition_table(divisible_table(2,2)) =:= [[heads,tails], [heads,tails]]).

random_table_test() ->
    ?_assert(random_table(0,0) =:= []),
    ?_assert(random_table(0,1) =:= [tails]),
    ?_assert(random_table(1,0) =:= [heads]),
    ?_assert(lists:member(random_table(1,1), [[heads,tails], [tails,heads]])).

repeat_test() ->
    ?_assert(repeat(0,0) =:= []),
    ?_assert(repeat(0,1) =:= [0]),
    ?_assert(repeat(0,2) =:= [0,0]),
    ?_assert(repeat(0,-1) =:= []),
    ?_assert(repeat(true,0) =:= []),
    ?_assert(repeat(true,1) =:= [true]),
    ?_assert(repeat(true,2) =:= [true, true]),
    ?_assert(repeat(true,-1) =:= []).
