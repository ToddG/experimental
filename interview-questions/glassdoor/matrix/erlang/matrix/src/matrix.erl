-module(matrix).
-include_lib("eunit/include/eunit.hrl").

%% API exports
-export([main/1, sum/5, matrix_list/3]).

%%====================================================================
%% API functions
%%====================================================================

%% escript Entry point
main(Args) ->
    io:format("Args: ~p~n", [Args]),
    erlang:halt(0).

%%====================================================================
%% Internal functions
%%====================================================================

sum(RowStart, RowEnd, ColStart, ColEnd, M) ->
    dict:fold(fun(_,V,Acc) -> Acc + V end, 0, dict:filter(fun({R,C},_) ->   R >= RowStart   andalso 
                                                                            R =< RowEnd     andalso
                                                                            C >= ColStart   andalso
                                                                            C =< ColEnd     end, 
                                                                            M
                                                                            )
             ).

sum_1x1_test() ->
    L = matrix_list(1, 1, 1),
    D = dict:from_list(L),
    ?_assert(sum(1,1,1,1,D) =:= 1).

sum_2x2_test() ->
    L = matrix_list(2, 2, 1),
    D = dict:from_list(L),
    ?_assert(sum(1,1,1,1, D) =:= 1),
    ?_assert(sum(1,2,1,2, D) =:= 4).

sum_4x4_test() ->
    L = matrix_list(2, 2, 1),
    D = dict:from_list(L),
    ?_assert(sum(1,1,1,1, D) =:= 1),
    ?_assert(sum(1,2,1,2, D) =:= 4),
    ?_assert(sum(1,4,1,4, D) =:= 16).

matrix_list(Rows, Cols, Val) ->
    [{{R,C},Val} || R <- lists:seq(1,Rows), C <- lists:seq(1,Cols)].
