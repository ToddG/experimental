-module(prop_matrix).
-include_lib("proper/include/proper.hrl").

%%%%%%%%%%%%%%%%%%
%%% Properties %%%
%%%%%%%%%%%%%%%%%%
prop_test() ->
    ?FORALL(KV, stuff(),
        begin
            {R1,R2,C1,C2,L} = KV,
            [RowStart, RowEnd] = lists:sort([R1,R2]),
            [ColStart, ColEnd] = lists:sort([C1,C2]),
            D = dict:from_list(L),
            matrix:sum(RowStart, RowEnd, ColStart, ColEnd, D) =:= model_sum(RowStart, RowEnd, ColStart, ColEnd, D)
        end).

%%%%%%%%%%%%%%%
%%% Helpers %%%
%%%%%%%%%%%%%%%
model_sum(RowStart, RowEnd, ColStart, ColEnd, D) ->
    PotentialKeys = [ {R, C} || R <- lists:seq(RowStart, RowEnd), C <- lists:seq(ColStart, ColEnd) ],
    ValidKeys = lists:filter(fun(X) -> dict:is_key(X, D) end, PotentialKeys),
    lists:sum([dict:fetch(K, D) || K <- ValidKeys]).


%%%%%%%%%%%%%%%%%%
%%% Generators %%%
%%%%%%%%%%%%%%%%%%
stuff() -> {pos_integer(), pos_integer(), pos_integer(), pos_integer(), list({key(), val()})}.
key() -> {pos_integer(), pos_integer()}.
val() -> integer().
