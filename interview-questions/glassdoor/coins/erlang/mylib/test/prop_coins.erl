-module(prop_coins).
-include_lib("proper/include/proper.hrl").

%%%%%%%%%%%%%%%%%%
%%% Properties %%%
%%%%%%%%%%%%%%%%%%
prop_test() ->
    ?FORALL(Type, term(),
        begin
            boolean(Type)
        end).

prop_repeat_test() ->
    ?FORALL(Type, {non_neg_integer(), non_neg_integer()},
    begin
	{Value, Length} = Type,
	Repeated = mylib:repeat(Value, Length),
	length(Repeated) =:= Length
	andalso
	lists:all(fun(N) -> N =:= Value end, Repeated)
    end).

prop_partition_table_test() ->
    ?FORALL(Type, {non_neg_integer(), non_neg_integer()},
    begin
	{NumHeads, NumTails} = Type,
        Table = mylib:divisible_table(NumHeads*2, NumTails*2),
        {T1, T2} = mylib:partition_table(Table),
        length([X || X <- T1, X =:= heads]) =:= NumHeads andalso
        length([X || X <- T1, X =:= tails]) =:= NumTails andalso
        length([X || X <- T2, X =:= heads]) =:= NumHeads andalso
        length([X || X <- T2, X =:= tails]) =:= NumTails
    end).

%%%%%%%%%%%%%%%
%%% Helpers %%%
%%%%%%%%%%%%%%%
boolean(_) -> true.

%%%%%%%%%%%%%%%%%%
%%% Generators %%%
%%%%%%%%%%%%%%%%%%
%% mytype() -> term().
