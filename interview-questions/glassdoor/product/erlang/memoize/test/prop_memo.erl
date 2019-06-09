-module(prop_memo).
-include_lib("proper/include/proper.hrl").

%%%%%%%%%%%%%%%%%%
%%% Properties %%%
%%%%%%%%%%%%%%%%%%
prop_test() ->
    ?FORALL(Type, posints(),
        begin
            M1 = memoize:mult(Type),
            M2 = memoize:multm(Type),
            io:format("T: ~p, M1: ~p, M2: ~p~n",[Type, M1,M2]),
            M1 =:= M2
        end).

%%%%%%%%%%%%%%%
%%% Helpers %%%
%%%%%%%%%%%%%%%
boolean(_) -> true.

%%%%%%%%%%%%%%%%%%
%%% Generators %%%
%%%%%%%%%%%%%%%%%%
posints() -> non_empty(list(pos_integer())).
