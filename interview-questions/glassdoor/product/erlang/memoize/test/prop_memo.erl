-module(prop_memo).
-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

%%%%%%%%%%%%%%%%%%
%%% Properties %%%
%%%%%%%%%%%%%%%%%%
prop_test() ->
    ?FORALL(Type, posints(),
        begin
            Len = length(Type),
            Msg1 = io_lib:format("|mult|len|~w|time|", [Len]),
            Msg2 = io_lib:format("|multm|len|~w|time|", [Len]),
            Msg3 = io_lib:format("|multz|len|~w|time|", [Len]),
            M1 = ?debugTime(Msg1, memoize:mult(Type)),
            M2 = ?debugTime(Msg2, memoize:multm(Type)),
            M3 = ?debugTime(Msg3, memoize:multz(Type)),
            M1 =:= M2 andalso
            M1 =:= M3
        end).

prop_collect_length() ->
    ?FORALL(Type, posints(),
            collect(to_range(10, length(Type)), true)).

to_range(M,N) ->
    Base = N div M,
    {Base*M, (Base+1)*M}.


%%%%%%%%%%%%%%%
%%% Helpers %%%
%%%%%%%%%%%%%%%
%boolean(_) -> true.

%%%%%%%%%%%%%%%%%%
%%% Generators %%%
%%%%%%%%%%%%%%%%%%
%%posints() -> resize(150, non_empty(list(pos_integer()))).
posints() -> non_empty(list(pos_integer())).
