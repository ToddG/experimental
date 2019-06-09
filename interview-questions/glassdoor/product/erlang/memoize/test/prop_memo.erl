-module(prop_memo).
-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

%%%%%%%%%%%%%%%%%%
%%% Properties %%%
%%%%%%%%%%%%%%%%%%
prop_test() ->
    ?FORALL(Type, posints(),
        begin
            M1 = memoize:mult(Type),
            M2 = memoize:multm(Type),
            M1 =:= M2
        end).

prop_collect_length() ->
    ?FORALL(Type, posints(),
            collect(to_range(10, length(Type)), true)).

to_range(M,N) ->
    Base = N div M,
    {Base*M, (Base+1)*M}.

prop_profile() ->
    ?FORALL(Type, posints(),
        begin
            {Mult, Multm, Multz, T} = multiply_init(),
            Len = length(Type),
            Msg1 = io_lib:format("|mult|len|~w|time|", [Len]),
            Msg2 = io_lib:format("|multm|len|~w|time|", [Len]),
            Msg3 = io_lib:format("|multz|len|~w|time|", [Len]),
            M1 = ?debugTime(Msg1, memoize:mult(Type, Mult)),
            M2 = ?debugTime(Msg2, memoize:multm(Type, Multm)),
            M3 = ?debugTime(Msg3, memoize:multz(Type, Multz)),
            [{mult, C1, C2, C3, _}|_] = ets:lookup(T, mult),
            ?debugFmt("|mult|count|~w|~n",  [C1]),
            ?debugFmt("|multm|count|~w|~n", [C2]),
            ?debugFmt("|multz|count|~w|~n", [C3]),
            M1 =:= M2 andalso
            M1 =:= M3
        end).

%%%%%%%%%%%%%%%
%%% Helpers %%%
%%%%%%%%%%%%%%%
%boolean(_) -> true.
ets_init() ->
    case ets:whereis(mmm) of
        undefined ->
            T = ets:new(mmm, [set, named_table, public]),
            ets:insert(T, {mult, 0, 0, 0, "calls to multiply from mult|multm|multz"}),
            T;
        Table ->
            % clear counters for subsequent runs
            ets:update_element(Table, mult, {2, 0}),
            ets:update_element(Table, mult, {3, 0}),
            ets:update_element(Table, mult, {4, 0}),
            Table
    end.

multiply_init() ->
    % ets stuff
    % T : table
    % mult : key name
    % 2 : mult counter
    % 3 : multm counter
    % 4 : multz counter
    T = ets_init(),
    F1 = fun(A, B) -> 
                 ets:update_counter(T, mult, {2, 1}),
                 memoize:multiply(A,B) end,
    F2 = fun(A, B) -> 
                 ets:update_counter(T, mult, {3, 1}),
                 memoize:multiply(A,B) end,
    F3 = fun(A, B) -> 
                 ets:update_counter(T, mult, {4, 1}),
                 memoize:multiply(A,B) end,
    {F1, F2, F3, T}.

%%%%%%%%%%%%%%%%%%
%%% Generators %%%
%%%%%%%%%%%%%%%%%%
posints() -> resize(150, non_empty(list(pos_integer()))).
