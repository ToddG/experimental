-module(sortz).
-compile(export_all).
-include_lib("eunit/include/eunit.hrl").
%% API exports
-export([main/1]).
-define(timeit(E),
	begin
	((fun () ->
		  {__T0, _} = statistics(wall_clock),
		  __V = (E),
		  {__T1, _} = statistics(wall_clock),
                  {(__T1-__T0)/1000, __V}
	  end)())
	end).
%%====================================================================
%% API functions
%%====================================================================

%% escript Entry point
main(_) ->
    run_benchmarks(suite()),
    erlang:halt(0).
-record(suite, {algorithm, generator, size}).

%%====================================================================
%% Internal functions
%%====================================================================
%%--------------------------------------------------------------------
%% Benchmark Framework
%%--------------------------------------------------------------------
header() ->
    io_lib:format(<<"alg|input|items|utc|ts|duration">>, []).
pheader() ->
    io_lib:format(<<"procs|~s">>, [header()]).

pbench(AlgName, InputName, F, L, Procs) ->
    S = bench(AlgName, InputName, F, L),
    S0 = io_lib:format(<<"~w|">>, [Procs]),
    S0 ++ S.

bench(AlgName, InputName, F, L) ->
    InputSize = length(L),
    TS = format_utc_timestamp(),
    TS1 = erlang:system_time(microsecond),
    {Duration, Res} = ?timeit(F(L)),
    S = io_lib:format(<<"~s|~s|~w|~s|~w|~.6f">>, [AlgName, InputName, InputSize, TS, TS1, Duration]),
    %% sanity check that the sorting function actually worked
    ?assertEqual(lists:sort(L), Res, AlgName),
    S.

run_benchmarks(S) ->
    {ok, File1} = file:open("docs/perf/perf_run.csv", [write]),
    S = suite(),
    D = [{GName, GFunc(Size)} || {GName, GFunc} <- S#suite.generator, 
                                 {Size} <- S#suite.size],
    dump(File1, [header()]),
    [dump(File1, [bench(AName, GName, AFunc, Data)]) || {AName, AFunc} <- S#suite.algorithm, {GName, Data} <- D].

%    {ok, File2} = file:open("docs/perf/pperf_run.csv", [write]),
%    dump(File2, [pheader()]),
%    PF = fun (Procs) -> [dump(
%                           File2, 
%                           [pbench(AName, GName, fun(L) ->  parallelized_sort(AName, L, Procs) end, Data, Procs)]) || {AName, _} <- S#suite.algorithm, {GName, Data} <- D]) end,
%    [PF(Procs) || Procs <- lists:seq(1, erlang:system_info(logical_processors_available))].


dump(F, R) ->
    [io:format("~s~n",[I]) || I <- R ],
    [io:format(F, "~s~n",[I]) || I <- R ].

%%--------------------------------------------------------------------
%% Sorting Algorithms -- dummy
%%--------------------------------------------------------------------
dummy_sort(L) ->
    lists:sort(L).


%%--------------------------------------------------------------------
%% Sorting Algorithms -- insertion
%%--------------------------------------------------------------------
insertion_sort([H|T]) ->
   insertion_sort([H], T).
insertion_sort(Sorted, []) ->
    Sorted;
insertion_sort(Sorted, [H|T]) ->
    {A, B} = lists:partition(fun(X) -> X < H end, Sorted),
    insertion_sort(A ++ [H] ++ B, T).

%%--------------------------------------------------------------------
%% Sorting Algorithms -- quicksort
%%--------------------------------------------------------------------
quicksort_generic(Pivot, F, L) ->
    {LHS, RHS} = lists:partition(fun(X) -> X < Pivot end, L),
    F(LHS) ++ [Pivot] ++ F(RHS).

quicksort_right([]) -> [];
quicksort_right([A]) -> [A];
quicksort_right(L) ->
    quicksort_generic(lists:last(L), fun quicksort_right/1, lists:droplast(L)).
quicksort_left([]) -> [];
quicksort_left([A]) -> [A];
quicksort_left(L) ->
    {LHS, RHS} = lists:split(1, L),
    quicksort_generic(lists:nth(1, LHS), fun quicksort_left/1, RHS).
quicksort_random([]) -> [];
quicksort_random([A]) -> [A];
quicksort_random(L) ->
    N = rand:uniform(length(L) - 1),
    {LHS, [Pivot|RHS]} = lists:split(N, L),
    quicksort_generic(Pivot, fun quicksort_random/1, LHS ++ RHS).

%%--------------------------------------------------------------------
%% Sorting Algorithms -- heapsort
%%--------------------------------------------------------------------
%% Algorithm shamelessly pulled from: 
%% 	Algorithms in A Nutshell, pg 87
%% 	ISBN 978-0-596-51624-6
%% 	Printed 2008, First Edition.
heapsort(L) ->
    A = array:from_list(L),
    N = array:size(A),
    A1 = build_heap(A, N),
    A2 = lists:foldl(fun(I, Acc) -> heapify(swap(Acc, 0, I, N), 0, I) end, A1, lists:seq(N - 1, 1, -1)),
    array:to_list(A2).

build_heap(A, N) ->
    lists:foldl(fun(I, Acc) -> heapify(Acc, I, N) end, A, lists:seq(N div 2 - 1, 0, -1)).

heapify(A, I, Max) ->
    L = 2*I + 1,
    R = 2*I + 2,
    Largest1 = largest_left(L, I, Max, array:get(L, A), array:get(I, A)),
    Largest2 = largest_right(R, Largest1, Max, array:get(R, A), array:get(Largest1, A)),
    if 
	Largest2 =/= I -> 
	    A2 = swap(A, Largest2, I, Max),
	    heapify(A2, Largest2, Max);
	true -> A
    end.

swap(A, X, X, _) ->
    A;
swap(A, L, R, Max) when L =/= R andalso L < Max andalso R < Max ->
    TL = array:get(L, A),
    A1 = array:set(L, array:get(R, A), A),
    A2 = array:set(R, TL, A1),
    A2;
swap(A, _, _, _) -> A.
    

largest_left(Left, _, Max, ALeft, AIdx) when Left < Max andalso ALeft > AIdx ->
    Left;
largest_left(_, Idx, _, _, _) ->
    Idx.
largest_right(Right, _, Max, ARight, ALargest) when Right < Max andalso ARight > ALargest ->
    Right;
largest_right(_, Largest, _, _, _) ->
    Largest.


%%--------------------------------------------------------------------
%% Sorting Algorithms -- bucketsort
%%--------------------------------------------------------------------

bucketsort(L) ->
    D = dict:new(),
    D1 = bucketsort(L, D, fun(X) -> trunc(math:log(X)) end),
    lists:flatten([insertion_sort(dict:fetch(K, D1)) || K <- insertion_sort(dict:fetch_keys(D1))]).

bucketsort([], D, _) -> D;
bucketsort([H|T], D, HashFunc) ->
    K = HashFunc(H),
    bucketsort(T, 
	       case dict:find(K, D) of 
		   {ok, _} -> dict:append(K, H, D); 
		   error -> dict:store(K, [H], D)
	       end, HashFunc).

%%--------------------------------------------------------------------
%% Parallelized Sorting Algorithms
%%--------------------------------------------------------------------
parallelized_sort(FName, L, Procs) -> 
    heapsort(lists:flatten(rpc:pmap({?MODULE, list_to_atom(FName)}, [], fragment(L, Procs)))).

fragment(L, Count) ->
    FragLen = length(L) div Count,
    fragment(L, FragLen, []).
fragment([], _, Acc) -> Acc;
fragment(L, 0, Acc) -> [L|Acc];
fragment(L, N, Acc) when length(L) > N ->
    {H,T} = lists:split(N, L),
    fragment(T, N, [H|Acc]);
fragment(L, N, Acc) when length(L) =< N -> [L|Acc].
    
%%--------------------------------------------------------------------
%% Generators
%%--------------------------------------------------------------------

constant(N) ->
    constant(1, N).
sorted(N) ->
    presorted(random(N, N*1000)).
reversed(N) ->
    lists:reverse(sorted(N)).
random(N) ->
    random(N, N*1000).
interleaved(N) ->
    % interleaved calls 4 separate data sources, so we get 1/4 N from each
    interleaved(N div 4, N*1000).
bucketed(N) ->
    bucketed(10, random(N, N*1000)).

constant(K, N) ->
    lists:duplicate(N, K).
presorted(L) ->
    lists:sort(L).
reversesorted(L) ->
    lists:reverse(lists:sort(L)).
random(N, M) ->
    [rand:uniform(M) || _ <- lists:seq(1, N)].
interleaved(N, M) ->
    constant(rand:uniform(M), N)  ++ 
    presorted(random(N,M))          ++ 
    reversesorted(random(N,M))      ++ 
    random(N,M).
bucketed(B, L) ->
    [E2 || {_, E2} <- lists:keysort(1, [{rand:uniform(B), E} || E <- L])].

%%--------------------------------------------------------------------
%% Helpers
%%--------------------------------------------------------------------
format_utc_timestamp() ->
    TS = {_,_,Micro} = os:timestamp(),
    {{Year,Month,Day},{Hour,Minute,Second}} = calendar:now_to_universal_time(TS),
    Mstr = element(Month,{"Jan","Feb","Mar","Apr","May","Jun","Jul", "Aug","Sep","Oct","Nov","Dec"}),
    io_lib:format("~2w ~s ~4w ~2w:~2..0w:~2..0w.~6..0w", [Day,Mstr,Year,Hour,Minute,Second,Micro]).

%%--------------------------------------------------------------------
%% Test Suite
%%--------------------------------------------------------------------

suite() ->
    #suite{
     algorithm=[{"dummy_sort",      fun dummy_sort/1},
                {"insertion_sort",  fun insertion_sort/1},
                {"quicksort_left",  fun quicksort_left/1},
                {"quicksort_right", fun quicksort_right/1},
                {"quicksort_random",fun quicksort_random/1},
		{"heapsort",	    fun heapsort/1},
		{"bucketsort",	    fun bucketsort/1}
               ],
     generator=[{"constant",      fun constant/1},
                {"sorted",        fun sorted/1},
                {"reversed",      fun reversed/1},
                {"random",        fun random/1},
                {"interleaved",   fun interleaved/1},
                {"bucketed",      fun bucketed/1}],
     size=[
           {10},
           {100}, 
           {1000},
           {10000},
           {100000}
          ]
      }.
