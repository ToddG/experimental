-module(psortz).
-compile(export_all).
-include_lib("eunit/include/eunit.hrl").
%% API exports
-record(suite, {algorithm, generator, size}).
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
    % test suite definition
    S = suite(),
    io:format("suite: ~p~n",[S]),
    % generate input datasets
    D = [{GName, GFunc(Size)} || {GName, GFunc} <- S#suite.generator, Size <- S#suite.size],
    %io:format("data: ~n~p~n",[D]),
    % run the benchmarks
    benchmark_01(S, D),
    benchmark_02(S, D),
    % done
    erlang:halt(0).

%%====================================================================
%% Internal functions
%%====================================================================
%%--------------------------------------------------------------------
%% Benchmark Framework
%%--------------------------------------------------------------------
pheader() ->
    io_lib:format(<<"procs|alg|input|items|utc|ts|duration|func">>, []).

pbench(AlgName, InputName, F, L, Procs) ->
    InputSize = length(L),
    TS = format_utc_timestamp(),
    TS1 = erlang:system_time(microsecond),
    {Duration, Res} = ?timeit(F(L)),
    S = io_lib:format(<<"~w|~s|~s|~w|~s|~w|~.6f|all">>, [Procs, AlgName, InputName, InputSize, TS, TS1, Duration]),
    %% sanity check that the sorting function actually worked
    ?assertEqual(lists:sort(L), Res, AlgName),
    S.

benchmark_01(S, D) ->
    %% benchmark sorting where:
    %%  L is the input dataset
    %%  C is a chunk of L, where the number of chunks == number of procs
    %%  F is the sorting function
    %%  F(rpc:pmap(M,F,[],C)
    %%
    %%  NOTE: so this boils down to ```F(pmap(F))```
    %%  I think we'll see that the outer F swamps the inner F.
    {ok, File} = file:open("docs/perf/pperf-01.csv", [write, append]),
    dump(File, [pheader()]),
    PF = fun (Procs) -> 
                 [dump(File, [pbench(AName, GName, fun(L) ->  parallelized_sort(AName, GName, AFunc, L, Procs, File) end, Data, Procs)]) || 
                  {AName, AFunc} <- S#suite.algorithm, {GName, Data} <- D] end,
    [PF(Procs) || Procs <- procs()].

benchmark_02(S, D) ->
    %% benchmark sorting where:
    %%  L is the input dataset
    %%  C is a chunk of L, where the number of chunks == number of procs
    %%  F is the sorting function
    %%  lists:merge(rpc:pmap(M,F,[],C)
    %%
    %%  NOTE: so this boils down to ```lists:merge(pmap(F))```
    %%  I think we'll better the true performance of the inner F
    %%  and the benefits of pmap in this benchmark.
    {ok, File} = file:open("docs/perf/pperf-02.csv", [write,append]),
    dump(File, [pheader()]),
    PF = fun (Procs) -> 
                 [dump(File, [pbench(AName, GName, fun(L) ->  parallelized_sort(AName, GName, L, Procs, File) end, Data, Procs)] ) || 
                  {AName, _} <- S#suite.algorithm, {GName, Data} <- D] end,
    [PF(Procs) || Procs <- procs()].

procs() ->
    % replace this line to hardcode the number of procs like so
    % [3,2,1].
    lists:seq(1, max(1, min(7, erlang:system_info(logical_processors_available)))).

dump(F, R) ->
    [io:format("~s~n",[I]) || I <- R ],
    [io:format(F, "~s~n",[I]) || I <- R ].

%%--------------------------------------------------------------------
%% Sorting Algorithms -- dummy
%%--------------------------------------------------------------------
dummy_sort(L) ->
    lists:sort(L).

%%--------------------------------------------------------------------
%% Sorting Algorithms -- quicksort
%%--------------------------------------------------------------------
quicksort_generic(Pivot, F, L) ->
    {LHS, RHS} = lists:partition(fun(X) -> X < Pivot end, L),
    F(LHS) ++ [Pivot] ++ F(RHS).

quicksort_random([]) -> [];
quicksort_random([A]) -> [A];
quicksort_random(L) ->
    N = rand:uniform(length(L) - 1),
    {LHS, [Pivot|RHS]} = lists:split(N, L),
    quicksort_generic(Pivot, fun quicksort_random/1, LHS ++ RHS).


%%--------------------------------------------------------------------
%% Parallelized Sorting Algorithms
%%--------------------------------------------------------------------
parallelized_sort(FName, GName, OuterF, L, Procs, File) ->
    DataLen = length(L),
    Log = fun(N,T) ->
        dump(File, [io_lib:format(<<"~w|~s|~s|~w|~s|~w|~.8f|~s">>, [Procs, FName, GName, DataLen, format_utc_timestamp(), erlang:system_time(microsecond), T, N])]) end,
    {FragTime, Frags} = ?timeit(fragment(L, Procs)),
    Log(frag, FragTime),
    FuncNameAtom = list_to_atom(FName),
    {RPCTime, RPCRes} = ?timeit(rpc:pmap({?MODULE, FuncNameAtom}, [], Frags)),
    Log(rpcpmap, RPCTime),
    {MergeTime, Merged} = ?timeit(OuterF(lists:flatten(RPCRes))),
    Log(merge, MergeTime),
    Merged.

parallelized_sort(FName, GName, L, Procs, File) ->
    DataLen = length(L),
    Log = fun(N,T) ->
        dump(File, [io_lib:format(<<"~w|~s|~s|~w|~s|~w|~.8f|~s">>, [Procs, FName, GName, DataLen, format_utc_timestamp(), erlang:system_time(microsecond), T, N])]) end,
    {FragTime, Frags} = ?timeit(fragment(L, Procs)),
    Log(frag, FragTime),
    FuncNameAtom = list_to_atom(FName),
    {RPCTime, RPCRes} = ?timeit(rpc:pmap({?MODULE, FuncNameAtom}, [], Frags)),
    Log(rpcpmap, RPCTime),
    {MergeTime, Merged} = ?timeit(lists:merge(RPCRes)),
    Log(merge, MergeTime),
    Merged.

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

random(N) ->
    random(N, N*1000).
random(N, M) ->
    [rand:uniform(M) || _ <- lists:seq(1, N)].

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
                {"quicksort_random",fun quicksort_random/1}
               ],
     generator=[
                {"random",        fun random/1}
               ],
     size=[trunc(math:pow(10, P)) || P <- lists:seq(1, max(1, min(7, erlang:system_info(logical_processors_available)))) ]
      }.
