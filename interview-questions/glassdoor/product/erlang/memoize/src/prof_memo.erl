-module(prof_memo).
-include_lib("eunit/include/eunit.hrl").

%% API exports
-export([cprof/0, fprof/0, perf/0]).
-define(timeit(S, E),
	begin
	((fun () ->
		  {__T0, _} = statistics(wall_clock),
		  __V = (E),
		  {__T1, _} = statistics(wall_clock),
                  {io_lib:format(<<"~ts~.3f">>, [(S), (__T1-__T0)/1000]), __V}
	  end)())
	end).
%%====================================================================
%% API functions
%%====================================================================
cprof() ->
    D = pdata(100),
    io:format("cprof mult~n~p~n",  [?debugTime("time=", cprofile(fun memoize:mult/1, D))]),
    io:format("cprof multm~n~p~n", [?debugTime("time=", cprofile(fun memoize:multm/1, D))]),
    io:format("cprof multz~n~p~n", [?debugTime("time=", cprofile(fun memoize:multz/1, D))]).

fprof() ->
    D = pdata(100),
    io:format("fprof mult~n~p~n",  [?debugTime("time=", fprofile("mult", fun memoize:mult/1, D))]),
    io:format("fprof multm~n~p~n", [?debugTime("time=", fprofile("multm", fun memoize:multm/1, D))]),
    io:format("fprof multz~n~p~n", [?debugTime("time=", fprofile("multz", fun memoize:multz/1, D))]).

perf() ->
    {ok, F} = file:open("perf_run.csv", [write]),
    perf(10, 100000, F).

perf(N, M, F) when N =< M ->
    run_tests(N, F),
    perf(N * 2, M, F);
perf(N, M, _) when N >= M ->
    ok.

run_tests(N, F) ->
    D = pdata(N),
    % swallow the output of the memoized functions
    FX = fun(Fx, X) ->
                        _ = Fx(X),
                        ok 
         end,
    M1 = io_lib:format("|mult|len|~w|time|", [N]),
    %M2 = io_lib:format("|multm|len|~w|time|", [N]),
    M3 = io_lib:format("|multz|len|~w|time|", [N]),
    {R1, _} = ?timeit(M1, FX(fun memoize:mult/1, D)),
    %{R2, _} = ?timeit(M2, FX(fun memoize:multm/1, D)),
    {R3, _} = ?timeit(M3, FX(fun memoize:multz/1, D)),
    io:format("~s~n", [R1]),
    %io:format("~s~n", [R2]),
    io:format("~s~n", [R3]),
    io:format(F, "~s~n", [R1]),
    %io:format(F, "~s~n", [R2]),
    io:format(F, "~s~n", [R3]).

pdata(N) ->
    pdata(N, []).
pdata(0, Acc) -> Acc;
pdata(N, Acc) when N > 0 ->
    pdata(N-1, [N|Acc]).

cprofile(F, A) ->
    cprof:stop(),
    cprof:start(),
    F(A),
    R = cprof:analyze(memoize),
    cprof:stop(),
    R.

fprofile(Name, F, A) ->
    fprof:trace(start),
    F(A),
    fprof:trace(stop),
    fprof:profile(),
    fprof:analyse({dest, Name ++ "_profile.fprof"}).
