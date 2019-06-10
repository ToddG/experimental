-module(prof_memo).
-include_lib("eunit/include/eunit.hrl").

%% API exports
-export([cprof/0, fprof/0]).

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
