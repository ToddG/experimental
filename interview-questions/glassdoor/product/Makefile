.PHONY: all
all: erlang

#.PHONY: python
#python:
#	mypy python/coins.py --ignore-missing-imports
#	pytest python/coins.py --hypothesis-show-statistics
#	python3 python/coins.py

.PHONY: erlang
erlang:
	cd erlang/memoize && rebar3 do escriptize, eunit, proper
	cd erlang/memoize && _build/default/bin/memoize
	# see https://github.com/isacssouza/erlgrind
	cd erlang/memoize && erlgrind mult_profile.fprof  mult_profile.cgrind
	cd erlang/memoize && erlgrind multm_profile.fprof multm_profile.cgrind
	cd erlang/memoize && erlgrind multz_profile.fprof multz_profile.cgrind
