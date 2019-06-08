.PHONY: all
all: erlang

#.PHONY: python
#python:
#	mypy python/coins.py --ignore-missing-imports
#	pytest python/coins.py --hypothesis-show-statistics
#	python3 python/coins.py

.PHONY: erlang
erlang:
	cd erlang/memoize && rebar3 do escriptize, eunit
	cd erlang/memoize && _build/default/bin/memoize
