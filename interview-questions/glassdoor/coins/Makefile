.PHONY: all
all: python erlang

.PHONY: python
python:
	mypy python/coins.py --ignore-missing-imports
	pytest python/coins.py --hypothesis-show-statistics
	python3 python/coins.py

.PHONY: erlang
erlang:
	cd erlang/mylib && rebar3 do escriptize, eunit, proper
	cd erlang/mylib && _build/default/bin/mylib
