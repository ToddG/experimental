.PHONY: all
all: erlang

.PHONY: python
python:
	mypy python/matrix.py --ignore-missing-imports
	pytest python/matrix.py --hypothesis-show-statistics
	python3 python/matrix.py

.PHONY: erlang
erlang:
	cd erlang/matrix && rebar3 do escriptize, eunit, proper
	cd erlang/matrix && _build/default/bin/matrix
