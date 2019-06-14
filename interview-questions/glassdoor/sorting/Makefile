.PHONY: all
all: jup

.PHONY: erlang
erlang:
	cd erlang/sortz && rebar3 do escriptize, eunit, proper
	cd erlang/sortz && _build/default/bin/sortz

.PHONY: jup
jup:
	cd erlang/sortz/docs && jupyter-notebook
