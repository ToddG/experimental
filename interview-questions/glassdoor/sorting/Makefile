.PHONY: all
all: jup

.PHONY: sortz
sortz:
	cd erlang/sortz && rebar3 do escriptize, eunit, proper
	cd erlang/sortz && _build/default/bin/sortz

.PHONY: psortz
psortz:
	cd erlang/psortz && rebar3 do escriptize, eunit
	cd erlang/psortz && _build/default/bin/psortz
