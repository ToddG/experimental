.PHONY: all
all: jup

.PHONY: sortz
sortz: monitor_start
	cd erlang/sortz && rebar3 do escriptize, eunit, proper
	cd erlang/sortz && _build/default/bin/sortz

.PHONY: psortz
psortz: monitor_start
	cd erlang/psortz && rebar3 do escriptize, eunit
	cd erlang/psortz && _build/default/bin/psortz

.PHONY: monitor_start
monitor_start: 
	cd monitor && $(MAKE) start

.PHONY: monitor_stop
monitor_stop: 
	cd monitor && $(MAKE) stop


