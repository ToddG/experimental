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

.PHONY: stop
stop: stop_collectd stop_influxdb stop_grafana
	docker ps -a

# monitor
.PHONY: monitor
monitor: collectd influxdb grafana
	docker ps -a

# start event collectd 
.PHONY: collectd
collectd: stop_collectd
	docker run									\
	    	--name collectd 							\
		--network=host --privileged 						\
		-v /proc:/mnt/proc:ro 							\
		-v $(CURDIR)/monitoring/collectd.conf:/etc/collectd/collectd.conf 	\
		--rm fr3nd/collectd &

# start influxdb to store metrics
.PHONY: influxdb
influxdb: stop_influxdb
	docker run 	 								\
		--name influxdb 							\
		-p 8083:8083 -p 8086:8086 -p 25826:25826/udp 				\
		-v $(CURDIR)/monitoring/influxdb:/var/lib/influxdb 			\
		-v $(CURDIR)/monitoring/influxdb.conf:/etc/influxdb/influxdb.conf:ro 	\
		-v $(CURDIR)/monitoring/types.db:/usr/share/collectd/types.db:ro 	\
		--rm influxdb:1.5.4 &


# start grafana for visualizations
.PHONY: grafana
grafana: stop_grafana
	if [ ! -e "$(CURDIR)/monitoring/grafana" ]; then mkdir -p $(CURDIR)/monitoring/grafana; fi
	docker run									\
		--name grafana 								\
		--user $(shell id -u)							\
		-p 3000:3000 								\
		-v $(CURDIR)/monitoring/grafana:/var/lib/grafana			\
		--link influxdb 							\
		--rm grafana/grafana:6.2.4 &

.PHONY: stop_grafana
stop_grafana:
	-docker stop grafana
	-docker rm grafana

.PHONY: stop_influxdb
stop_influxdb:
	-docker stop influxdb
	-docker rm influxdb

.PHONY: stop_collectd
stop_collectd:
	-docker stop collectd
	-docker rm collectd
