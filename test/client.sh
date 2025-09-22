#!/bin/bash

iperf3 -c 192.168.0.135 -p 5201 -i 5 -n 1g > tcp_1g.txt
iperf3 -c 192.168.0.135 -p 5201 -i 5 -n 500m > tcp_500m.txt
iperf3 -c 192.168.0.135 -p 5201 -i 5 -t 30 > tcp_30s.txt
iperf3 -c 192.168.0.135 -p 5201 -i 5 -t 60 > tcp_60s.txt
iperf3 -c 192.168.0.135 -p 5201 -i 5 -P 4 -t 20 > tcp_4streams.txt
iperf3 -c 192.168.0.135 -p 5201 -i 5 -P 8 -t 20 > tcp_8streams.txt
iperf3 -c 192.168.0.135 -p 5201 -i 5 -R -t 30 > tcp_reverse_30s.txt
iperf3 -c 192.168.0.135 -p 5201 -i 5 -R -t 60 > tcp_reverse_30s.txt
