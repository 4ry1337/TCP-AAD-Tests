#!/bin/bash

IPERF_PORT=${IPERF_PORT:-5201}

if pgrep -x "iperf3" > /dev/null; then
    echo "WARNING: iperf3 is already running"
    read -p "Kill existing iperf3 processes? (y/n) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        pkill -x iperf3
        echo "Killed existing iperf3 processes"
        sleep 1
    fi
fi

echo "Network interfaces:"
ip -br addr
echo ""
echo "Kernel version: $(uname -r)"
echo ""
echo "Starting iperf3 server on port ${IPERF_PORT}..."
echo ""

iperf3 -s -p ${IPERF_PORT}
