#!/usr/bin/env bash

KERNEL_TYPE=${1:-"tcpaad"} # Kernel type: "tcpaad" or "default"
SERVER_IP="192.168.1.165" # Modified machine (WiFi, iperf3 server)
CLIENT_IP="192.168.1.50"   # Default machine (Ethernet, iperf3 client)
ROUTER_IP="192.168.1.1"    # OpenWRT router
ROUTER_USER="root"         # Router SSH username
ROUTER_SSH_OPTS="-oHostKeyAlgorithms=+ssh-rsa -oPubkeyAcceptedAlgorithms=+ssh-rsa"  # SSH options for older OpenWRT routers
ROUTER_PASSWORD=""         # Router SSH password (leave empty if using SSH keys)
                           # WARNING: Password stored in plaintext. For local networks only.
SERVER_USER="rakhat"       # Server SSH username (adjust as needed)
SERVER_WIFI_IFACE="wlan0"  # WiFi interface on server (not used for tc)
CLIENT_IFACE="eth0"        # Client ethernet interface (for tc bandwidth/delay shaping)
                           # Common names: eth0, enp0s3, ens33, etc. Check with: ip link show

IPERF_PORT=5201
TEST_DURATION=30 # seconds per test

BANDWIDTHS=(10 20 50 nolim)            # Bandwidth limits in Mbps (nolim = unlimited)
DELAYS=(10 50 100)                     # Network delays in milliseconds
RATES=(34 35 36 37 44 45 46 47 94 95 96 97 104 105 106 107)  # WiFi MCS rate indices
ITERATIONS=3                           # Number of iterations per configuration

SETTLE_TIME=5                          # Seconds to wait between tests

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RESULTS_DIR="${SCRIPT_DIR}/results/${KERNEL_TYPE}"
LOGS_DIR="${SCRIPT_DIR}/results/logs"

declare -A RATE_MAP=(
    [34]="HT20-SGI-MCS4"   [35]="HT20-SGI-MCS5"   [36]="HT20-SGI-MCS6"   [37]="HT20-SGI-MCS7"
    [44]="HT20-SGI-MCS12"  [45]="HT20-SGI-MCS13"  [46]="HT20-SGI-MCS14"  [47]="HT20-SGI-MCS15"
    [94]="HT40-SGI-MCS4"   [95]="HT40-SGI-MCS5"   [96]="HT40-SGI-MCS6"   [97]="HT40-SGI-MCS7"
    [104]="HT40-SGI-MCS12" [105]="HT40-SGI-MCS13" [106]="HT40-SGI-MCS14" [107]="HT40-SGI-MCS15"
)

export SERVER_IP CLIENT_IP ROUTER_IP ROUTER_USER ROUTER_SSH_OPTS ROUTER_PASSWORD SERVER_USER SERVER_WIFI_IFACE CLIENT_IFACE
export IPERF_PORT TEST_DURATION
export BANDWIDTHS DELAYS RATES ITERATIONS
export SETTLE_TIME KERNEL_TYPE
export SCRIPT_DIR RESULTS_DIR LOGS_DIR
export RATE_MAP
