#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "${SCRIPT_DIR}/config.sh"
source "${SCRIPT_DIR}/scripts/utils.sh"

if [ $# -ne 1 ]; then
    log_error "Usage: $0 <output_file>"
    exit 1
fi

OUTPUT_FILE=$1

{
    echo "{"
    echo "  \"timestamp\": \"$(date -Iseconds)\","
    echo "  \"kernel\": \"${KERNEL_TYPE}\","
    echo -n "  \"server_kernel_version\": \""
    ssh "${SERVER_USER}@${SERVER_IP}" "uname -r" 2>/dev/null | tr -d '\n'
    echo "\","
    echo "  \"wifi_stats\": {"
    echo -n "    \"rc_stats\": \""
    ssh "${ROUTER_USER}@${ROUTER_IP}" "cat /sys/kernel/debug/ieee80211/phy1/rc/fixed_rate_idx 2>/dev/null" 2>/dev/null | tr -d '\n'
    echo "\","
    echo -n "    \"station_info\": \""
    ssh "${ROUTER_USER}@${ROUTER_IP}" "iw dev wlan0 station dump 2>/dev/null | head -20" 2>/dev/null | sed 's/"/\\"/g' | tr '\n' ' ' | tr -d '\r'
    echo "\""
    echo "  },"
    echo "  \"tcp_stats\": {"
    echo -n "    \"ss_output\": \""
    ssh "${SERVER_USER}@${SERVER_IP}" "ss -tin dst ${CLIENT_IP} 2>/dev/null" 2>/dev/null | sed 's/"/\\"/g' | tr '\n' ' ' | tr -d '\r'
    echo "\""
    echo "  }"
    echo "}"
} > "$OUTPUT_FILE"

exit 0
