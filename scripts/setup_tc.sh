#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "${SCRIPT_DIR}/config.sh"
source "${SCRIPT_DIR}/scripts/utils.sh"

if [ $# -ne 2 ]; then
    log_error "Usage: $0 <bandwidth> <delay>"
    log_error "  bandwidth: 10|20|50|nolim (in Mbps)"
    log_error "  delay: delay in milliseconds (e.g., 10, 50, 100)"
    exit 1
fi

BANDWIDTH=$1
DELAY=$2

"${SCRIPT_DIR}/scripts/cleanup_tc.sh" 2>/dev/null

log_info "Applying tc: bandwidth=${BANDWIDTH}mb, delay=${DELAY}ms"

# Apply tc rules
if [ "$BANDWIDTH" = "nolim" ]; then
    # Only apply delay, no bandwidth limit
    if ssh "${SERVER_USER}@${SERVER_IP}" \
        "tc qdisc add dev ${SERVER_WIFI_IFACE} root netem delay ${DELAY}ms" 2>/dev/null; then
        log_success "Applied tc: delay=${DELAY}ms (no bandwidth limit)"
        exit 0
    else
        log_error "Failed to apply tc delay"
        exit 1
    fi
else
    if ! ssh "${SERVER_USER}@${SERVER_IP}" \
        "tc qdisc add dev ${SERVER_WIFI_IFACE} root handle 1: tbf rate ${BANDWIDTH}mbit burst 32kbit latency 400ms" 2>/dev/null; then
        log_error "Failed to apply tc bandwidth limit"
        exit 1
    fi

    if ! ssh "${SERVER_USER}@${SERVER_IP}" \
        "tc qdisc add dev ${SERVER_WIFI_IFACE} parent 1:1 handle 10: netem delay ${DELAY}ms" 2>/dev/null; then
        log_error "Failed to apply tc delay"
        # Cleanup partial configuration
        ssh "${SERVER_USER}@${SERVER_IP}" "tc qdisc del dev ${SERVER_WIFI_IFACE} root" 2>/dev/null
        exit 1
    fi

    log_success "Applied tc: bandwidth=${BANDWIDTH}mb, delay=${DELAY}ms"
    exit 0
fi
