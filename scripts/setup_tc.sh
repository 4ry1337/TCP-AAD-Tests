#!/usr/bin/env bash

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

"${SCRIPT_DIR}/scripts/cleanup_tc.sh"

log_info "Applying tc on ${CLIENT_IFACE}: bw=${BANDWIDTH}mb, d=${DELAY}ms"

if [ "$BANDWIDTH" = "nolim" ]; then
    if sudo tc qdisc add dev ${CLIENT_IFACE} root netem delay ${DELAY}ms; then
        log_success "Applied tc: delay=${DELAY}ms (no bandwidth limit)"
        exit 0
    else
        log_error "Failed to apply tc delay (see error above)"
        exit 1
    fi
else
    # Step 1: Add tbf qdisc for bandwidth limiting
    if ! sudo tc qdisc add dev ${CLIENT_IFACE} root handle 1: tbf rate ${BANDWIDTH}mbit burst 32kbit latency 400ms; then
        log_error "Failed to apply tc bandwidth limit (see error above)"
        exit 1
    fi

    # Step 2: Add netem qdisc as child for delay
    if ! sudo tc qdisc add dev ${CLIENT_IFACE} parent 1:1 handle 10: netem delay ${DELAY}ms; then
        log_error "Failed to apply tc delay (see error above)"
        # Cleanup partial configuration
        sudo tc qdisc del dev ${CLIENT_IFACE} root 2>/dev/null
        exit 1
    fi

    log_success "Applied tc on client: bandwidth=${BANDWIDTH}mb, delay=${DELAY}ms"
    exit 0
fi
