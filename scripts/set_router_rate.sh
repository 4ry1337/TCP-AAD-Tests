#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "${SCRIPT_DIR}/config.sh"
source "${SCRIPT_DIR}/scripts/utils.sh"

# Check arguments
if [ $# -ne 1 ]; then
    log_error "Usage: $0 <rate_index>"
    exit 1
fi

RATE_INDEX=$1

if [[ ! " ${RATES[@]} " =~ " ${RATE_INDEX} " ]]; then
    log_error "Invalid rate index: ${RATE_INDEX}"
    log_error "Valid rates: ${RATES[*]}"
    exit 1
fi

log_info "Setting WiFi rate to index ${RATE_INDEX} (${RATE_MAP[$RATE_INDEX]})"

if ssh ${ROUTER_SSH_OPTS} "${ROUTER_USER}@${ROUTER_IP}" "/root/fixrate1 ${RATE_INDEX}" 2>/dev/null; then
    log_success "WiFi rate set to ${RATE_INDEX}"
    exit 0
else
    log_error "Failed to set WiFi rate on router"
    exit 1
fi
