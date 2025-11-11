#!/usr/bin/env bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "${SCRIPT_DIR}/config.sh"
source "${SCRIPT_DIR}/scripts/utils.sh" 2>/dev/null || true

# Disable trap to prevent recursion when called from cleanup_on_error
trap - ERR INT TERM

# Remove all tc qdiscs from the WiFi interface
ssh "${SERVER_USER}@${SERVER_IP}" "sudo tc qdisc del dev ${SERVER_WIFI_IFACE} root 2>/dev/null"

exit 0
