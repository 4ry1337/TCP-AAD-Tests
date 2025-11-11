#!/usr/bin/env bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "${SCRIPT_DIR}/config.sh"
source "${SCRIPT_DIR}/scripts/utils.sh" 2>/dev/null || true

ssh "${SERVER_USER}@${SERVER_IP}" "tc qdisc del dev ${SERVER_WIFI_IFACE} root 2>/dev/null" 2>/dev/null

exit 0
