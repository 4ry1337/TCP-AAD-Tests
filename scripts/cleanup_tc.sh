#!/usr/bin/env bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "${SCRIPT_DIR}/config.sh"
source "${SCRIPT_DIR}/scripts/utils.sh" 2>/dev/null || true

sudo tc qdisc del dev ${CLIENT_IFACE} root 2>/dev/null

# Note: tc qdisc del will return non-zero if no qdisc exists, which is fine
# We suppress errors since this is a cleanup operation

exit 0
