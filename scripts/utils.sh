#!/usr/bin/env bash

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log_info() {
    echo -e "${BLUE}[INFO]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1" | tee -a "${RESULTS_DIR}/logs/experiment.log"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1" | tee -a "${RESULTS_DIR}/logs/experiment.log"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1" | tee -a "${RESULTS_DIR}/logs/experiment.log"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1" | tee -a "${RESULTS_DIR}/logs/experiment.log"
}

command_exists() {
    command -v "$1" >/dev/null 2>&1
}

check_ssh() {
    local user=$1
    local host=$2
    local name=$3
    local ssh_opts=$4

    log_info "Checking SSH connectivity to ${name} (${user}@${host})..."
    if ssh ${ssh_opts} "${user}@${host}" "exit" 2>/dev/null; then
        log_success "SSH connection to ${name} successful"
        return 0
    else
        log_error "Cannot connect to ${name} via SSH"
        return 1
    fi
}

verify_dependencies() {
    log_info "Verifying dependencies..."

    local missing_deps=()

    if ! command_exists iperf3; then
        missing_deps+=("iperf3")
    fi

    if ! command_exists ssh; then
        missing_deps+=("ssh")
    fi

    if [ ${#missing_deps[@]} -ne 0 ]; then
        log_error "Missing dependencies: ${missing_deps[*]}"
        return 1
    fi

    log_success "All dependencies found"
    return 0
}

# Helper function to execute SSH commands on router
router_ssh() {
    ssh ${ROUTER_SSH_OPTS} "${ROUTER_USER}@${ROUTER_IP}" "$@"
}

ensure_dir() {
    local dir=$1
    if [ ! -d "$dir" ]; then
        mkdir -p "$dir"
        log_info "Created directory: $dir"
    fi
}

show_progress() {
    local current=$1
    local total=$2
    local desc=$3
    local percent=$((current * 100 / total))
    local filled=$((percent / 2))
    local empty=$((50 - filled))

    printf "\r${BLUE}Progress:${NC} [%${filled}s%${empty}s] %d%% - %s" \
        "$(printf '#%.0s' $(seq 1 $filled))" \
        "$(printf ' %.0s' $(seq 1 $empty))" \
        "$percent" \
        "$desc"
}

calculate_total_tests() {
    local bw_count=${#BANDWIDTHS[@]}
    local delay_count=${#DELAYS[@]}
    local rate_count=${#RATES[@]}
    local iter_count=$ITERATIONS

    echo $((bw_count * delay_count * rate_count * iter_count))
}

format_duration() {
    local seconds=$1
    local hours=$((seconds / 3600))
    local minutes=$(((seconds % 3600) / 60))
    local secs=$((seconds % 60))

    printf "%02d:%02d:%02d" $hours $minutes $secs
}

validate_ip() {
    local ip=$1
    if [[ $ip =~ ^[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}$ ]]; then
        return 0
    else
        return 1
    fi
}

get_server_kernel() {
    ssh "${SERVER_USER}@${SERVER_IP}" "uname -r" 2>/dev/null
}

cleanup_on_error() {
    log_warning "Performing cleanup due to error..."
    "${SCRIPT_DIR}/scripts/cleanup_tc.sh" 2>/dev/null
    log_info "Cleanup completed"
}

trap cleanup_on_error ERR INT TERM
