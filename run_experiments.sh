#!/usr/bin/env bash

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [ $# -gt 1 ]; then
    echo "Usage: $0 [tcpaad|default]"
    exit 1
fi

export KERNEL_TYPE=${1:-"tcpaad"}

if [[ "$KERNEL_TYPE" != "tcpaad" && "$KERNEL_TYPE" != "default" ]]; then
    echo "Error: Kernel type must be 'tcpaad' or 'default'"
    exit 1
fi

source "${SCRIPT_DIR}/config.sh"
source "${SCRIPT_DIR}/scripts/utils.sh"

echo "TCP-AAD WiFi Experiment Suite"
echo "Kernel Type: ${KERNEL_TYPE}"
echo "Server: ${SERVER_IP} (WiFi, iperf3 server)"
echo "Client: ${CLIENT_IP} (Ethernet, iperf3 client)"
echo "Router: ${ROUTER_IP}"

ensure_dir "${RESULTS_DIR}/raw"
ensure_dir "${RESULTS_DIR}/metadata"
ensure_dir "${LOGS_DIR}"

# Verify dependencies
log_info "Starting pre-flight checks..."
verify_dependencies || exit 1
check_ssh "${ROUTER_USER}" "${ROUTER_IP}" "Router" "${ROUTER_SSH_OPTS}" || exit 1
check_ssh "${SERVER_USER}" "${SERVER_IP}" "Server" || exit 1

# Display server kernel version
SERVER_KERNEL=$(get_server_kernel)
log_info "Server kernel version: ${SERVER_KERNEL}"
TOTAL_TESTS=$(calculate_total_tests)
log_info "Total tests to run: ${TOTAL_TESTS}"
ESTIMATED_SECONDS=$((TOTAL_TESTS * (IPERF_TEST_DURATION + SETTLE_TIME + RATE_SLEEP_TIME)))
ESTIMATED_DURATION=$(format_duration ${ESTIMATED_SECONDS})
log_info "Estimated duration: ${ESTIMATED_DURATION}"

echo ""
read -p "Press Enter to start the experiments or Ctrl+C to cancel..."
echo ""

# Initialize counters
test_count=0
failed_count=0
start_time=$(date +%s)

# Main experiment loop
log_info "Starting experiments..."
echo ""

for rate in "${RATES[@]}"; do
    log_info "====== Rate: ${rate} (${RATE_MAP[$rate]}) ======"

    if ! "${SCRIPT_DIR}/scripts/set_router_rate.sh" "${rate}"; then
        log_error "Failed to set rate ${rate}, skipping this configuration"
        continue
    fi

    # Wait for router to settle on new rate
    sleep ${RATE_SLEEP_TIME}

    for bw in "${BANDWIDTHS[@]}"; do
        log_info "=== Bandwidth: ${bw}mb ==="

        for delay in "${DELAYS[@]}"; do
            log_info "== Delay: ${delay}ms =="

            for iter in $(seq 1 ${ITERATIONS}); do
                test_count=$((test_count + 1))

                # Generate filenames
                test_name="rate${rate}_bw${bw}_delay${delay}_iter${iter}"
                result_file="${RESULTS_DIR}/raw/${test_name}.json"
                metadata_file="${RESULTS_DIR}/metadata/${test_name}.json"
                test_log="${LOGS_DIR}/${test_name}.log"

                # Check if test already completed
                if [ -f "${result_file}" ] && [ -f "${metadata_file}" ] && [ -f "${test_log}" ]; then
                    log_info "Skipping ${test_name} (already completed)"
                    continue
                fi

                # Show progress
                show_progress ${test_count} ${TOTAL_TESTS} "${test_name}"

                # Start test log with header
                {
                    echo "================================================================================"
                    echo "Test: ${test_name}"
                    echo "Kernel: ${KERNEL_TYPE}"
                    echo "Timestamp: $(date -Iseconds)"
                    echo "Settings: BW=${bw} Delay=${delay} Rate=${rate} Iter=${iter}"
                    echo "================================================================================"
                    echo ""
                } > "${test_log}"

                if ! "${SCRIPT_DIR}/scripts/setup_tc.sh" "${bw}" "${delay}" 2>&1 | tee -a "${test_log}"; then
                    log_error "Failed to apply tc, skipping test ${test_name}" | tee -a "${test_log}"
                    failed_count=$((failed_count + 1))
                    continue
                fi

                # Capture pre-test metadata (errors non-fatal)
                {
                    echo "--- Pre-test Metadata ---"
                    "${SCRIPT_DIR}/scripts/capture_metadata.sh" "${metadata_file}" 2>&1 || true
                    echo ""
                } | tee -a "${test_log}"

                {
                    echo "--- Running iperf3 Test (${IPERF_TEST_DURATION}s) ---"
                    if ! iperf3 -c "${SERVER_IP}" -p "${IPERF_PORT}" -t "${IPERF_TEST_DURATION}" -J --get-server-output > "${result_file}" 2>&1; then
                        echo "ERROR: iperf3 test failed"
                        log_error "iperf3 test failed: ${test_name}"
                        failed_count=$((failed_count + 1))
                    else
                        echo "SUCCESS: iperf3 test completed"
                    fi
                    echo ""
                } | tee -a "${test_log}"

                {
                    echo "--- Cleanup ---"
                    "${SCRIPT_DIR}/scripts/cleanup_tc.sh" 2>&1
                    echo ""
                    echo "Test completed at: $(date -Iseconds)"
                    echo "================================================================================"
                } | tee -a "${test_log}"

                sleep ${SETTLE_TIME}
            done
        done
    done
done

echo ""
echo ""

end_time=$(date +%s)
elapsed_seconds=$((end_time - start_time))
elapsed_duration=$(format_duration ${elapsed_seconds})

echo "================================================================================"
echo "  Experiment Summary"
echo "================================================================================"
log_success "All experiments completed!"
echo ""
echo "  Total tests run: ${test_count}"
echo "  Successful: $((test_count - failed_count))"
echo "  Failed: ${failed_count}"
echo "  Duration: ${elapsed_duration}"
echo "  Results saved to: ${RESULTS_DIR}"
echo ""
echo "Next steps:"
echo "  1. Run analysis scripts: cd analysis && python analyze_results.py"
echo "  2. Generate comparison: python compare_kernels.py"
echo "================================================================================"

exit 0
