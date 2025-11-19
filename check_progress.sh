#!/usr/bin/env bash

source "${SCRIPT_DIR}/config.sh"

echo "TCP-AAD Experiment Progress"

TOTAL_EXPECTED=$((${#BANDWIDTHS[@]} * ${#DELAYS[@]} * ${#RATES[@]} * ${ITERATIONS}))

echo "Expected tests per kernel: ${TOTAL_EXPECTED}"

# Check TCP-AAD results
if [ -d "${SCRIPT_DIR}/results/tcpaad/raw" ]; then
    TCPAAD_COUNT=$(find "${SCRIPT_DIR}/results/tcpaad/raw" -name "*.json" -type f 2>/dev/null | wc -l)
    TCPAAD_PCT=$((TCPAAD_COUNT * 100 / TOTAL_EXPECTED))
    echo "TCP-AAD Tests:"
    echo "  Completed: ${TCPAAD_COUNT} / ${TOTAL_EXPECTED} (${TCPAAD_PCT}%)"

    if [ $TCPAAD_COUNT -lt $TOTAL_EXPECTED ]; then
        REMAINING=$((TOTAL_EXPECTED - TCPAAD_COUNT))
        EST_TIME=$((REMAINING * 40 / 60))
        echo "  Remaining: ${REMAINING} tests (~${EST_TIME} minutes)"
    else
        echo "  Status: Complete"
    fi
else
    echo "TCP-AAD Tests: Not started"
fi

echo ""

# Check Default results
if [ -d "${SCRIPT_DIR}/results/default/raw" ]; then
    DEFAULT_COUNT=$(find "${SCRIPT_DIR}/results/default/raw" -name "*.json" -type f 2>/dev/null | wc -l)
    DEFAULT_PCT=$((DEFAULT_COUNT * 100 / TOTAL_EXPECTED))
    echo "Default Tests:"
    echo "  Completed: ${DEFAULT_COUNT} / ${TOTAL_EXPECTED} (${DEFAULT_PCT}%)"

    if [ $DEFAULT_COUNT -lt $TOTAL_EXPECTED ]; then
        REMAINING=$((TOTAL_EXPECTED - DEFAULT_COUNT))
        EST_TIME=$((REMAINING * 40 / 60))  # 35 seconds per test
        echo "  Remaining: ${REMAINING} tests (~${EST_TIME} minutes)"
    else
        echo "  Status: ✓ Complete"
    fi
else
    echo "Default Tests: Not started"
fi

echo ""

# Check for summary files
echo "Analysis Status:"
if [ -f "${SCRIPT_DIR}/results/summary_tcpaad.csv" ]; then
    echo "TCP-AAD summary generated"
else
    echo "TCP-AAD summary not generated"
fi

if [ -f "${SCRIPT_DIR}/results/summary_default.csv" ]; then
    echo "  ✓ Default summary generated"
else
    echo "  ✗ Default summary not generated"
fi

if [ -f "${SCRIPT_DIR}/results/comparison.csv" ]; then
    echo "  ✓ Comparison generated"
else
    echo "  ✗ Comparison not generated"
fi

if [ -d "${SCRIPT_DIR}/results/plots" ] && [ "$(ls -A ${SCRIPT_DIR}/results/plots 2>/dev/null)" ]; then
    PLOT_COUNT=$(find "${SCRIPT_DIR}/results/plots" -name "*.png" -type f 2>/dev/null | wc -l)
    echo "  ✓ Plots generated (${PLOT_COUNT} files)"
else
    echo "  ✗ Plots not generated"
fi

echo ""

# Check disk usage
if [ -d "${SCRIPT_DIR}/results" ]; then
    DISK_USAGE=$(du -sh "${SCRIPT_DIR}/results" 2>/dev/null | cut -f1)
    echo "Disk Usage: ${DISK_USAGE}"
fi

echo ""

echo ""
if [ $TCPAAD_COUNT -eq $TOTAL_EXPECTED ] && [ $DEFAULT_COUNT -eq $TOTAL_EXPECTED ]; then
    if [ ! -f "${SCRIPT_DIR}/results/comparison.csv" ]; then
        echo "Next step: Run analysis"
        echo "  cd analysis && python compare_kernels.py"
    else
        echo "All tests and analysis complete! ✓"
        echo "Check results/comparison.csv and results/plots/ for results"
    fi
elif [ $TCPAAD_COUNT -eq $TOTAL_EXPECTED ]; then
    echo "Next step: Run default kernel tests"
    echo "  1. Reboot server into default kernel"
    echo "  2. ./run_experiments.sh default"
elif [ $TCPAAD_COUNT -gt 0 ]; then
    echo "TCP-AAD tests in progress..."
    echo "Run './check_progress.sh' again to see updated status"
else
    echo "Next step: Start TCP-AAD tests"
    echo "  1. Boot server into TCP-AAD kernel"
    echo "  2. On server: ./server_setup.sh"
    echo "  3. On client: ./run_experiments.sh tcpaad"
fi
