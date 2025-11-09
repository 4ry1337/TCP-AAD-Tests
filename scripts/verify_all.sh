#!/bin/bash

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Directories
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
MODELS_DIR="$PROJECT_ROOT/models"
RESULTS_DIR="$PROJECT_ROOT/results/verification_outputs"

# Create results directory
mkdir -p "$RESULTS_DIR"

# Configuration
MODE="${1:-quick}"
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
REPORT_FILE="$RESULTS_DIR/verification_report_${TIMESTAMP}.txt"

# SPIN options
SPIN_BASIC="-a"
SPIN_SAFETY="-a -DSAFETY"
SPIN_FULL="-a -DNOREDUCE"

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}TCP DACK/AAD Formal Verification${NC}"
echo -e "${BLUE}========================================${NC}"
echo "Mode: $MODE"
echo "Timestamp: $TIMESTAMP"
echo "Report: $REPORT_FILE"
echo ""

# Initialize report
cat > "$REPORT_FILE" << EOF
TCP DACK/AAD Formal Verification Report
Generated: $(date)
Mode: $MODE

========================================
EOF

# Function to run verification
verify_model() {
    local model_file=$1
    local model_name=$2
    local property=$3
    local property_name=$4

    echo -e "${YELLOW}Verifying: $model_name - $property_name${NC}"

    local output_file="$RESULTS_DIR/${model_name}_${property_name}_${TIMESTAMP}"

    # Compile the model
    echo "  [1/4] Compiling model..."
    if spin $SPIN_BASIC "$model_file" > "${output_file}.spin.log" 2>&1; then
        echo -e "    ${GREEN}✓ Compilation successful${NC}"
    else
        echo -e "    ${RED}✗ Compilation failed${NC}"
        cat "${output_file}.spin.log"
        return 1
    fi

    # Build pan verifier
    echo "  [2/4] Building verifier..."
    if gcc -DMEMLIM=4096 -DCOLLAPSE -O2 -o "${output_file}.pan" pan.c > "${output_file}.gcc.log" 2>&1; then
        echo -e "    ${GREEN}✓ Build successful${NC}"
    else
        echo -e "    ${RED}✗ Build failed${NC}"
        cat "${output_file}.gcc.log"
        return 1
    fi

    # Run verification
    echo "  [3/4] Running verification..."
    if timeout 300 "${output_file}.pan" -a -N "$property" > "${output_file}.result" 2>&1; then
        echo -e "    ${GREEN}✓ Verification completed${NC}"

        # Check for errors
        if grep -q "errors: 0" "${output_file}.result"; then
            echo -e "    ${GREEN}✓ Property HOLDS${NC}"
            RESULT="PASS"
        else
            echo -e "    ${RED}✗ Property VIOLATED${NC}"
            RESULT="FAIL"
            # Extract counter-example if exists
            if [ -f "${model_name}.pml.trail" ]; then
                echo "  [4/4] Extracting counter-example..."
                spin -t -p "$model_file" > "${output_file}.counterexample" 2>&1
                echo -e "    ${YELLOW}Counter-example saved${NC}"
            fi
        fi
    else
        echo -e "    ${YELLOW}⚠ Verification timeout (300s)${NC}"
        RESULT="TIMEOUT"
    fi

    # Extract statistics
    echo "  [4/4] Extracting statistics..."
    STATES=$(grep "states, stored" "${output_file}.result" | awk '{print $1}' || echo "N/A")
    TRANSITIONS=$(grep "states, matched" "${output_file}.result" | awk '{print $1}' || echo "N/A")
    MEMORY=$(grep "total actual memory usage" "${output_file}.result" | awk '{print $1}' || echo "N/A")

    # Append to report
    cat >> "$REPORT_FILE" << EOF

----------------------------------------
Model: $model_name
Property: $property_name
Result: $RESULT
States Explored: $STATES
Transitions: $TRANSITIONS
Memory Used: $MEMORY MB
Output: ${output_file}.result
EOF

    if [ "$RESULT" == "FAIL" ]; then
        echo "Counter-example: ${output_file}.counterexample" >> "$REPORT_FILE"
    fi

    # Cleanup
    rm -f pan pan.* "${output_file}.pan" _spin_nvr.tmp

    echo ""
}

# Quick mode properties
QUICK_PROPS_BASIC=(
    "all_acked:All segments acknowledged"
    "progress:Progress check"
)

QUICK_PROPS_DACK=(
    "max_two_delayed:Max 2 delayed segments"
    "eventual_ack_dack:Eventual acknowledgment"
    "completion:Connection completion"
)

QUICK_PROPS_AAD=(
    "ato_bounded:ATO bounded"
    "eventual_ack_aad:Eventual acknowledgment"
    "adaptive_used:Adaptive ACKs used"
    "completion_aad:Connection completion"
)

# Full mode additional properties
FULL_PROPS_DACK=(
    "acks_sent_progress:ACKs sent progress"
)

FULL_PROPS_AAD=(
    "iat_min_valid:IAT_min valid"
    "acks_progress:ACKs progress"
    "iat_reset:IAT reset periodic"
)

# Run verifications
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}1. TCP Basic Model${NC}"
echo -e "${BLUE}========================================${NC}"
for prop in "${QUICK_PROPS_BASIC[@]}"; do
    IFS=':' read -r prop_name prop_desc <<< "$prop"
    verify_model "$MODELS_DIR/tcp_basic.pml" "tcp_basic" "$prop_name" "$prop_desc"
done

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}2. TCP Default DACK Model${NC}"
echo -e "${BLUE}========================================${NC}"
for prop in "${QUICK_PROPS_DACK[@]}"; do
    IFS=':' read -r prop_name prop_desc <<< "$prop"
    verify_model "$MODELS_DIR/tcp_default_dack.pml" "tcp_default_dack" "$prop_name" "$prop_desc"
done

if [ "$MODE" == "full" ]; then
    for prop in "${FULL_PROPS_DACK[@]}"; do
        IFS=':' read -r prop_name prop_desc <<< "$prop"
        verify_model "$MODELS_DIR/tcp_default_dack.pml" "tcp_default_dack" "$prop_name" "$prop_desc"
    done
fi

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}3. TCP-AAD Model${NC}"
echo -e "${BLUE}========================================${NC}"
for prop in "${QUICK_PROPS_AAD[@]}"; do
    IFS=':' read -r prop_name prop_desc <<< "$prop"
    verify_model "$MODELS_DIR/tcp_aad.pml" "tcp_aad" "$prop_name" "$prop_desc"
done

if [ "$MODE" == "full" ]; then
    for prop in "${FULL_PROPS_AAD[@]}"; do
        IFS=':' read -r prop_name prop_desc <<< "$prop"
        verify_model "$MODELS_DIR/tcp_aad.pml" "tcp_aad" "$prop_name" "$prop_desc"
    done
fi

# Generate summary
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}Verification Summary${NC}"
echo -e "${BLUE}========================================${NC}"

TOTAL=$(grep -c "^Result:" "$REPORT_FILE" || echo "0")
PASSED=$(grep -c "^Result: PASS" "$REPORT_FILE" || echo "0")
FAILED=$(grep -c "^Result: FAIL" "$REPORT_FILE" || echo "0")
TIMEOUT=$(grep -c "^Result: TIMEOUT" "$REPORT_FILE" || echo "0")

echo "Total Properties Verified: $TOTAL"
echo -e "${GREEN}Passed: $PASSED${NC}"
echo -e "${RED}Failed: $FAILED${NC}"
echo -e "${YELLOW}Timeout: $TIMEOUT${NC}"
echo ""
echo "Full report: $REPORT_FILE"

# Append summary to report
cat >> "$REPORT_FILE" << EOF

========================================
SUMMARY
========================================
Total Properties: $TOTAL
Passed: $PASSED
Failed: $FAILED
Timeout: $TIMEOUT

Verification completed: $(date)
EOF

echo -e "${GREEN}Verification complete!${NC}"
