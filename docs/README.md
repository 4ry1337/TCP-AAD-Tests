# TCP-AAD Formal Verification with SPIN/Promela

This project provides formal verification of the TCP-AAD (Aggregation-Aware Delayed Acknowledgment) algorithm using the SPIN model checker and Promela specification language.

## Overview

The project verifies three models:
1. **tcp_basic.pml** - Baseline TCP with immediate ACKs
2. **tcp_default_dack.pml** - Standard Linux delayed ACK (RFC 1122)
3. **tcp_aad.pml** - Adaptive delayed ACK algorithm

### Key Features

- ✅ Complete Promela models of TCP acknowledgment mechanisms
- ✅ 20+ LTL properties (safety, liveness, correctness)
- ✅ Automated verification scripts
- ✅ Comparative analysis tools
- ✅ LaTeX table generation for academic papers

## Prerequisites

### Required Software

1. **SPIN Model Checker** (version 6.5.0 or later)
   ```bash
   # Ubuntu/Debian
   sudo apt-get install spin

   # macOS
   brew install spin

   # From source
   wget http://spinroot.com/spin/Src/spin652.tar.gz
   tar -xzf spin652.tar.gz
   cd Spin/Src*
   make
   sudo cp spin /usr/local/bin/
   ```

2. **GCC Compiler**
   ```bash
   # Ubuntu/Debian
   sudo apt-get install build-essential

   # macOS (Xcode Command Line Tools)
   xcode-select --install
   ```

3. **Python 3.7+** (for analysis scripts)
   ```bash
   python3 --version
   ```

### Verify Installation

```bash
# Check SPIN
spin -V
# Should output: Spin Version 6.5.x or later

# Check GCC
gcc --version

# Check Python
python3 --version
```

## Quick Start

### 1. Basic Model Check (5 minutes)

Run quick verification on all models:

```bash
cd formal_methods/scripts
./verify_all.sh quick
```

This will verify:
- Basic TCP properties (no deadlock, eventual ACK)
- DACK properties (max 2 delayed segments, completion)
- TCP-AAD properties (ATO bounds, adaptive behavior)

### 2. View Results

```bash
# Check the latest report
ls -lt ../results/verification_outputs/verification_report_*.txt | head -1

# Analyze results
python3 analyze_results.py ../results/verification_outputs/verification_report_*.txt
```

### 3. Manual Verification (Advanced)

Verify a specific property on a specific model:

```bash
cd formal_methods/models

# Compile the model with LTL property
spin -a -N ato_bounded_aad tcp_aad.pml

# Build the verifier
gcc -DMEMLIM=2048 -O2 -o pan pan.c

# Run verification
./pan -a

# If errors found, view counter-example
spin -t -p tcp_aad.pml
```

## Project Structure

```
formal_methods/
├── models/
│   ├── tcp_basic.pml           # Basic TCP model
│   ├── tcp_default_dack.pml    # Default DACK model
│   └── tcp_aad.pml             # TCP-AAD model
├── properties/
│   └── properties.ltl          # LTL property specifications
├── scripts/
│   ├── verify_all.sh           # Automated verification script
│   └── analyze_results.py      # Results analysis script
├── docs/
│   ├── README.md               # This file
│   ├── TIME_ABSTRACTION.md     # Time modeling documentation
│   └── VERIFICATION_REPORT.md  # Detailed findings
├── paper/
│   ├── main.tex                # LaTeX paper
│   └── sections/               # Paper sections
└── results/
    └── verification_outputs/   # Verification results
```

## Verification Modes

### Quick Mode (5-10 minutes)

Verifies essential properties:
```bash
./verify_all.sh quick
```

Properties verified:
- All segments acknowledged
- No deadlock
- ATO bounds
- Connection completion

### Full Mode (1-2 hours)

Verifies all properties including:
```bash
./verify_all.sh full
```

Additional properties:
- Integer overflow checks
- Timer correctness
- IAT reset periodicity
- Adaptive behavior verification

## Understanding Results

### Successful Verification

```
Verifying: tcp_aad - ATO bounded
  [1/4] Compiling model...
    ✓ Compilation successful
  [2/4] Building verifier...
    ✓ Build successful
  [3/4] Running verification...
    ✓ Verification completed
    ✓ Property HOLDS
  [4/4] Extracting statistics...

States Explored: 12,534
Transitions: 45,231
Memory Used: 15.2 MB
```

This means the property **holds** - no violations found.

### Property Violation

```
Verifying: tcp_default_dack - max_two_delayed
  ...
    ✗ Property VIOLATED
  [4/4] Extracting counter-example...
    ⚠ Counter-example saved

Counter-example: tcp_default_dack_max_two_delayed.counterexample
```

When a property is violated:
1. A counter-example trace is saved
2. Use `spin -t -p model.pml` to replay the trace
3. Analyze the trace to understand the bug
4. Fix the model or refine the property

## Common Issues & Solutions

### Issue: "pan: out of memory"

**Solution**: Use bitstate hashing (trades completeness for memory):
```bash
gcc -DMEMLIM=4096 -DBITSTATE -O2 -o pan pan.c
./pan -k3 -w28  # 3-bit hash, 2^28 states
```

### Issue: "pan: search was truncated"

**Solution**: The state space is too large. Options:
1. Reduce `MAX_SEGMENTS` in the model
2. Use abstraction (reduce channel sizes)
3. Use bitstate hashing
4. Verify properties separately

### Issue: Verification timeout

**Solution**: Increase timeout or use partial verification:
```bash
timeout 600 ./pan -a  # 10 minute timeout
```

### Issue: Compilation errors

**Solution**: Check SPIN version and GCC compatibility:
```bash
spin -V
gcc --version

# Try alternative compile options
gcc -O2 -o pan pan.c  # Without memory limit
```

## Time Abstraction

**Important**: These models use logical time, not real time.

- 1 time unit = 1ms (abstracted)
- ATO ≤ 500 time units = 500ms
- IAT filter < 2 units = 0.2ms
- Reset period = 1000 units = 1 second

See [TIME_ABSTRACTION.md](TIME_ABSTRACTION.md) for detailed explanation.

## Model Parameters

You can adjust these in the `.pml` files:

```promela
#define MAX_SEGMENTS 10      // Number of segments to send
#define CHANNEL_SIZE 20      // Buffer size
#define MAX_ATO 500          // Maximum ATO (ms)
#define RESET_PERIOD 1000    // IAT_min reset period (ms)
```

**Note**: Larger values increase state space exponentially!

## Comparative Analysis

To compare DACK vs AAD:

```bash
# Run full verification on both
./verify_all.sh full

# Analyze and compare
python3 analyze_results.py ../results/verification_outputs/verification_report_*.txt
```

The analysis script generates:
- Markdown comparison table
- LaTeX table for paper
- JSON data for further processing

## Contributing to the Models

### Adding a New Property

1. Add to `properties/properties.ltl`:
```promela
/* S17: My new property */
ltl my_property { [](some_condition -> <>some_result) }
```

2. Add to verification script `verify_all.sh`:
```bash
QUICK_PROPS_AAD+=(
    "my_property:My property description"
)
```

3. Run verification:
```bash
./verify_all.sh quick
```

### Modifying a Model

1. Edit the `.pml` file
2. Test manually first:
```bash
spin -a model.pml
gcc -o pan pan.c
./pan
```
3. Run full verification suite
4. Document changes in commit message

## References

- [SPIN Model Checker](http://spinroot.com/)
- [Promela Language Reference](http://spinroot.com/spin/Man/promela.html)
- [LTL Formula Patterns](http://patterns.projects.cs.ksu.edu/documentation/patterns/ltl.shtml)
- [TCP-AAD Paper](../paper/main.pdf)

## Troubleshooting

For common issues, check:
1. SPIN installation: `spin -V`
2. GCC installation: `gcc --version`
3. File permissions: `chmod +x scripts/*.sh`
4. Python version: `python3 --version`

For more help:
- Check [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md)
- Review [TIME_ABSTRACTION.md](TIME_ABSTRACTION.md)
- See example runs in `results/`

## License

This verification framework is provided for academic and educational purposes.

## Citation

If you use this work, please cite:

```bibtex
@thesis{tcp_aad_verification,
  author = {Your Name},
  title = {Formal Verification of TCP-AAD using SPIN},
  year = {2025},
  school = {Innopolis University}
}
```
