# Getting Started with TCP-AAD Formal Verification

Welcome! This guide will help you get started with verifying the TCP-AAD algorithm using SPIN.

## Quick Start (5 minutes)

### Step 1: Install SPIN

**Ubuntu/Debian**:
```bash
sudo apt-get update
sudo apt-get install spin gcc
```

**macOS**:
```bash
brew install spin
```

**Verify installation**:
```bash
spin -V
# Should show: Spin Version 6.5.x or later
```

### Step 2: Run Your First Verification

```bash
cd formal_methods/scripts
./verify_all.sh quick
```

This will:
- Compile all three models (Basic TCP, DACK, TCP-AAD)
- Verify essential safety and liveness properties
- Generate a verification report
- Take approximately 5-10 minutes

### Step 3: View Results

```bash
# View the report
cat ../results/verification_outputs/verification_report_*.txt

# Or analyze with Python
python3 analyze_results.py ../results/verification_outputs/verification_report_*.txt
```

## What's Included

### Models (`.pml` files)

1. **tcp_basic.pml** - Baseline TCP with immediate ACKs
   - Simple sender/receiver interaction
   - No delayed ACK logic
   - ~2,000 states

2. **tcp_default_dack.pml** - Standard Linux delayed ACK
   - Implements RFC 1122 DACK (every 2 segments, 500ms timeout)
   - ~15,000 states
   - Matches Linux kernel behavior

3. **tcp_aad.pml** - TCP-AAD adaptive algorithm
   - IAT tracking and adaptive timeout calculation
   - Frame aggregation detection
   - Periodic IAT_min reset
   - ~20,000 states

### Properties (`properties.ltl`)

20+ LTL temporal logic properties:

**Safety** (bad things never happen):
- ATO bounded ≤ 500ms
- No integer overflow
- Valid ACK ordering

**Liveness** (good things eventually happen):
- All segments eventually ACKed
- System makes progress
- IAT periodically reset

**Correctness** (protocol requirements):
- Connection completes
- Adaptive behavior works
- Timer set correctly

### Scripts

- `verify_all.sh` - Automated verification runner
- `analyze_results.py` - Results parser and comparison tool

### Documentation

- `README.md` - Full documentation
- `TIME_ABSTRACTION.md` - How we model time in untimed SPIN
- `VERIFICATION_REPORT.md` - Template for results

### Paper

- `paper/main.tex` - LaTeX academic paper
- `paper/sections/` - Individual sections
- `paper/references.bib` - Bibliography

## Usage Examples

### Verify a Specific Model and Property

```bash
cd models

# Verify that ATO is bounded in TCP-AAD
spin -a -N ato_bounded_aad tcp_aad.pml
gcc -O2 -o pan pan.c
./pan -a

# Check results
grep "errors:" pan.out
```

### Run Full Verification (1-2 hours)

```bash
cd scripts
./verify_all.sh full
```

This verifies ALL properties including:
- Overflow checks
- Timer correctness
- Comparison properties

### Compare DACK vs AAD

After running verification:

```bash
python3 analyze_results.py results/verification_outputs/verification_report_*.txt
```

Outputs:
- Markdown comparison table
- LaTeX table for paper
- JSON data file
- Performance metrics

## Understanding Your Results

### ✓ Property HOLDS (Good!)

```
States Explored: 12,534
Transitions: 45,231
Memory Used: 15.2 MB
Result: PASS
errors: 0
```

Meaning: The property is verified for all reachable states.

### ✗ Property VIOLATED (Found a bug!)

```
Result: FAIL
errors: 1
Counter-example: tcp_aad_ato_bounded.counterexample
```

Meaning: SPIN found a trace where the property is violated.

**What to do**:
1. Examine counter-example: `spin -t -p tcp_aad.pml`
2. Understand the bug: trace shows the sequence of events
3. Fix the model or refine the property
4. Re-verify

### ⚠ Verification TIMEOUT

```
Result: TIMEOUT
```

Meaning: State space too large (> 300 seconds).

**Solutions**:
- Reduce `MAX_SEGMENTS` in model
- Use bitstate hashing: `gcc -DBITSTATE -o pan pan.c`
- Verify properties separately

## Next Steps

### For Beginners

1. ✅ Read `docs/README.md` - comprehensive guide
2. ✅ Study `models/tcp_basic.pml` - simplest model
3. ✅ Run `verify_all.sh quick` - see it work
4. ✅ Read `docs/TIME_ABSTRACTION.md` - understand time modeling

### For Advanced Users

1. ✅ Modify models to test different scenarios
2. ✅ Add new LTL properties
3. ✅ Compare with real Linux kernel behavior
4. ✅ Write the formal verification paper

### For Your Course Project

1. ✅ Run all verifications and document results
2. ✅ Analyze counter-examples if any found
3. ✅ Create comparison tables (DACK vs AAD)
4. ✅ Write report using provided LaTeX template
5. ✅ Present findings: "We formally verified that TCP-AAD..."

## Common Questions

**Q: Do I need to understand SPIN deeply?**
A: No! The models are already written. You can run verifications and analyze results. Understanding comes with use.

**Q: What if verification finds bugs?**
A: Great! That's the point of formal verification. Document the bug, understand it, and either fix the model or note it as a limitation.

**Q: How accurate is the time abstraction?**
A: It captures qualitative behavior (does TCP-AAD adapt?) not quantitative performance (exact throughput). Perfect for protocol correctness verification.

**Q: Can I use this for other protocols?**
A: Yes! The methodology (logical time, LTL properties, verification scripts) is reusable for any timing-based protocol.

**Q: How do I cite this work?**
A: See `references.bib` for citation format.

## Troubleshooting

### Error: "spin: command not found"

Solution: Install SPIN (see Step 1 above)

### Error: "gcc: command not found"

Solution: `sudo apt-get install build-essential`

### Error: "out of memory"

Solution: Use bitstate hashing or reduce state space

```bash
gcc -DMEMLIM=4096 -DBITSTATE -o pan pan.c
./pan -k3 -w28
```

### Error: "property syntax error"

Solution: Check LTL formula syntax in `properties.ltl`

## Resources

- SPIN Manual: http://spinroot.com/spin/Man/
- Promela Reference: http://spinroot.com/spin/Man/promela.html
- LTL Patterns: http://patterns.projects.cs.ksu.edu/
- Our Documentation: `docs/README.md`

## Support

- Check documentation in `docs/`
- Review examples in `models/`
- See verification outputs in `results/`

## License & Citation

This framework is provided for academic use.

If you use this work, please cite:
- Albert's thesis on TCP-AAD implementation
- This formal verification study
- SPIN model checker

---

**Ready to verify?**

```bash
cd formal_methods/scripts
./verify_all.sh quick
```

**Happy verifying! 🚀**
