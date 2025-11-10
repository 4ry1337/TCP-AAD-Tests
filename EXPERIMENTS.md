# TCP-AAD WiFi Experiments - User Guide

This guide explains how to run the TCP-AAD WiFi experiments comparing TCP-AAD kernel with default kernel.

## Overview

The experiment suite conducts comprehensive tests comparing TCP-AAD (Aggregation-Aware Delayed ACK) with standard TCP over WiFi under various network conditions.

### Test Parameters

- **Bandwidth limits**: 10mb, 20mb, 50mb, nolim (unlimited)
- **Network delays**: 10ms, 50ms, 100ms
- **WiFi rate indices**: 34-37, 44-47, 94-97, 104-107 (16 rates total)
- **Iterations**: 3 per configuration (configurable)
- **Total tests**: 4 × 3 × 16 × 3 = **576 tests per kernel**
- **Grand total**: **1152 tests** (both kernels)

### Test Setup

**Server Machine** (dual-boot):
- Kernel 1: TCP-AAD modified kernel
- Kernel 2: Default/vanilla kernel
- Connected via WiFi to router
- Runs iperf3 server

**Client Machine**:
- Default kernel only
- Connected via Ethernet
- Runs test orchestration and iperf3 client

**Router**:
- OpenWRT with `/root/fixrate1` script for rate control
- SSH accessible from client
- **Note**: Older OpenWRT routers may require ssh-rsa algorithm (already configured in `config.sh`)


## Running Experiments

On server machine, boot into **TCP-AAD kernel** and run:
```bash
./server_setup.sh
```

This starts iperf3 server. Keep this terminal open.

On client machine:
```bash
./run_experiments.sh tcpaad
```

This will:
- Run 576 tests (estimated 7-8 hours)
- Save results to `results/tcpaad/`
- Display progress bar
- Log all operations

**Note**: You can safely interrupt with Ctrl+C and resume later. Already completed tests won't be re-run if the output files exist.

## Analyzing Results

### Generate Summary CSVs

On client machine:
```bash
cd analysis
python analyze_results.py ../results/tcpaad ../results/summary_tcpaad.csv
python analyze_results.py ../results/default ../results/summary_default.csv
```

This creates:
- `results/summary_tcpaad.csv` - Aggregated TCP-AAD metrics
- `results/summary_default.csv` - Aggregated default metrics

### Generate Comparison

```bash
python compare_kernels.py
```

Output:
- `results/comparison.csv` - Side-by-side comparison
- Console output with detailed statistics including:
  - Mean/median improvement
  - Best/worst cases
  - Breakdown by delay and bandwidth

### Generate Plots

```bash
python plot_comparison.py
```

Creates visualizations in `results/plots/`:
- `throughput_delay_*.png` - Throughput by delay
- `improvement_heatmap.png` - Improvement heatmap
- `improvement_by_rate.png` - Improvement by rate index
- `retransmission_comparison.png` - Retransmission analysis

## Troubleshooting

### Test failures

Check logs:
```bash
tail -f results/logs/experiment.log
```

### SSH connection issues

**Router connection errors** (e.g., "no matching host key type found"):

OpenWRT routers often require older ssh-rsa algorithm. This is already configured in `config.sh` via `ROUTER_SSH_OPTS`.

To manually test router connection:
```bash
ssh -o HostKeyAlgorithms=+ssh-rsa -o PubkeyAcceptedAlgorithms=+ssh-rsa root@router_ip
```

To setup SSH keys for router:
```bash
ssh-copy-id -o HostKeyAlgorithms=+ssh-rsa -o PubkeyAcceptedAlgorithms=+ssh-rsa root@router_ip
```

### iperf3 port already in use

Kill existing iperf3:
```bash
pkill iperf3
```

## Expected Results

Based on Albert's thesis, you should expect:

- **Best improvements**: 50ms delay, moderate-to-high bandwidth, higher MCS rates
- **Average improvement**: ~9% throughput increase
- **Limited benefits**: Very low bandwidth or very high delay scenarios
- **Reduced retransmissions**: Especially at higher delays

## Tips for Success

1. **Network stability**: Ensure WiFi environment is stable (no interference)
2. **Server positioning**: Keep server at consistent distance from router
3. **Avoid interference**: Don't move equipment or start new WiFi traffic during tests
4. **Monitor progress**: Keep an eye on the progress bar and logs
5. **Backup results**: Copy results directory periodically
6. **Document conditions**: Note any environmental factors (time of day, other WiFi networks, etc.)

## Time Estimates

- Single test: ~30 seconds
- Single configuration (3 iterations): ~2 minutes
- Full test suite (576 tests): **7-8 hours**
- Both kernels: **14-16 hours total**

Schedule accordingly - you may want to run tests overnight!

## Questions or Issues?

Refer to:
- `README.md` for project overview
- `Albert_s_thesis.pdf` for TCP-AAD mechanism details
- Experiment logs in `results/logs/`
