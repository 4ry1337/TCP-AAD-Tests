# Quick Start Guide

## Setup (One-time)

1. **Configure settings** - Edit `config.sh`:
   ```bash
   SERVER_IP="192.168.1.100"
   ROUTER_IP="192.168.1.1"
   SERVER_USER="youruser"
   ```

2. **Setup SSH keys**:
   ```bash
   ssh-copy-id user@server_ip
   ssh-copy-id root@router_ip
   ```

3. **Install dependencies**:
   ```bash
   # On both server and client
   sudo apt install iperf3 iproute2

   # On client (for analysis)
   pip install matplotlib numpy
   ```

## Running Experiments

### Phase 1: TCP-AAD Kernel

**On Server (boot into TCP-AAD kernel):**
```bash
./server_setup.sh
```

**On Client:**
```bash
./run_experiments.sh tcpaad
```

---

### Phase 2: Default Kernel

**On Server (reboot into default kernel):**
```bash
./server_setup.sh
```

**On Client:**
```bash
./run_experiments.sh default
```

---

## Analysis

**On Client:**
```bash
cd analysis
python analyze_results.py ../results/tcpaad
python analyze_results.py ../results/default
python compare_kernels.py
python plot_comparison.py
```

## Results

Find results in:
- `results/summary_tcpaad.csv` - TCP-AAD metrics
- `results/summary_default.csv` - Default metrics
- `results/comparison.csv` - Comparison table
- `results/plots/` - Visualizations

## Troubleshooting

**Test not starting?**
```bash
# Check logs
tail -f results/logs/experiment.log

# Verify SSH
ssh root@router_ip "echo OK"
ssh user@server_ip "echo OK"
```

**Server errors?**
```bash
# Kill old iperf3
ssh user@server_ip "pkill iperf3"

# Restart server
ssh user@server_ip "cd /path/to/project && ./server_setup.sh"
```

**Want to resume?** Just re-run the same command - completed tests are skipped automatically.

---

For detailed information, see `EXPERIMENTS.md`
