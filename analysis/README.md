## Scripts

### 1. analyze_results.py

Parses raw iperf3 JSON files and generates summary statistics.

**Usage:**
```bash
python analyze_results.py <results_dir> [output_csv]
```

**Examples:**
```bash
# Analyze TCP-AAD results
python analyze_results.py ../results/tcpaad ../results/summary_tcpaad.csv

# Analyze default results
python analyze_results.py ../results/default ../results/summary_default.csv
```

**Output CSV columns:**
- `bandwidth` - Bandwidth limit configuration
- `delay_ms` - Network delay in milliseconds
- `rate_index` - WiFi MCS rate index
- `iterations` - Number of test iterations
- `avg_throughput_mbps` - Mean throughput across iterations
- `std_throughput_mbps` - Standard deviation of throughput
- `min_throughput_mbps` - Minimum throughput observed
- `max_throughput_mbps` - Maximum throughput observed
- `avg_retransmits` - Average retransmission count
- `total_retransmits` - Total retransmissions across all iterations
- `packet_loss_pct` - Packet loss percentage

---

### 2. compare_kernels.py

Compares TCP-AAD and default kernel results, calculating improvement metrics.

**Usage:**
```bash
python compare_kernels.py [tcpaad_csv] [default_csv] [output_csv]
```

**Example:**
```bash
# Use default paths
python compare_kernels.py

# Or specify files explicitly
python compare_kernels.py ../results/summary_tcpaad.csv ../results/summary_default.csv ../results/comparison.csv
```

**Output:**
- `results/comparison.csv` - Detailed comparison table
- Console output with summary statistics including:
  - Overall improvement statistics
  - Best/worst cases
  - Breakdown by delay and bandwidth
  - Top 10 improvements and degradations

**Comparison CSV columns:**
- `bandwidth`, `delay_ms`, `rate_index` - Test configuration
- `default_throughput_mbps` - Default kernel throughput
- `tcpaad_throughput_mbps` - TCP-AAD kernel throughput
- `throughput_improvement_pct` - Percentage improvement
- `default_std_mbps`, `tcpaad_std_mbps` - Standard deviations
- `default_retransmits`, `tcpaad_retransmits` - Retransmission counts
- `retrans_reduction_pct` - Retransmission reduction percentage
- `default_loss_pct`, `tcpaad_loss_pct` - Packet loss rates

---

### 3. plot_comparison.py

Generates visualization plots for comparison analysis.

**Requirements:**
```bash
pip install matplotlib numpy
```

**Usage:**
```bash
python plot_comparison.py [comparison_csv]
```

**Example:**
```bash
# Use default path
python plot_comparison.py

# Or specify file
python plot_comparison.py ../results/comparison.csv
```

**Generated plots** (saved to `results/plots/`):

1. **throughput_delay_*.png** - Throughput comparison for each delay setting
   - Bar charts comparing default vs TCP-AAD
   - Grouped by bandwidth
   - One plot per delay value

2. **improvement_heatmap.png** - Heatmap of throughput improvements
   - Rows: delay values
   - Columns: bandwidth settings
   - Colors: improvement percentage (green = good, red = degradation)

3. **improvement_by_rate.png** - Bar chart of improvement by WiFi rate
   - Shows mean improvement for each MCS rate index
   - Error bars show standard deviation
   - Helps identify which rates benefit most

4. **retransmission_comparison.png** - Retransmission analysis
   - Compares default vs TCP-AAD retransmissions
   - Grouped by delay
   - Shows retransmission reduction

---

## Workflow

Typical analysis workflow:

```bash
cd analysis
python analyze_results.py ../results/tcpaad
python analyze_results.py ../results/default
python compare_kernels.py
python plot_comparison.py
```

## Dependencies

- matplotlib
- numpy

## Notes
- All scripts handle missing data gracefully
- Progress and warnings are printed to stderr
- CSV files use standard comma-separated format
- Plots use 150 DPI for publication quality

## Troubleshooting

**"No valid test results found"**
- Check that raw JSON files exist in `results/*/raw/`
- Verify JSON files are not empty or corrupted

**"No default data for configuration"**
- Ensure both TCP-AAD and default tests ran with identical parameters
- Check that both summary CSV files were generated
