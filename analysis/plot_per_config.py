#!/usr/bin/env python3

import json
import sys
import os
from pathlib import Path
from collections import defaultdict
import re
import numpy as np

try:
    import matplotlib.pyplot as plt
    import matplotlib
    matplotlib.use('Agg')  # Non-interactive backend for batch processing
except ImportError:
    print("Error: This script requires matplotlib", file=sys.stderr)
    print("Install with: pip install matplotlib", file=sys.stderr)
    sys.exit(1)


def parse_filename(filename):
    """
    Parse test filename to extract parameters.
    Format: bw{X}_delay{Y}_rate{Z}_iter{N}.json
    """
    pattern = r'bw(\w+)_delay(\w+)_rate(\d+)_iter(\d+)\.json'
    match = re.match(pattern, filename)

    if not match:
        return None

    return {
        'bandwidth': match.group(1),
        'delay': match.group(2),
        'rate': int(match.group(3)),
        'iteration': int(match.group(4))
    }


def parse_iperf3_intervals(filepath):
    """
    Parse iperf3 JSON and extract per-interval throughput data.
    Returns list of (time, throughput_mbps) tuples.
    """
    try:
        with open(filepath, 'r') as f:
            data = json.load(f)

        if 'error' in data:
            return None

        intervals = data.get('intervals', [])
        if not intervals:
            return None

        # Extract throughput for each interval
        # Check if we have server-side data
        time_series = []
        for interval in intervals:
            streams = interval.get('streams', [])
            if not streams:
                continue

            # Use first stream (sum for multi-stream tests)
            stream = streams[0]

            # Get time and throughput
            end_time = stream.get('end', 0)
            bits_per_second = stream.get('bits_per_second', 0)
            throughput_mbps = bits_per_second / 1e6

            time_series.append((end_time, throughput_mbps))

        return time_series

    except (json.JSONDecodeError, FileNotFoundError, KeyError) as e:
        print(f"Error parsing {filepath}: {e}", file=sys.stderr)
        return None


def group_tests_by_config(results_dir):
    """
    Group all tests by configuration (bandwidth, delay, rate).
    Returns dict: (bw, delay, rate) -> {iteration: time_series}
    """
    raw_dir = Path(results_dir) / 'raw'

    if not raw_dir.exists():
        print(f"Error: Directory not found: {raw_dir}", file=sys.stderr)
        sys.exit(1)

    grouped = defaultdict(dict)

    for json_file in raw_dir.glob('*.json'):
        params = parse_filename(json_file.name)
        if not params:
            continue

        time_series = parse_iperf3_intervals(json_file)
        if not time_series:
            continue

        config_key = (params['bandwidth'], params['delay'], params['rate'])
        iteration = params['iteration']

        grouped[config_key][iteration] = time_series

    return grouped


def calculate_average_timeseries(iterations_data):
    """
    Calculate average time series from multiple iterations.
    Handles different lengths by interpolating to common time points.
    """
    if not iterations_data:
        return None

    # Collect all time points
    all_times = set()
    for time_series in iterations_data.values():
        for time, _ in time_series:
            all_times.add(time)

    if not all_times:
        return None

    # Sort time points
    common_times = sorted(all_times)

    # For each time point, average the throughput across iterations
    avg_series = []
    for t in common_times:
        throughputs = []

        for time_series in iterations_data.values():
            # Find closest time point in this iteration
            closest = min(time_series, key=lambda x: abs(x[0] - t))
            if abs(closest[0] - t) < 1.0:  # Within 1 second
                throughputs.append(closest[1])

        if throughputs:
            avg_throughput = np.mean(throughputs)
            avg_series.append((t, avg_throughput))

    return avg_series


def plot_configuration(config_key, iterations_data, output_dir, kernel_type):
    """
    Create a plot for one configuration showing all iterations + average.
    """
    bw, delay, rate = config_key

    # Create figure
    fig, ax = plt.subplots(figsize=(12, 6))

    # Define colors for iterations
    colors = ['#1f77b4', '#ff7f0e', '#2ca02c']  # Blue, Orange, Green

    # Plot each iteration
    for iteration in sorted(iterations_data.keys()):
        time_series = iterations_data[iteration]
        times = [t for t, _ in time_series]
        throughputs = [tp for _, tp in time_series]

        color = colors[iteration - 1] if iteration <= 3 else 'gray'
        ax.plot(times, throughputs,
                label=f'Iteration {iteration}',
                color=color,
                alpha=0.6,
                linewidth=1.5)

    # Calculate and plot average
    avg_series = calculate_average_timeseries(iterations_data)
    if avg_series:
        times = [t for t, _ in avg_series]
        throughputs = [tp for _, tp in avg_series]
        ax.plot(times, throughputs,
                label='Average',
                color='black',
                linewidth=2.5,
                linestyle='-')

    # Formatting
    ax.set_xlabel('Time (seconds)', fontsize=12)
    ax.set_ylabel('Throughput (Mbps)', fontsize=12)
    ax.set_title(f'{kernel_type.upper()} - BW={bw}, Delay={delay}, Rate={rate}',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='best')
    ax.grid(True, alpha=0.3)

    # Set reasonable y-axis limits (avoid extreme outliers)
    all_throughputs = []
    for time_series in iterations_data.values():
        all_throughputs.extend([tp for _, tp in time_series])
    if all_throughputs:
        max_tp = np.percentile(all_throughputs, 99)  # 99th percentile
        ax.set_ylim(0, max_tp * 1.1)

    # Save plot
    plt.tight_layout()
    plot_filename = f'config_bw{bw}_delay{delay}_rate{rate}.png'
    plot_path = output_dir / plot_filename
    plt.savefig(plot_path, dpi=100, bbox_inches='tight')
    plt.close()

    return plot_path


def main():
    if len(sys.argv) < 2:
        print(
            "Usage: python plot_per_config.py <results_dir> [output_dir]", file=sys.stderr)
        print("Example: python plot_per_config.py ../results/tcpaad", file=sys.stderr)
        sys.exit(1)

    results_dir = Path(sys.argv[1])

    # Determine output directory
    if len(sys.argv) >= 3:
        output_dir = Path(sys.argv[2])
    else:
        output_dir = results_dir / 'plots'

    # Create output directory
    output_dir.mkdir(parents=True, exist_ok=True)

    # Determine kernel type from results_dir
    kernel_type = results_dir.name  # 'tcpaad' or 'default'

    print(f"Processing results from: {results_dir}")
    print(f"Saving plots to: {output_dir}")
    print(f"Kernel type: {kernel_type}")
    print()

    # Group tests by configuration
    print("Grouping tests by configuration...")
    grouped = group_tests_by_config(results_dir)

    if not grouped:
        print("Error: No valid test data found", file=sys.stderr)
        sys.exit(1)

    print(f"Found {len(grouped)} configurations")
    print()

    # Generate plots
    print("Generating plots...")
    plot_count = 0

    for config_key in sorted(grouped.keys()):
        iterations_data = grouped[config_key]

        # Only plot if we have data
        if not iterations_data:
            continue

        try:
            plot_path = plot_configuration(config_key, iterations_data,
                                           output_dir, kernel_type)
            plot_count += 1

            if plot_count % 10 == 0:
                print(f"  Generated {plot_count} plots...", end='\r')

        except Exception as e:
            bw, delay, rate = config_key
            print(f"\nError plotting config bw={bw} delay={delay} rate={rate}: {e}",
                  file=sys.stderr)

    print(f"\nCompleted: {plot_count} plots generated")
    print(f"Plots saved to: {output_dir}")


if __name__ == '__main__':
    main()
