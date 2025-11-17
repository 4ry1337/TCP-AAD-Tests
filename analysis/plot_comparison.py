import sys
import csv
from pathlib import Path
from collections import defaultdict

try:
    import matplotlib.pyplot as plt
    import numpy as np
except ImportError:
    print("Error: This script requires matplotlib and numpy", file=sys.stderr)
    print("Install with: pip install matplotlib numpy", file=sys.stderr)
    sys.exit(1)


def read_comparison_csv(filepath):
    data = []
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            row['delay_ms'] = int(row['delay_ms'])
            row['rate_index'] = int(row['rate_index'])
            row['default_throughput_mbps'] = float(row['default_throughput_mbps'])
            row['tcpaad_throughput_mbps'] = float(row['tcpaad_throughput_mbps'])
            row['throughput_improvement_pct'] = float(row['throughput_improvement_pct'])
            row['retrans_reduction_pct'] = float(row['retrans_reduction_pct'])
            data.append(row)
    return data


def plot_throughput_by_delay(data, output_dir):
    by_delay = defaultdict(lambda: defaultdict(lambda: {'default': [], 'tcpaad': []}))

    for row in data:
        delay = row['delay_ms']
        bw = row['bandwidth']
        by_delay[delay][bw]['default'].append(row['default_throughput_mbps'])
        by_delay[delay][bw]['tcpaad'].append(row['tcpaad_throughput_mbps'])

    for delay in sorted(by_delay.keys()):
        fig, ax = plt.subplots(figsize=(12, 6))

        bandwidths = sorted(by_delay[delay].keys())
        x_pos = np.arange(len(bandwidths))
        width = 0.35

        default_means = [np.mean(by_delay[delay][bw]['default']) for bw in bandwidths]
        tcpaad_means = [np.mean(by_delay[delay][bw]['tcpaad']) for bw in bandwidths]

        bars1 = ax.bar(x_pos - width/2, default_means, width, label='Default', alpha=0.8)
        bars2 = ax.bar(x_pos + width/2, tcpaad_means, width, label='TCP-AAD', alpha=0.8)

        ax.set_xlabel('Bandwidth', fontsize=12)
        ax.set_ylabel('Throughput (Mbps)', fontsize=12)
        ax.set_title(f'Throughput Comparison - {delay}ms Delay', fontsize=14, fontweight='bold')
        ax.set_xticks(x_pos)
        ax.set_xticklabels(bandwidths)
        ax.legend()
        ax.grid(axis='y', alpha=0.3)

        plt.tight_layout()
        plt.savefig(output_dir / f'throughput_delay_{delay}ms.png', dpi=150)
        plt.close()

    print(f"Created {len(by_delay)} throughput plots by delay", file=sys.stderr)


def plot_improvement_heatmap(data, output_dir):
    by_delay_bw = defaultdict(lambda: defaultdict(list))

    for row in data:
        delay = row['delay_ms']
        bw = row['bandwidth']
        by_delay_bw[delay][bw].append(row['throughput_improvement_pct'])

    delays = sorted(by_delay_bw.keys())
    bandwidths = sorted(set(bw for delay_dict in by_delay_bw.values() for bw in delay_dict.keys()))

    improvement_matrix = np.zeros((len(delays), len(bandwidths)))

    for i, delay in enumerate(delays):
        for j, bw in enumerate(bandwidths):
            if bw in by_delay_bw[delay]:
                improvement_matrix[i, j] = np.mean(by_delay_bw[delay][bw])

    fig, ax = plt.subplots(figsize=(10, 8))
    im = ax.imshow(improvement_matrix, cmap='RdYlGn', aspect='auto', vmin=-10, vmax=30)

    ax.set_xticks(np.arange(len(bandwidths)))
    ax.set_yticks(np.arange(len(delays)))
    ax.set_xticklabels(bandwidths)
    ax.set_yticklabels([f'{d}ms' for d in delays])

    ax.set_xlabel('Bandwidth', fontsize=12)
    ax.set_ylabel('Delay', fontsize=12)
    ax.set_title('TCP-AAD Throughput Improvement (%)', fontsize=14, fontweight='bold')

    for i in range(len(delays)):
        for j in range(len(bandwidths)):
            text = ax.text(j, i, f'{improvement_matrix[i, j]:.1f}%',
                          ha="center", va="center", color="black", fontsize=9)

    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Improvement (%)', rotation=270, labelpad=20)

    plt.tight_layout()
    plt.savefig(output_dir / 'improvement_heatmap.png', dpi=150)
    plt.close()

    print("Created improvement heatmap", file=sys.stderr)


def plot_improvement_by_rate(data, output_dir):
    by_rate = defaultdict(list)

    for row in data:
        by_rate[row['rate_index']].append(row['throughput_improvement_pct'])

    rates = sorted(by_rate.keys())
    improvements = [np.mean(by_rate[r]) for r in rates]
    std_devs = [np.std(by_rate[r]) for r in rates]

    fig, ax = plt.subplots(figsize=(14, 6))

    ax.bar(range(len(rates)), improvements, yerr=std_devs, capsize=5, alpha=0.8, color='steelblue')
    ax.axhline(y=0, color='red', linestyle='--', linewidth=1, alpha=0.5)

    ax.set_xlabel('Rate Index', fontsize=12)
    ax.set_ylabel('Throughput Improvement (%)', fontsize=12)
    ax.set_title('TCP-AAD Improvement by WiFi Rate Index', fontsize=14, fontweight='bold')
    ax.set_xticks(range(len(rates)))
    ax.set_xticklabels(rates, rotation=45)
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    plt.savefig(output_dir / 'improvement_by_rate.png', dpi=150)
    plt.close()

    print("Created improvement by rate plot", file=sys.stderr)


def plot_retransmission_comparison(data, output_dir):
    by_delay = defaultdict(lambda: {'default': [], 'tcpaad': []})

    for row in data:
        delay = row['delay_ms']
        by_delay[delay]['default'].append(row['default_retransmits'])
        by_delay[delay]['tcpaad'].append(row['tcpaad_retransmits'])

    delays = sorted(by_delay.keys())
    default_retrans = [np.mean(by_delay[d]['default']) for d in delays]
    tcpaad_retrans = [np.mean(by_delay[d]['tcpaad']) for d in delays]

    fig, ax = plt.subplots(figsize=(10, 6))

    x_pos = np.arange(len(delays))
    width = 0.35

    bars1 = ax.bar(x_pos - width/2, default_retrans, width, label='Default', alpha=0.8, color='coral')
    bars2 = ax.bar(x_pos + width/2, tcpaad_retrans, width, label='TCP-AAD', alpha=0.8, color='lightgreen')

    ax.set_xlabel('Delay (ms)', fontsize=12)
    ax.set_ylabel('Average Retransmissions', fontsize=12)
    ax.set_title('Retransmission Comparison by Delay', fontsize=14, fontweight='bold')
    ax.set_xticks(x_pos)
    ax.set_xticklabels([f'{d}ms' for d in delays])
    ax.legend()
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    plt.savefig(output_dir / 'retransmission_comparison.png', dpi=150)
    plt.close()

    print("Created retransmission comparison plot", file=sys.stderr)


def main():
    if len(sys.argv) >= 2:
        comparison_csv = Path(sys.argv[1])
    else:
        script_dir = Path(__file__).parent
        comparison_csv = script_dir.parent / 'results' / 'comparison.csv'

    if not comparison_csv.exists():
        print(f"Error: Comparison file not found: {comparison_csv}", file=sys.stderr)
        print("Please run compare_kernels.py first.", file=sys.stderr)
        sys.exit(1)

    output_dir = comparison_csv.parent / 'plots'
    output_dir.mkdir(exist_ok=True)

    print(f"Reading comparison data from: {comparison_csv}", file=sys.stderr)
    print(f"Saving plots to: {output_dir}", file=sys.stderr)

    data = read_comparison_csv(comparison_csv)
    print(f"Loaded {len(data)} comparison records", file=sys.stderr)

    print("\nGenerating plots...", file=sys.stderr)
    plot_throughput_by_delay(data, output_dir)
    plot_improvement_heatmap(data, output_dir)
    plot_improvement_by_rate(data, output_dir)
    plot_retransmission_comparison(data, output_dir)

    print(f"\nAll plots saved to: {output_dir}", file=sys.stderr)

if __name__ == '__main__':
    main()
