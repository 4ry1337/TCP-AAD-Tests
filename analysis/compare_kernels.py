import sys
import csv
from pathlib import Path
from collections import defaultdict

def read_csv(filepath):
    """
    Read summary CSV file and return list of dictionaries.
    """
    data = []
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            # Convert numeric fields
            row['delay_ms'] = int(row['delay_ms'])
            row['rate_index'] = int(row['rate_index'])
            row['avg_throughput_mbps'] = float(row['avg_throughput_mbps'])
            row['std_throughput_mbps'] = float(row['std_throughput_mbps'])
            row['avg_retransmits'] = float(row['avg_retransmits'])
            row['total_retransmits'] = int(row['total_retransmits'])
            row['packet_loss_pct'] = float(row['packet_loss_pct'])
            data.append(row)
    return data


def compare_results(tcpaad_data, default_data):
    default_index = {}
    for row in default_data:
        key = (row['bandwidth'], row['delay_ms'], row['rate_index'])
        default_index[key] = row

    comparisons = []

    for tcpaad_row in tcpaad_data:
        key = (tcpaad_row['bandwidth'], tcpaad_row['delay_ms'], tcpaad_row['rate_index'])

        default_row = default_index.get(key)
        if not default_row:
            print(f"Warning: No default data for {key}", file=sys.stderr)
            continue

        default_tp = default_row['avg_throughput_mbps']
        tcpaad_tp = tcpaad_row['avg_throughput_mbps']

        if default_tp > 0:
            improvement_pct = ((tcpaad_tp - default_tp) / default_tp) * 100
        else:
            improvement_pct = 0

        default_retrans = default_row['total_retransmits']
        tcpaad_retrans = tcpaad_row['total_retransmits']

        if default_retrans > 0:
            retrans_reduction_pct = ((default_retrans - tcpaad_retrans) / default_retrans) * 100
        else:
            retrans_reduction_pct = 0

        comparisons.append({
            'bandwidth': tcpaad_row['bandwidth'],
            'delay_ms': tcpaad_row['delay_ms'],
            'rate_index': tcpaad_row['rate_index'],
            'default_throughput_mbps': round(default_tp, 2),
            'tcpaad_throughput_mbps': round(tcpaad_tp, 2),
            'throughput_improvement_pct': round(improvement_pct, 2),
            'default_std_mbps': round(default_row['std_throughput_mbps'], 2),
            'tcpaad_std_mbps': round(tcpaad_row['std_throughput_mbps'], 2),
            'default_retransmits': default_retrans,
            'tcpaad_retransmits': tcpaad_retrans,
            'retrans_reduction_pct': round(retrans_reduction_pct, 2),
            'default_loss_pct': round(default_row['packet_loss_pct'], 3),
            'tcpaad_loss_pct': round(tcpaad_row['packet_loss_pct'], 3),
        })

    return comparisons


def write_comparison_csv(comparisons, output_file):
    """
    Write comparison results to CSV.
    """
    if not comparisons:
        print("Error: No comparison data to write", file=sys.stderr)
        return

    columns = [
        'bandwidth', 'delay_ms', 'rate_index',
        'default_throughput_mbps', 'tcpaad_throughput_mbps', 'throughput_improvement_pct',
        'default_std_mbps', 'tcpaad_std_mbps',
        'default_retransmits', 'tcpaad_retransmits', 'retrans_reduction_pct',
        'default_loss_pct', 'tcpaad_loss_pct'
    ]

    with open(output_file, 'w') as f:
        writer = csv.DictWriter(f, fieldnames=columns)
        writer.writeheader()
        writer.writerows(comparisons)

    print(f"Comparison written to: {output_file}", file=sys.stderr)


def print_summary_statistics(comparisons):
    if not comparisons:
        return

    improvements = [c['throughput_improvement_pct'] for c in comparisons]
    retrans_reductions = [c['retrans_reduction_pct'] for c in comparisons]

    # Filter for positive and negative improvements
    positive_improvements = [i for i in improvements if i > 0]
    negative_improvements = [i for i in improvements if i < 0]

    print("\n" + "="*80, file=sys.stderr)
    print("COMPARISON SUMMARY", file=sys.stderr)
    print("="*80, file=sys.stderr)

    print(f"\nTotal configurations compared: {len(comparisons)}", file=sys.stderr)

    print(f"\nThroughput Improvement:", file=sys.stderr)
    print(f"  Mean: {sum(improvements) / len(improvements):.2f}%", file=sys.stderr)
    print(f"  Median: {sorted(improvements)[len(improvements)//2]:.2f}%", file=sys.stderr)
    print(f"  Min: {min(improvements):.2f}%", file=sys.stderr)
    print(f"  Max: {max(improvements):.2f}%", file=sys.stderr)
    print(f"  Positive improvements: {len(positive_improvements)} ({len(positive_improvements)/len(improvements)*100:.1f}%)", file=sys.stderr)
    print(f"  Negative improvements: {len(negative_improvements)} ({len(negative_improvements)/len(improvements)*100:.1f}%)", file=sys.stderr)

    print(f"\nRetransmission Reduction:", file=sys.stderr)
    print(f"  Mean: {sum(retrans_reductions) / len(retrans_reductions):.2f}%", file=sys.stderr)

    # Best improvements by delay
    print(f"\nBest Improvements by Delay:", file=sys.stderr)
    by_delay = defaultdict(list)
    for c in comparisons:
        by_delay[c['delay_ms']].append(c['throughput_improvement_pct'])

    for delay in sorted(by_delay.keys()):
        improvements_for_delay = by_delay[delay]
        mean_imp = sum(improvements_for_delay) / len(improvements_for_delay)
        print(f"  {delay}ms delay: {mean_imp:.2f}% average improvement", file=sys.stderr)

    # Best improvements by bandwidth
    print(f"\nBest Improvements by Bandwidth:", file=sys.stderr)
    by_bw = defaultdict(list)
    for c in comparisons:
        by_bw[c['bandwidth']].append(c['throughput_improvement_pct'])

    for bw in sorted(by_bw.keys()):
        improvements_for_bw = by_bw[bw]
        mean_imp = sum(improvements_for_bw) / len(improvements_for_bw)
        print(f"  {bw}: {mean_imp:.2f}% average improvement", file=sys.stderr)

    # Top 10 best improvements
    print(f"\nTop 10 Best Improvements:", file=sys.stderr)
    sorted_comparisons = sorted(comparisons, key=lambda x: x['throughput_improvement_pct'], reverse=True)
    for i, c in enumerate(sorted_comparisons[:10], 1):
        print(f"  {i}. BW={c['bandwidth']}, Delay={c['delay_ms']}ms, Rate={c['rate_index']}: "
              f"{c['throughput_improvement_pct']:.2f}% "
              f"({c['default_throughput_mbps']:.2f} → {c['tcpaad_throughput_mbps']:.2f} Mbps)",
              file=sys.stderr)

    # Top 10 worst cases
    print(f"\nTop 10 Worst Cases (degradations):", file=sys.stderr)
    for i, c in enumerate(sorted_comparisons[-10:][::-1], 1):
        print(f"  {i}. BW={c['bandwidth']}, Delay={c['delay_ms']}ms, Rate={c['rate_index']}: "
              f"{c['throughput_improvement_pct']:.2f}% "
              f"({c['default_throughput_mbps']:.2f} → {c['tcpaad_throughput_mbps']:.2f} Mbps)",
              file=sys.stderr)

    print("\n" + "="*80 + "\n", file=sys.stderr)


def main():
    if len(sys.argv) >= 3:
        tcpaad_csv = sys.argv[1]
        default_csv = sys.argv[2]
    else:
        script_dir = Path(__file__).parent
        results_dir = script_dir.parent / 'results'
        tcpaad_csv = results_dir / 'summary_tcpaad.csv'
        default_csv = results_dir / 'summary_default.csv'

    if len(sys.argv) >= 4:
        output_csv = sys.argv[3]
    else:
        script_dir = Path(__file__).parent
        output_csv = script_dir.parent / 'results' / 'comparison.csv'

    print(f"Comparing:", file=sys.stderr)
    print(f"  TCP-AAD: {tcpaad_csv}", file=sys.stderr)
    print(f"  Default: {default_csv}", file=sys.stderr)
    print(f"  Output: {output_csv}", file=sys.stderr)

    try:
        tcpaad_data = read_csv(tcpaad_csv)
        default_data = read_csv(default_csv)
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        print("\nPlease run analyze_results.py first to generate summary CSV files.", file=sys.stderr)
        sys.exit(1)

    print(f"Loaded {len(tcpaad_data)} TCP-AAD results", file=sys.stderr)
    print(f"Loaded {len(default_data)} default results", file=sys.stderr)

    comparisons = compare_results(tcpaad_data, default_data)
    write_comparison_csv(comparisons, output_csv)
    print_summary_statistics(comparisons)


if __name__ == '__main__':
    main()
