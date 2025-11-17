import json
import sys
import os
from pathlib import Path
from collections import defaultdict
import re


def parse_filename(filename):
    pattern = r'bw(\w+)_delay(\d+)_rate(\d+)_iter(\d+)\.json'
    match = re.match(pattern, filename)

    if not match:
        return None

    return {
        'bandwidth': match.group(1),
        'delay': int(match.group(2)),
        'rate': int(match.group(3)),
        'iteration': int(match.group(4))
    }


def parse_iperf3_json(filepath):
    try:
        with open(filepath, 'r') as f:
            data = json.load(f)

        # Check for errors
        if 'error' in data:
            return None

        # Extract metrics from iperf3 output
        end_data = data.get('end', {})

        # Sum streams for overall throughput
        sum_sent = end_data.get('sum_sent', {})
        sum_received = end_data.get('sum_received', {})

        metrics = {
            'bits_per_second': sum_received.get('bits_per_second', 0) / 1e6,  # Convert to Mbps
            'bytes': sum_received.get('bytes', 0),
            'seconds': sum_received.get('seconds', 0),
            'retransmits': sum_sent.get('retransmits', 0),
            'jitter_ms': sum_received.get('jitter_ms', 0),
            'lost_packets': sum_received.get('lost_packets', 0),
            'packets': sum_received.get('packets', 0),
        }

        return metrics

    except (json.JSONDecodeError, FileNotFoundError, KeyError) as e:
        print(f"Error parsing {filepath}: {e}", file=sys.stderr)
        return None


def aggregate_results(results_dir):
    raw_dir = Path(results_dir) / 'raw'

    if not raw_dir.exists():
        print(f"Error: Directory not found: {raw_dir}", file=sys.stderr)
        sys.exit(1)

    # Collect all results
    all_tests = []

    for json_file in raw_dir.glob('*.json'):
        # Parse filename
        params = parse_filename(json_file.name)
        if not params:
            print(f"Warning: Skipping file with invalid name: {json_file.name}", file=sys.stderr)
            continue

        # Parse iperf3 results
        metrics = parse_iperf3_json(json_file)
        if not metrics:
            print(f"Warning: Failed to parse: {json_file.name}", file=sys.stderr)
            continue

        # Combine parameters and metrics
        test_result = {**params, **metrics}
        all_tests.append(test_result)

    if not all_tests:
        print("Error: No valid test results found", file=sys.stderr)
        sys.exit(1)

    print(f"Parsed {len(all_tests)} test results", file=sys.stderr)

    # Group by configuration (bandwidth, delay, rate)
    grouped = defaultdict(list)
    for test in all_tests:
        key = (test['bandwidth'], test['delay'], test['rate'])
        grouped[key].append(test)

    # Calculate aggregate statistics
    aggregated = []

    for (bw, delay, rate), tests in sorted(grouped.items()):
        if not tests:
            continue

        # Calculate mean and std for throughput
        throughputs = [t['bits_per_second'] for t in tests]
        retransmits = [t['retransmits'] for t in tests]

        n = len(throughputs)
        mean_throughput = sum(throughputs) / n
        std_throughput = (sum((x - mean_throughput)**2 for x in throughputs) / n) ** 0.5 if n > 1 else 0

        mean_retransmits = sum(retransmits) / n
        total_retransmits = sum(retransmits)

        # Packet loss rate
        total_packets = sum(t['packets'] for t in tests if t['packets'] > 0)
        total_lost = sum(t['lost_packets'] for t in tests)
        loss_rate = (total_lost / total_packets * 100) if total_packets > 0 else 0

        aggregated.append({
            'bandwidth': bw,
            'delay_ms': delay,
            'rate_index': rate,
            'iterations': n,
            'avg_throughput_mbps': round(mean_throughput, 2),
            'std_throughput_mbps': round(std_throughput, 2),
            'min_throughput_mbps': round(min(throughputs), 2),
            'max_throughput_mbps': round(max(throughputs), 2),
            'avg_retransmits': round(mean_retransmits, 1),
            'total_retransmits': total_retransmits,
            'packet_loss_pct': round(loss_rate, 3),
        })

    return aggregated


def write_csv(data, output_file):
    if not data:
        print("Error: No data to write", file=sys.stderr)
        return

    # Define columns
    columns = [
        'bandwidth', 'delay_ms', 'rate_index', 'iterations',
        'avg_throughput_mbps', 'std_throughput_mbps',
        'min_throughput_mbps', 'max_throughput_mbps',
        'avg_retransmits', 'total_retransmits', 'packet_loss_pct'
    ]

    with open(output_file, 'w') as f:
        # Write header
        f.write(','.join(columns) + '\n')

        # Write data rows
        for row in data:
            values = [str(row.get(col, '')) for col in columns]
            f.write(','.join(values) + '\n')

    print(f"Results written to: {output_file}", file=sys.stderr)


def main():
    if len(sys.argv) < 2:
        print("Usage: python analyze_results.py <results_dir> [output_csv]", file=sys.stderr)
        print("Example: python analyze_results.py ../results/tcpaad", file=sys.stderr)
        sys.exit(1)

    results_dir = sys.argv[1]

    if len(sys.argv) >= 3:
        output_file = sys.argv[2]
    else:
        kernel_type = Path(results_dir).name
        output_file = Path(results_dir).parent / f'summary_{kernel_type}.csv'

    print(f"Analyzing results from: {results_dir}", file=sys.stderr)

    aggregated = aggregate_results(results_dir)

    print(f"Aggregated {len(aggregated)} configurations", file=sys.stderr)

    write_csv(aggregated, output_file)

    print("\nSummary Statistics:", file=sys.stderr)
    print(f"  Total configurations: {len(aggregated)}", file=sys.stderr)

    if aggregated:
        all_throughputs = [row['avg_throughput_mbps'] for row in aggregated]
        print(f"  Throughput range: {min(all_throughputs):.2f} - {max(all_throughputs):.2f} Mbps", file=sys.stderr)
        print(f"  Mean throughput: {sum(all_throughputs) / len(all_throughputs):.2f} Mbps", file=sys.stderr)


if __name__ == '__main__':
    main()
