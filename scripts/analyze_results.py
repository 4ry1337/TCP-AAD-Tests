#!/usr/bin/env python3
"""
Verification Results Analysis Script

Parses SPIN verification outputs and generates:
- Comparison tables (DACK vs AAD)
- Performance metrics
- Visualization data
- LaTeX tables for paper

Usage:
    python3 analyze_results.py <report_file>
    python3 analyze_results.py results/verification_outputs/verification_report_*.txt
"""

import sys
import re
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple
import json


class VerificationResult:
    """Represents a single verification result"""

    def __init__(self, model: str, property_name: str, result: str,
                 states: str, transitions: str, memory: str):
        self.model = model
        self.property_name = property_name
        self.result = result
        self.states = self._parse_number(states)
        self.transitions = self._parse_number(transitions)
        self.memory = self._parse_number(memory)

    @staticmethod
    def _parse_number(value: str) -> int:
        """Convert string number to int, handling N/A"""
        if value == "N/A" or not value:
            return 0
        try:
            return int(value.replace(',', ''))
        except ValueError:
            return 0

    def __repr__(self):
        return f"{self.model}:{self.property_name}={self.result}"


class ResultsAnalyzer:
    """Analyzes verification results"""

    def __init__(self, report_path: str):
        self.report_path = Path(report_path)
        self.results: List[VerificationResult] = []
        self.parse_report()

    def parse_report(self):
        """Parse verification report file"""
        with open(self.report_path, 'r') as f:
            content = f.read()

        # Split into individual result blocks
        blocks = content.split('----------------------------------------')

        for block in blocks:
            if 'Model:' not in block:
                continue

            model_match = re.search(r'Model:\s+(\S+)', block)
            property_match = re.search(r'Property:\s+(.+)', block)
            result_match = re.search(r'Result:\s+(\S+)', block)
            states_match = re.search(r'States Explored:\s+(\S+)', block)
            transitions_match = re.search(r'Transitions:\s+(\S+)', block)
            memory_match = re.search(r'Memory Used:\s+(\S+)', block)

            if all([model_match, property_match, result_match]):
                result = VerificationResult(
                    model=model_match.group(1),
                    property_name=property_match.group(1).strip(),
                    result=result_match.group(1),
                    states=states_match.group(1) if states_match else "N/A",
                    transitions=transitions_match.group(1) if transitions_match else "N/A",
                    memory=memory_match.group(1) if memory_match else "N/A"
                )
                self.results.append(result)

    def get_summary(self) -> Dict[str, Dict[str, int]]:
        """Get summary statistics by model"""
        summary = {}

        for result in self.results:
            if result.model not in summary:
                summary[result.model] = {
                    'total': 0,
                    'passed': 0,
                    'failed': 0,
                    'timeout': 0,
                    'total_states': 0,
                    'total_memory': 0
                }

            summary[result.model]['total'] += 1
            summary[result.model][result.result.lower()] = \
                summary[result.model].get(result.result.lower(), 0) + 1
            summary[result.model]['total_states'] += result.states
            summary[result.model]['total_memory'] += result.memory

        return summary

    def generate_comparison_table(self) -> str:
        """Generate comparison table for DACK vs AAD"""
        dack_results = [r for r in self.results if 'dack' in r.model.lower() and 'tcp_basic' not in r.model]
        aad_results = [r for r in self.results if 'aad' in r.model.lower()]

        # Match common properties
        table = "| Property | DACK Result | DACK States | AAD Result | AAD States | Improvement |\n"
        table += "|----------|-------------|-------------|------------|------------|-------------|\n"

        # Find common property names
        common_props = set()
        for dr in dack_results:
            for ar in aad_results:
                if self._normalize_property(dr.property_name) == self._normalize_property(ar.property_name):
                    common_props.add(self._normalize_property(dr.property_name))

        for prop in sorted(common_props):
            dack = next((r for r in dack_results if self._normalize_property(r.property_name) == prop), None)
            aad = next((r for r in aad_results if self._normalize_property(r.property_name) == prop), None)

            if dack and aad:
                improvement = ""
                if dack.states > 0 and aad.states > 0:
                    diff_pct = ((aad.states - dack.states) / dack.states) * 100
                    improvement = f"{diff_pct:+.1f}%"

                table += f"| {prop} | {dack.result} | {dack.states:,} | {aad.result} | {aad.states:,} | {improvement} |\n"

        return table

    @staticmethod
    def _normalize_property(prop_name: str) -> str:
        """Normalize property name for comparison"""
        # Remove _dack or _aad suffix
        prop = re.sub(r'_(dack|aad)$', '', prop_name.lower())
        return prop.strip()

    def generate_latex_table(self) -> str:
        """Generate LaTeX table for paper"""
        latex = r"""\begin{table}[ht]
\centering
\caption{Verification Results: TCP Default DACK vs TCP-AAD}
\label{tab:verification_results}
\begin{tabular}{|l|c|c|c|c|}
\hline
\textbf{Property} & \textbf{DACK} & \textbf{States} & \textbf{AAD} & \textbf{States} \\
\hline
"""

        dack_results = [r for r in self.results if 'dack' in r.model.lower() and 'tcp_basic' not in r.model]
        aad_results = [r for r in self.results if 'aad' in r.model.lower()]

        # Find common properties
        common_props = set()
        for dr in dack_results:
            for ar in aad_results:
                if self._normalize_property(dr.property_name) == self._normalize_property(ar.property_name):
                    common_props.add(self._normalize_property(dr.property_name))

        for prop in sorted(common_props):
            dack = next((r for r in dack_results if self._normalize_property(r.property_name) == prop), None)
            aad = next((r for r in aad_results if self._normalize_property(r.property_name) == prop), None)

            if dack and aad:
                dack_symbol = r"\checkmark" if dack.result == "PASS" else r"\times"
                aad_symbol = r"\checkmark" if aad.result == "PASS" else r"\times"
                latex += f"{prop.replace('_', ' ').title()} & ${dack_symbol}$ & {dack.states:,} & ${aad_symbol}$ & {aad.states:,} \\\\\n"

        latex += r"""\hline
\end{tabular}
\end{table}
"""
        return latex

    def export_json(self, output_path: str):
        """Export results to JSON"""
        data = {
            'timestamp': datetime.now().isoformat(),
            'report_file': str(self.report_path),
            'summary': self.get_summary(),
            'results': [
                {
                    'model': r.model,
                    'property': r.property_name,
                    'result': r.result,
                    'states': r.states,
                    'transitions': r.transitions,
                    'memory_mb': r.memory
                }
                for r in self.results
            ]
        }

        with open(output_path, 'w') as f:
            json.dump(data, f, indent=2)

        print(f"Exported results to {output_path}")


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 analyze_results.py <report_file>")
        sys.exit(1)

    report_file = sys.argv[1]

    if not Path(report_file).exists():
        print(f"Error: Report file not found: {report_file}")
        sys.exit(1)

    print(f"Analyzing verification results from: {report_file}\n")

    analyzer = ResultsAnalyzer(report_file)

    # Print summary
    print("=" * 60)
    print("VERIFICATION SUMMARY")
    print("=" * 60)
    summary = analyzer.get_summary()

    for model, stats in summary.items():
        print(f"\n{model}:")
        print(f"  Total Properties: {stats['total']}")
        print(f"  Passed: {stats.get('pass', 0)}")
        print(f"  Failed: {stats.get('fail', 0)}")
        print(f"  Timeout: {stats.get('timeout', 0)}")
        print(f"  Total States Explored: {stats['total_states']:,}")
        print(f"  Total Memory Used: {stats['total_memory']:.1f} MB")

    # Generate comparison table
    print("\n" + "=" * 60)
    print("COMPARISON: DACK vs AAD")
    print("=" * 60)
    print(analyzer.generate_comparison_table())

    # Generate LaTeX table
    print("\n" + "=" * 60)
    print("LATEX TABLE FOR PAPER")
    print("=" * 60)
    print(analyzer.generate_latex_table())

    # Export to JSON
    output_json = Path(report_file).parent / "analysis_results.json"
    analyzer.export_json(str(output_json))

    # Save LaTeX table
    latex_file = Path(report_file).parent / "results_table.tex"
    with open(latex_file, 'w') as f:
        f.write(analyzer.generate_latex_table())
    print(f"\nLaTeX table saved to: {latex_file}")

    print("\nAnalysis complete!")


if __name__ == "__main__":
    main()
