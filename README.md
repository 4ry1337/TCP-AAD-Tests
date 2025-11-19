# Experiments with TCP over Wi-Fi

Supervisor: Shinnazar Seytnazarov

Type of project:
- [x] Research and Development
- [ ] System Development

Topic: Experiments with TCP over Wi-Fi

Team:
- Rakhat Yskak

## Overview
TCP is the most widely used transport-layer protocol due to its completeness. It
provides reliability, congestion control and flow control services. For example,
to provide reliability, it uses acknowledgment (ACK) mechanism were reciever
signals the sender about the successful reception of the packet. We have an
improved version of TCP here ACK mechanism is optimized for wireless scenarios.

This project conducts a **comprehensive experiments evalution** of an **improved
TCP** (Linux kernel code provided) across controlled Wi-Fi scenarios, to qualify
benefits, limits, and trade-offs and to guide upstreaming/real-world deployment.

**Eligibility**
- Students with solid **computer networks**, **Linux** fundamentals, **C**
programming

## Product description

A **reproduction experimental suite** for **TCP-over-WiFi**, centered on the
provided **Linux kernel code** and **Jupyter test notebook**, what we deliver:

- **One command runner**: set Wi-FI parameters (channel width, MCS/Aggregation, TX
power), toggles offloads (TSO/RSO), selects TCP CC (CUBIC/BBR/candidate), and
applies clean configs.
- **Scenario matrix**: single vs multi-station; upload/download; short vs. long
flows; controlled distance/attention; optional WAN effects via tc netem
(RTT/loss/jitter).
- **Data capture**: iperf3/Flent results, tcpdump pcaps, ss (cwnd/RTT), Wi-Fi
stats (iw/mac80211), and qdisc counters - saved with per-run metadata.
- **Analysis notebook**: generates throughput/latency CDFs, time-series overlays
(cwnd/RTT/throughput), fairness metrics, and summery tables; auto-exports
publication-quality figures.
- **Artifacts**: scripts + configs, sample logs dataset, and quick-start README;
optional short "deployment notes" (tunning checklist and known caveats).

**Primary KPI**: goodput, flow-completion time, loss/retransmissions, and fairness
under contention.

## Tentative deliveries

- **Experiment suite**: scripts + configs + Makefile (or PyInvoke) to run the matrix
and collect logs.
- **Dataset**: raw logs, pcaps, and per-run metadata (JSON)
- **Notebook outputs**: plots (throughput/latency CDFs; cwnd/RTT traces), summary
tables, regression analysis.
- **Final report**: results, guidlines, and known limitations; patch notes for
kernel code (if any).
- **Quick start README**: exact steps to replicate on fresh machines.
- **Optional**: IEEE conference style 6-page paper.

## Hardware and Software Requirements 

### Hardware
- 2 Linux hosts with modern Wi-Fi one configurable
- AP/router.

### Software
- Linux (kernel 5.15+ or 6.x), root access, toolchain to build the provided
kernel code.
- **iperf3, Flent, tcpdump/wireshark, tc netem, iw/hostapd** (as needed), Python 3
for the analysis notebook.

## Reference
1. **RFC 9438: CUBIC for Fast and Long-Distance Networks** (standard TCP CC, default
   in many stacks)
2. **BBR congestion control**.
3. **Linux TCP docs & pluggable CC** (kernel.org).
4. **802.11n frame aggregation (A-MDPU/A-MSDU)**.
5. **Minstrel rate control (mac80211)** (Linux Wireless docs; background paper).
6. **tc netem** (Linux network emulator).
7. **Flent** (Flexible Network Tester) for automated multi-tool tests & plotting.
