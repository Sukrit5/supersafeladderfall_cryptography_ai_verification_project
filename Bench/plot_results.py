#!/usr/bin/env python3
"""Create a simple ChaCha20 timing line graph using only Python's stdlib."""

import csv
import statistics
import sys
from collections import defaultdict

if len(sys.argv) != 4:
    raise SystemExit("usage: plot_results.py FIRST.csv SECOND.csv OUTPUT.svg")

input_files = sys.argv[1:3]
output_file = sys.argv[3]
samples = defaultdict(list)
versions = []
for filename in input_files:
    with open(filename, newline="") as file:
        for row in csv.DictReader(file):
            if row["version"] not in versions:
                versions.append(row["version"])
            key = row["version"], int(row["size_bytes"])
            samples[key].append(float(row["ns_per_call"]) / 1_000_000)

if len(versions) != 2:
    raise SystemExit("the two CSV files must contain two distinct versions")

sizes = sorted({size for _, size in samples})
times = {
    version: [statistics.median(samples[version, size]) for size in sizes]
    for version in versions
}

width, height = 800, 500
left, top, right, bottom = 75, 50, 25, 65
plot_width = width - left - right
plot_height = height - top - bottom
maximum = max(max(values) for values in times.values()) * 1.1

def x(index):
    return left + index * plot_width / (len(sizes) - 1)

def y(milliseconds):
    return top + plot_height * (maximum - milliseconds) / maximum

svg = [
    f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">',
    '<rect width="100%" height="100%" fill="white"/>',
    '<style>text { font-family: sans-serif; fill: #222; }</style>',
    '<text x="400" y="27" text-anchor="middle" font-size="20">ChaCha20 encryption performance</text>',
    f'<line x1="{left}" y1="{top}" x2="{left}" y2="{top + plot_height}" stroke="#555"/>',
    f'<line x1="{left}" y1="{top + plot_height}" x2="{left + plot_width}" y2="{top + plot_height}" stroke="#555"/>',
]

for index, size in enumerate(sizes):
    label = f"{size} B" if size < 1024 else f"{size // 1024} KiB"
    svg.append(f'<text x="{x(index):.1f}" y="{height - 35}" text-anchor="middle" font-size="12">{label}</text>')

for tick in range(6):
    value = maximum * tick / 5
    position = y(value)
    svg.append(f'<line x1="{left}" y1="{position:.1f}" x2="{left + plot_width}" y2="{position:.1f}" stroke="#ddd"/>')
    svg.append(f'<text x="{left - 8}" y="{position + 4:.1f}" text-anchor="end" font-size="12">{value:.3g}</text>')

colors = dict(zip(versions, ("#d1495b", "#167d9a")))
for version in versions:
    points = " ".join(f"{x(i):.1f},{y(value):.1f}" for i, value in enumerate(times[version]))
    svg.append(f'<polyline points="{points}" fill="none" stroke="{colors[version]}" stroke-width="3"/>')
    for i, value in enumerate(times[version]):
        svg.append(f'<circle cx="{x(i):.1f}" cy="{y(value):.1f}" r="4" fill="{colors[version]}"/>')

svg += [
    f'<line x1="535" y1="25" x2="560" y2="25" stroke="{colors[versions[0]]}" stroke-width="3"/><text x="567" y="29" font-size="12">{versions[0].title()}</text>',
    f'<line x1="665" y1="25" x2="690" y2="25" stroke="{colors[versions[1]]}" stroke-width="3"/><text x="697" y="29" font-size="12">{versions[1].title()}</text>',
    '<text x="400" y="490" text-anchor="middle" font-size="13">Input size</text>',
    '<text x="17" y="250" text-anchor="middle" font-size="13" transform="rotate(-90 17 250)">Median time (ms)</text>',
    '</svg>',
]

with open(output_file, "w") as file:
    file.write("\n".join(svg))
