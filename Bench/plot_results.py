#!/usr/bin/env python3
"""Create benchmark timing graphs using only Python's stdlib."""

import argparse
import csv
import html
import statistics
from collections import defaultdict

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("first")
parser.add_argument("second")
parser.add_argument("output")
parser.add_argument("--versions", nargs=2, help="Select two versions from the input CSVs")
parser.add_argument("--labels", nargs=2, help="Legend labels in version order")
parser.add_argument("--title", default="ChaCha20 encryption performance")
parser.add_argument("--subtitle", default="")
parser.add_argument("--footer", default="")
args = parser.parse_args()
input_files = [args.first, args.second]
output_file = args.output
samples = defaultdict(list)
versions = list(args.versions or [])
for filename in input_files:
    with open(filename, newline="") as file:
        for row in csv.DictReader(file):
            if args.versions and row["version"] not in args.versions:
                continue
            if row["version"] not in versions:
                versions.append(row["version"])
            key = row["version"], int(row["size_bytes"])
            samples[key].append(float(row["ns_per_call"]) / 1_000_000)

if len(versions) != 2:
    raise SystemExit("the two CSV files must contain two distinct versions")

sizes = sorted({size for _, size in samples})
if not sizes or any(not samples[version, size] for version in versions for size in sizes):
    raise SystemExit("both versions must have samples at every input size")
times = {
    version: [statistics.median(samples[version, size]) for size in sizes]
    for version in versions
}

width, height = 800, 560
left, top, right, bottom = 75, 115, 25, 105
plot_width = width - left - right
plot_height = height - top - bottom
maximum = max(max(values) for values in times.values()) * 1.1

def x(index):
    return left + index * plot_width / max(1, len(sizes) - 1)

def y(milliseconds):
    return top + plot_height * (maximum - milliseconds) / maximum

svg = [
    f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img">',
    f'<title>{html.escape(args.title)}</title>',
    f'<desc>{html.escape(args.subtitle)} Median time per call; lower is faster. {html.escape(args.footer)}</desc>',
    '<rect width="100%" height="100%" fill="white"/>',
    '<style>text { font-family: sans-serif; fill: #222; }</style>',
    f'<text x="400" y="29" text-anchor="middle" font-size="20">{html.escape(args.title)}</text>',
    f'<text x="400" y="51" text-anchor="middle" font-size="12">{html.escape(args.subtitle)}</text>',
    f'<line x1="{left}" y1="{top}" x2="{left}" y2="{top + plot_height}" stroke="#555"/>',
    f'<line x1="{left}" y1="{top + plot_height}" x2="{left + plot_width}" y2="{top + plot_height}" stroke="#555"/>',
]

for index, size in enumerate(sizes):
    label = f"{size} B" if size < 1024 else f"{size // 1024} KiB"
    svg.append(f'<text x="{x(index):.1f}" y="{top + plot_height + 25}" text-anchor="middle" font-size="12">{label}</text>')

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
        svg.append(f'<circle cx="{x(i):.1f}" cy="{y(value):.1f}" r="4" fill="{colors[version]}"><title>{html.escape(version)}: {sizes[i]} bytes, {value:.6f} ms, {len(samples[version, sizes[i]])} samples</title></circle>')

labels = args.labels or [version.title() for version in versions]
for index, version in enumerate(versions):
    legend_x = 160 + 300 * index
    svg.append(f'<line x1="{legend_x}" y1="82" x2="{legend_x + 25}" y2="82" stroke="{colors[version]}" stroke-width="3"/><text x="{legend_x + 34}" y="86" font-size="13">{html.escape(labels[index])}</text>')

svg += [
    '<text x="400" y="509" text-anchor="middle" font-size="13">Input size (equally spaced benchmark sizes)</text>',
    '<text x="17" y="250" text-anchor="middle" font-size="13" transform="rotate(-90 17 250)">Median time (ms)</text>',
    f'<text x="400" y="542" text-anchor="middle" font-size="11">{html.escape(args.footer)}</text>',
    '</svg>',
]

with open(output_file, "w") as file:
    file.write("\n".join(svg))
