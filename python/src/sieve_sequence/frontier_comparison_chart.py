"""Real-sieve frontier chart: empirical survivors vs the random projection and
the c=1 square-window frontier.

Recreates four_lines_chart.py focused on the three trajectories the draft
phase-transition article actually needs (Property III/IV): the real measured
sieve survivors in the fixed window [Q, Q^2), the true-random projection
w_r=1, and the c=1 frontier projection w_r=1+log(r). The friendly ceiling and
the proved worst-case adversarial floor are deliberately dropped -- the
question here is whether the real sieve stays above the square-window
threshold, not its distance to the absolute bounds.

Reads ../../../data/candidates/four-lines-Q101.csv (written by
sieve_sequence_empirical.four_lines_cli, which adds the N_frontier column for
w_r=1+log r via four_lines.log_growth_trajectory; run that first) rather than
recomputing anything.

Semantics of the three lines:
  - empirical   the real measured surviving count in [Q,Q^2) after each
                installed filter -- not a projection at all
  - random      N_0 * prod(1 - 2/r)      -- the true-random baseline (w_r=1)
  - frontier    N_0 * prod(1 - 2*(1+log r)/r) -- the article's c=1 square-window
                threshold (Property IV): the slowest-growing relative factor
                whose square-window expectation still tends to zero

Solid = real data. Dashed = projections under a stated per-filter model,
matching the four-lines/spacing convention. Only one solid line: the frontier
is drawn in the same black the phase-transition charts use for their boundary,
dashed here because it is a projection onto real data, not that chart's
analytic boundary.

Run: python3 frontier_comparison_chart.py
Output: ./out/frontier-comparison-Q101.svg
"""

import csv
import datetime
import os
import subprocess
import sys

from .svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "charts")
DATA_PATH = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "candidates", "four-lines-Q101.csv"
)

COLOR_EMPIRICAL = "#2a78d6"    # blue -- the real data, solid
COLOR_RANDOM = "#e34948"       # red -- w_r=1 projection, dashed
COLOR_FRONTIER = "#111111"     # black -- c=1 frontier projection, dashed

DASH_EMPIRICAL = None
DASH_RANDOM = "7,4"
DASH_FRONTIER = "10,3,2,3"

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"


def vertical_text(canvas, x, y, label, size=12, fill=INK_MUTED):
    canvas.elements.append(
        f'<text x="{x}" y="{y}" font-family="{canvas.font_family}" font-size="{size}" '
        f'font-weight="normal" font-style="normal" fill="{fill}" '
        f'text-anchor="middle" transform="rotate(-90 {x} {y})">{escape(label)}</text>'
    )


def load_rows():
    with open(DATA_PATH, newline="") as f:
        return list(csv.DictReader(f))


def draw(rows):
    left, right, top, bottom = 70, 210, 50, 85
    plot_w, plot_h = 500, 380
    W = left + plot_w + right
    H = top + plot_h + bottom
    canvas = Canvas(W, H)

    canvas.comment(f"Generated: {datetime.datetime.now().isoformat()}")
    canvas.comment(f"Script: {os.path.basename(__file__)}")
    canvas.comment(f"Python: {sys.version}")
    canvas.comment(f"Input: {DATA_PATH}")
    try:
        commit = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], text=True).strip()
        canvas.comment(f"Git commit: {commit}")
    except Exception:
        canvas.comment("Git commit: unknown")

    layers = [int(r["layer"]) for r in rows]
    x_lo, x_hi = min(layers), max(layers)
    y_max = max(
        max(float(r["N_empirical_pre"]) for r in rows),
        max(float(r["N_empirical_post"]) for r in rows),
    )
    y_hi = y_max * 1.08

    def to_x(layer):
        span = (x_hi - x_lo) or 1
        return left + (layer - x_lo) / span * plot_w

    def to_y(value):
        return top + plot_h - (value / y_hi) * plot_h

    canvas.line(left, top, left, top + plot_h, stroke=GRID, width=1)
    canvas.line(left, top + plot_h, left + plot_w, top + plot_h, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = top + plot_h - frac * plot_h
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        canvas.text(left - 10, y + 4, f"{frac * y_hi:.0f}", size=11, anchor="end", fill=INK_MUTED)

    anchor_layer = int(rows[0]["anchor_layer"])
    anchor_r = rows[0]["anchor_r"]
    for r in rows:
        layer = int(r["layer"])
        canvas.text(to_x(layer), top + plot_h + 18, r["r"], size=10, anchor="middle", fill=INK_MUTED)
    canvas.text(left + plot_w / 2, top + plot_h + 38, "installed filter r", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, top + plot_h / 2, "surviving 2-gaps in [Q, Q^2)", size=12, fill=INK_MUTED)

    def series(col):
        return [(to_x(int(r["layer"])), to_y(float(r[col]))) for r in rows]

    canvas.polyline(series("N_random"), stroke=COLOR_RANDOM, width=2, dash=DASH_RANDOM)
    canvas.polyline(series("N_frontier"), stroke=COLOR_FRONTIER, width=2, dash=DASH_FRONTIER)
    canvas.polyline(series("N_empirical_post"), stroke=COLOR_EMPIRICAL, width=2.5, dash=DASH_EMPIRICAL)

    # anchor marker: all three lines agree here by construction
    ax, ay = to_x(anchor_layer), to_y(float(rows[0]["anchor_n0"]))
    canvas.circle(ax, ay, r=5, fill="white", stroke=INK_PRIMARY, width=2)

    legend_x, legend_y = left + plot_w + 24, top + 24
    entries = [
        ("empirical (real sieve data)", COLOR_EMPIRICAL, DASH_EMPIRICAL),
        ("random (w_r=1 projection)", COLOR_RANDOM, DASH_RANDOM),
        ("frontier (w_r=1+log r, c=1)", COLOR_FRONTIER, DASH_FRONTIER),
    ]
    canvas.text(legend_x, legend_y - 14, "trajectory", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color, dash) in enumerate(entries):
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5 if dash is None else 2, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)
    note_y = legend_y + len(entries) * 22 + 14
    for i, line in enumerate([
        "solid = real data, dashed = projections.",
        "The frontier is the square-window",
        "threshold of the phase-transition",
        "article (c=1, Property IV): the slowest",
        "growing factor whose window expectation",
        "still tends to zero. This is a finite",
        "measurement: 16 layers, one lineage",
        "chain. The trajectory stays above the",
        "threshold across them, but nothing",
        "beyond the measured range is implied.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        f"Real sieve vs random projection and the c=1 frontier (layer {anchor_layer}, r={anchor_r}, Q=101)",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "Adversariality Phase Transition in 2-Gap Companions: square-window survival vs the real sieve",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = load_rows()
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "frontier-comparison-Q101.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
