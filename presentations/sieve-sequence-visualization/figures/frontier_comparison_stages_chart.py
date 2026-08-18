"""Wide-range real-sieve frontier chart: per-filter 2-gap destruction fraction
vs the random and c=1 frontier benchmarks, over all measured stages to large
primes.

Companion to frontier_comparison_chart.py (which tracks ONE fixed lineage
window [Q,Q^2) toward Q=101 over ~16 layers). This version loads the much
larger per-stage measurements -- data/candidates/window-measurements.csv
(dense, p to ~1000) and window-measurements-sparse.csv (sparse sample, p to
~19000) -- so the same empirical-vs-random-vs-frontier comparison is carried
to far bigger primes.

Semantics per stage (p, q = consecutive primes, window [q, q^2)):
  - G_local   real 2-gap starts in the window before installing filter p
  - destroyed real 2-gap starts destroyed by installing p (<= worst_case_A)
  - empirical curve = destroyed / G_local
  - random benchmark  = 2/p            (w_r=1: destroys 2 of p residues)
  - frontier benchmark = 2*(1+ln p)/p  (w_r=1+ln p: the article's c=1
                                       square-window threshold, Property IV)

Because q is the NEXT prime after p (so q~p, hence q^2/p ~ p), the destroyed
count is bounded by the number of primes in [p, q^2/p], a constant ~1-3, while
G_local grows like q^2/(ln q)^2 -- so the measured fraction falls far below
both benchmarks at large p. That is the real-sieve signal this chart shows.

Display choices:
- Log-log axes: both benchmarks are cleanly visible and the empirical cloud
  spans ~5 decades of destruction fraction.
- Stages where destroyed=0 (rate exactly 0) cannot sit on a log axis; they are
  drawn on a floor at 10^-7 with a smaller marker and called out in the note.
- The frontier benchmark 2*(1+ln p)/p exceeds 1 for p<7 (the f_r<1 premise
  fails there); that curve starts at p=7.

Solid/dashed and color conventions match the other phase-transition charts:
blue = real data, violet = the random baseline, black = the c=1 frontier.

Run: python3 frontier_comparison_stages_chart.py
Output: ./out/frontier-comparison-stages.svg
"""

import csv
import datetime
import math
import os
import subprocess
import sys

from svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")
DENSE_PATH = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "candidates", "window-measurements.csv"
)
SPARSE_PATH = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "candidates", "window-measurements-sparse.csv"
)

COLOR_EMPIRICAL = "#2a78d6"    # blue -- the real data
COLOR_RANDOM = "#e34948"       # red -- 2/p benchmark, dashed
COLOR_FRONTIER = "#111111"     # black -- 2*(1+ln p)/p benchmark, dashed

DASH_RANDOM = "7,4"
DASH_FRONTIER = "10,3,2,3"

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"

RATE_FLOOR = 1e-7  # drawn position for stages where destroyed = 0


def vertical_text(canvas, x, y, label, size=12, fill=INK_MUTED):
    canvas.elements.append(
        f'<text x="{x}" y="{y}" font-family="{canvas.font_family}" font-size="{size}" '
        f'font-weight="normal" font-style="normal" fill="{fill}" '
        f'text-anchor="middle" transform="rotate(-90 {x} {y})">{escape(label)}</text>'
    )


def load_stages():
    stages = []
    for path in (DENSE_PATH, SPARSE_PATH):
        with open(path, newline="") as f:
            for row in csv.DictReader(f):
                p = int(float(row["p"]))
                g = float(row["G_local"])
                if g <= 0:
                    continue
                destroyed = int(float(row["destroyed"]))
                stages.append((p, destroyed / g if destroyed else 0.0))
    stages.sort(key=lambda s: s[0])
    return stages


def draw(stages):
    left, right, top, bottom = 70, 270, 50, 85
    plot_w, plot_h = 480, 380
    W = left + plot_w + right
    H = top + plot_h + bottom
    canvas = Canvas(W, H)

    canvas.comment(f"Generated: {datetime.datetime.now().isoformat()}")
    canvas.comment(f"Script: {os.path.basename(__file__)}")
    canvas.comment(f"Python: {sys.version}")
    canvas.comment(f"Input: {DENSE_PATH}")
    canvas.comment(f"Input: {SPARSE_PATH}")
    try:
        commit = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], text=True).strip()
        canvas.comment(f"Git commit: {commit}")
    except Exception:
        canvas.comment("Git commit: unknown")

    x_lo, x_hi = math.log10(3.0), math.log10(20000.0)
    y_lo, y_hi = -7.5, 0.6

    def to_x(lp):
        return left + (lp - x_lo) / (x_hi - x_lo) * plot_w

    def to_y(rate):
        lr = math.log10(max(rate, 1e-12))
        return top + plot_h - (lr - y_lo) / (y_hi - y_lo) * plot_h

    canvas.line(left, top, left, top + plot_h, stroke=GRID, width=1)
    canvas.line(left, top + plot_h, left + plot_w, top + plot_h, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = top + plot_h - frac * plot_h
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        val = y_lo + frac * (y_hi - y_lo)
        canvas.text(left - 10, y + 4, f"1e{val:.0f}", size=11, anchor="end", fill=INK_MUTED)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        x = left + frac * plot_w
        val = x_lo + frac * (x_hi - x_lo)
        canvas.line(x, top, x, top + plot_h, stroke=GRID, width=1)
        canvas.text(x, top + plot_h + 18, f"{10 ** val:.0f}", size=10, anchor="middle", fill=INK_MUTED)
    canvas.text(left + plot_w / 2, top + plot_h + 38, "filter p (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, top + plot_h / 2, "fraction of 2-gap starts destroyed by p", size=12, fill=INK_MUTED)

    # benchmarks
    bench_pts = []
    for lp in [x_lo + (x_hi - x_lo) * i / 300 for i in range(301)]:
        p = 10 ** lp
        if p < 7:
            continue
        bench_pts.append((lp, p))
    # empirical stages -- drawn first (below the benchmark lines) so the
    # benchmarks stay visible where the measured cloud sits on them
    dense = [(p, rate) for p, rate in stages if p < 1000]
    sparse = [(p, rate) for p, rate in stages if p >= 1000]
    for p, rate in dense:
        canvas.circle(to_x(math.log10(p)), to_y(rate if rate > 0 else RATE_FLOOR),
                      r=2.2, fill=COLOR_EMPIRICAL, stroke=COLOR_EMPIRICAL, width=1, opacity=0.55)
    for p, rate in sparse:
        canvas.circle(to_x(math.log10(p)), to_y(rate if rate > 0 else RATE_FLOOR),
                      r=2.5, fill=COLOR_EMPIRICAL, stroke=COLOR_EMPIRICAL, width=1, opacity=0.55)
    canvas.polyline(
        [(to_x(lp), to_y(2.0 / p)) for lp, p in bench_pts],
        stroke=COLOR_RANDOM, width=2, dash=DASH_RANDOM,
    )
    canvas.polyline(
        [(to_x(lp), to_y(2.0 * (1.0 + math.log(p)) / p)) for lp, p in bench_pts],
        stroke=COLOR_FRONTIER, width=2, dash=DASH_FRONTIER,
    )

    legend_x, legend_y = left + plot_w + 24, top + 24
    entries = [
        ("empirical (real sieve, per stage)", COLOR_EMPIRICAL, None, "point"),
        ("random benchmark 2/p (w_r=1)", COLOR_RANDOM, DASH_RANDOM, "line"),
        ("c=1 frontier 2(1+ln p)/p", COLOR_FRONTIER, DASH_FRONTIER, "line"),
    ]
    canvas.text(legend_x, legend_y - 14, "per-filter destruction", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color, dash, kind) in enumerate(entries):
        y = legend_y + i * 22
        if kind == "point":
            canvas.circle(legend_x + 11, y, r=2.8, fill=COLOR_EMPIRICAL, stroke=COLOR_EMPIRICAL, width=1, opacity=0.55)
            canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)
        else:
            canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2, dash=dash)
            canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)
    note_y = legend_y + len(entries) * 22 + 16
    for i, line in enumerate([
        "Real 2-gap destruction fraction in the",
        "head window [q,q^2), dense to p=997 plus",
        "a sparse sample to p~19400.",
        "",
        "At large p the real sieve destroys far",
        "less than the random benchmark 2/p --",
        "the destroyed count is O(1), bounded by",
        "the primes in [p, q^2/p].",
        "",
        "Smaller blue dots = stages with zero",
        "destruction, drawn on the 10^-7 floor.",
        "Finite measurement: no claim beyond the",
        "measured range is implied.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "Per-filter 2-gap destruction vs the random and c=1 benchmarks, p to ~19400",
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
    stages = load_stages()
    canvas = draw(stages)
    out_path = os.path.join(OUT_DIR, "frontier-comparison-stages.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path} ({len(stages)} measured stages)")


if __name__ == "__main__":
    main()
