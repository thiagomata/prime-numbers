"""Per-sequence frontier chart: real 2-gap counts in [h, h^2) vs the random and
c=1 frontier expectations, one point per sieve sequence (head h).

Companion to frontier_comparison_chart.py (one fixed lineage, Q=101) and
frontier_comparison_stages_chart.py (per-transition destruction fractions).
This one uses the much larger per-sequence dataset behind the giant heatmaps:
data/sieve-sequence/first_gaps_per_seq.csv (written by generate_gaps.py), which
records, for each of 200 stages/heads h, the ordered list of actual survivors
(numbers coprime to every prime below h). From it each head's own square window
[h, h^2) yields:

  empirical  = count of 2-gap starts (x, x+2) in [h, h^2) -- the real
               per-sequence square-window 2-gap population
  random     = |W| * (1/2) * prod_{3<=r<h}(1-2/r) -- the complete-period
               expected 2-gap count (the same main_term as lib.py #10)
  frontier   = random * prod_{7<=r<h}(1 - 2 ln(r)/(r-2)) -- random expectation
               under the article's c=1 log-growth excess w_r = 1 + ln r
               (Property IV), relative to the random baseline

The window [h, h^2) is fully inside the 100k-gap prefix only for heads up to
1129 (188 sequences); the last 12 heads (1151..1229) are partially covered and
excluded from the empirical points, with the coverage limit noted in the plot.

Display choices:
- Log-log axes (head h vs 2-gap count): the empirical points, the random
  expectation, and the collapsing frontier expectation are all visible.
- Empirical as points so the near-random tracking stays legible even where it
  overlaps the random expectation line.
- Colors/dashes match the other phase-transition charts: blue = real data,
  violet = random baseline, black = c=1 frontier.

Run: python3 per_sequence_frontier_chart.py
Output: ./out/per-sequence-frontier.svg
"""

import csv
import datetime
import math
import os
import subprocess
import sys

from svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")
CSV_PATH = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "sieve-sequence", "first_gaps_per_seq.csv"
)

COLOR_EMPIRICAL = "#2a78d6"    # blue -- the real data
COLOR_RANDOM = "#e34948"       # red -- random expectation, dashed
COLOR_FRONTIER = "#111111"     # black -- c=1 frontier expectation, dashed

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


def primes_upto(n):
    is_p = [True] * (n + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if is_p[i]:
            for j in range(i * i, n + 1, i):
                is_p[j] = False
    return [i for i in range(n + 1) if is_p[i]]


def load_stages():
    by_index = {}
    with open(CSV_PATH, newline="") as f:
        for row in csv.DictReader(f):
            idx = int(row["stage_index"])
            entry = by_index.setdefault(idx, {"head": int(row["head"]), "survivors": []})
            entry["survivors"].append(int(row["survivor"]))
    return [by_index[i] for i in sorted(by_index)]


def build_series(stages):
    max_head = max(s["head"] for s in stages)
    primes = primes_upto(max_head)
    dens = 0.5      # the (1/2) pair-density factor, then prod_{3<=r<h}(1-2/r)
    fr = 1.0        # prod_{7<=r<h}(1 - 2 ln(r)/(r-2)), the frontier excess ratio
    pi = 0
    rows = []
    for s in stages:
        h = s["head"]
        while pi < len(primes) and primes[pi] < h:
            r = primes[pi]
            if r >= 3:
                dens *= (1.0 - 2.0 / r)
            if r >= 7:
                fr *= (1.0 - 2.0 * math.log(r) / (r - 2.0))
            pi += 1
        hi = h * h
        inwin = [x for x in s["survivors"] if h <= x < hi]
        xs = set(inwin)
        g2 = sum(1 for x in inwin if x + 2 in xs)
        full = s["survivors"][-1] >= hi
        main_term = (hi - h) * dens
        rows.append({"h": h, "g2": g2, "full": full,
                     "main": main_term, "frontier": main_term * fr})
    return rows


def draw(rows):
    left, right, top, bottom = 70, 270, 50, 85
    plot_w, plot_h = 480, 380
    W = left + plot_w + right
    H = top + plot_h + bottom
    canvas = Canvas(W, H)

    canvas.comment(f"Generated: {datetime.datetime.now().isoformat()}")
    canvas.comment(f"Script: {os.path.basename(__file__)}")
    canvas.comment(f"Python: {sys.version}")
    canvas.comment(f"Input: {CSV_PATH}")
    try:
        commit = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], text=True).strip()
        canvas.comment(f"Git commit: {commit}")
    except Exception:
        canvas.comment("Git commit: unknown")

    full = [r for r in rows if r["full"]]
    x_lo, x_hi = math.log10(3.0), math.log10(1230.0)
    y_lo, y_hi = -2.2, math.log10(max(r["g2"] for r in full) * 1.3)

    def to_x(lp):
        return left + (lp - x_lo) / (x_hi - x_lo) * plot_w

    def to_y(v):
        return top + plot_h - (math.log10(v) - y_lo) / (y_hi - y_lo) * plot_h

    canvas.line(left, top, left, top + plot_h, stroke=GRID, width=1)
    canvas.line(left, top + plot_h, left + plot_w, top + plot_h, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = top + plot_h - frac * plot_h
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        val = y_lo + frac * (y_hi - y_lo)
        canvas.text(left - 10, y + 4, f"1e{val:.1f}", size=11, anchor="end", fill=INK_MUTED)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        x = left + frac * plot_w
        val = x_lo + frac * (x_hi - x_lo)
        canvas.line(x, top, x, top + plot_h, stroke=GRID, width=1)
        canvas.text(x, top + plot_h + 18, f"{10 ** val:.0f}", size=10, anchor="middle", fill=INK_MUTED)
    canvas.text(left + plot_w / 2, top + plot_h + 38, "sequence head h (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, top + plot_h / 2, "2-gap starts in [h, h^2)", size=12, fill=INK_MUTED)

    for r in full:
        canvas.circle(to_x(math.log10(r["h"])), to_y(r["g2"]),
                      r=2.2, fill=COLOR_EMPIRICAL, stroke=COLOR_EMPIRICAL, width=1, opacity=0.55)
    canvas.polyline(
        [(to_x(math.log10(r["h"])), to_y(r["main"])) for r in full],
        stroke=COLOR_RANDOM, width=2, dash=DASH_RANDOM,
    )
    canvas.polyline(
        [(to_x(math.log10(r["h"])), to_y(r["frontier"])) for r in full],
        stroke=COLOR_FRONTIER, width=2, dash=DASH_FRONTIER,
    )

    legend_x, legend_y = left + plot_w + 24, top + 24
    entries = [
        ("empirical (real 2-gaps in [h,h^2))", COLOR_EMPIRICAL, None, "point"),
        ("random expectation (w_r=1)", COLOR_RANDOM, DASH_RANDOM, "line"),
        ("c=1 frontier expectation (w_r=1+ln r)", COLOR_FRONTIER, DASH_FRONTIER, "line"),
    ]
    canvas.text(legend_x, legend_y - 14, "per sequence (head h)", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color, dash, kind) in enumerate(entries):
        y = legend_y + i * 22
        if kind == "point":
            canvas.circle(legend_x + 11, y, r=2.8, fill=COLOR_EMPIRICAL, stroke=COLOR_EMPIRICAL, width=1, opacity=0.55)
        else:
            canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)
    note_y = legend_y + len(entries) * 22 + 16
    for i, line in enumerate([
        "One point per sieve sequence: the full",
        "window [h,h^2) is measured for heads",
        "3..1129 (188 sequences); the 12 heads",
        "beyond it have partial coverage and",
        "are excluded.",
        "",
        "The real 2-gap counts track the random",
        "expectation within a few percent; the",
        "c=1 frontier expectation collapses with",
        "h, and the real sieve stays orders of",
        "magnitude above it.",
        "",
        "Finite measurement: no claim beyond",
        "head 1129 is implied.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "Per-sequence 2-gap counts vs the random and c=1 frontier expectations",
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
    rows = build_series(stages)
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "per-sequence-frontier.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path} ({len(rows)} sequences, "
          f"{sum(1 for r in rows if r['full'])} with full window coverage)")


if __name__ == "__main__":
    main()
