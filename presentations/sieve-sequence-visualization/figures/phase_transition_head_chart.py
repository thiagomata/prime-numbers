"""Phase-transition chart 2: the head-recurrence Borel-Cantelli boundary.

Reads ../../../data/candidates/phase-transition-head.csv (written by
sieve_sequence_empirical.phase_transition_head_cli -- run that first)
rather than recomputing anything.

Plots the *cumulative sum* of head-occurrence probability, summed over real
enumerated primes up to Q, for w_r = 1 + c*log(r) at several c (draft
article Property IV, section 5.2). This directly visualizes the
Borel-Cantelli criterion: a curve that keeps climbing means the sum
diverges (infinitely many head hits, with mixing); a curve that flattens
means the sum converges (only finitely many head hits). The article's
threshold is c=1/2 -- c=0.0 and c=0.1 climb the whole way, c>=0.5 all
flatten out.

The six c values are not arbitrary: c=0.0 is the true-random baseline
(w_r=1 exactly, matching the random benchmark elsewhere in this project --
realized-filter-adversariality-score.md's d_p=2/p at C_p=1/2), c=0.5 is the
article's own head threshold, and c=1.0 is its own square-window threshold
(section 5.2). 0.1 and 0.3 give a clearly- and a barely-divergent example
above the true-random baseline but still below the head threshold; 0.7
gives a convergent example between the two thresholds.

Color is shared with phase_transition_window_chart.py wherever the two
charts describe the same underlying quantity: c=0.0 here is exactly w=1
there (both mean w_r=1 constant, the true-random baseline), so both draw
that series in the same blue. The boundary itself -- this chart's c=0.5
and the window chart's c=1 frontier -- is drawn as the same solid black
line in both charts, so a reader sees the two thresholds as the same kind
of object. Every non-boundary series is dashed, and those dashed colors do
not carry across the two charts.

Two display choices, both fixes for an earlier draft of this chart:
- The y-axis is log10(cumulative sum), not the raw value. c=0.0's sum
  reaches into the hundreds while c=1.0's stays near 0.12; on a linear axis
  the smaller curves are indistinguishable flat lines at the bottom and
  c=0.0 visually swallows the chart. Log-space gives every curve's *shape*
  (still rising vs. flat) equal visual weight regardless of its absolute
  scale.
- The displayed Q range is trimmed to where the story actually resolves
  (Q up to ~2.5*10^5), not the full computed range (up to 10^7 in the CSV).
  By that point c=0.7/1.0 have been flat for a while -- c=0.5, right at the
  boundary, converges far more slowly (needs Q~1.8*10^6 to settle, checked
  directly against the CSV) and is still visibly approaching its limit at
  the right edge here, which is the honest picture at the boundary itself.

c=0.3 is included deliberately as a subtle case: it is still climbing at
the right edge of this chart (per the proof, it must diverge, being below
1/2), but far more slowly than c=0.0 or c=0.1 -- a real illustration of how
close to the boundary the divergence becomes numerically hard to
distinguish from convergence, not a rendering artifact.

Run: python3 phase_transition_head_chart.py
Output: ./out/phase-transition-head.svg
"""

import csv
import math
import os

from svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")
DATA_PATH = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "candidates", "phase-transition-head.csv"
)

C_VALUES = [0.0, 0.1, 0.3, 0.5, 0.7, 1.0]
COLUMN_FOR_C = {c: f"cumsum_c{str(c).replace('.', '_')}" for c in C_VALUES}

COLORS = ["#2a78d6", "#e34948", "#1baf7a", "#111111", "#eda100", "#4a3aa7"]
# c=0.5 (index 3) is the c=1/2 boundary itself -- the one solid line in this
# chart -- and it is drawn in the same solid black as the window chart's c=1
# frontier, so the two charts' thresholds read identically; every other c is
# dashed. c=0.0 (blue, "1,4") also matches that chart's w=1 baseline -- see
# docstring. The remaining dashed colors are local to this chart.
DASHES = ["1,4", "2,2", "7,4", None, "4,2,1,2,1,2", "10,3,2,3,2,3"]

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"

Q_MAX_DISPLAY = 250_000  # trims the long flat tail past 10^7 -- see module docstring


def vertical_text(canvas, x, y, label, size=12, fill=INK_MUTED):
    canvas.elements.append(
        f'<text x="{x}" y="{y}" font-family="{canvas.font_family}" font-size="{size}" '
        f'font-weight="normal" font-style="normal" fill="{fill}" '
        f'text-anchor="middle" transform="rotate(-90 {x} {y})">{escape(label)}</text>'
    )


def load_rows():
    with open(DATA_PATH, newline="") as f:
        rows = list(csv.DictReader(f))
    for row in rows:
        row["Q"] = float(row["Q"])
        for c in C_VALUES:
            row[COLUMN_FOR_C[c]] = float(row[COLUMN_FOR_C[c]])
    return [r for r in rows if r["Q"] <= Q_MAX_DISPLAY]


def draw(rows):
    left, right, top, bottom = 70, 280, 50, 85
    plot_w, plot_h = 460, 380
    W = left + plot_w + right
    H = top + plot_h + bottom
    canvas = Canvas(W, H)

    log_Q = [math.log10(r["Q"]) for r in rows]
    x_lo, x_hi = min(log_Q), max(log_Q)
    log_vals = [math.log10(r[COLUMN_FOR_C[c]]) for r in rows for c in C_VALUES]
    y_lo, y_hi = min(log_vals) - 0.2, max(log_vals) + 0.2

    def to_x(lq):
        return left + (lq - x_lo) / (x_hi - x_lo) * plot_w

    def to_y(value):
        log_v = math.log10(value)
        return top + plot_h - (log_v - y_lo) / (y_hi - y_lo) * plot_h

    canvas.line(left, top, left, top + plot_h, stroke=GRID, width=1)
    canvas.line(left, top + plot_h, left + plot_w, top + plot_h, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = top + plot_h - frac * plot_h
        log_val = y_lo + frac * (y_hi - y_lo)
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        canvas.text(left - 10, y + 4, f"{10 ** log_val:.2f}", size=11, anchor="end", fill=INK_MUTED)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        x = left + frac * plot_w
        val = x_lo + frac * (x_hi - x_lo)
        canvas.line(x, top, x, top + plot_h, stroke=GRID, width=1)
        canvas.text(x, top + plot_h + 18, f"{val:.1f}", size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, top + plot_h + 38, "log10(Q)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, top + plot_h / 2, "cumulative sum of Pr(head is a 2-gap) [log scale]", size=12, fill=INK_MUTED)

    def series(c):
        col = COLUMN_FOR_C[c]
        return [(to_x(math.log10(r["Q"])), to_y(r[col])) for r in rows]

    for c, color, dash in zip(C_VALUES, COLORS, DASHES):
        canvas.polyline(series(c), stroke=color, width=2.5 if dash is None else 2, dash=dash)

    legend_x, legend_y = left + plot_w + 24, top + 24
    labels = {
        0.0: "c=0.0 (true random, diverges)",
        0.1: "c=0.1 (diverges clearly)",
        0.3: "c=0.3 (diverges slowly)",
        0.5: "c=0.5 (boundary)",
        0.7: "c=0.7 (converges slowly)",
        1.0: "c=1.0 (converges clearly)",
    }
    canvas.text(legend_x, legend_y - 14, "w_r = 1 + c*log(r)", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, c in enumerate(C_VALUES):
        color, dash = COLORS[i], DASHES[i]
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5 if dash is None else 2, dash=dash)
        canvas.text(legend_x + 30, y + 4, labels[c], size=11, anchor="start", fill=INK_PRIMARY)

    note_y = legend_y + len(C_VALUES) * 22 + 16
    for i, line in enumerate([
        "Threshold is c=1/2 (draft Property IV).",
        "c=0.0 is the true-random baseline",
        "(w_r=1, no growing penalty at all).",
        "Y-axis is log-scale: a still-rising line",
        "means the Borel-Cantelli sum diverges",
        "(infinitely many head hits, with mixing);",
        "a flat line means it converges (only",
        "finitely many, almost surely).",
        "",
        "c=0.3 is still technically rising here --",
        "proved divergent, just numerically slow",
        "this close to the c=1/2 boundary.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "Head recurrence: the c=1/2 Borel-Cantelli boundary",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "Adversariality Phase Transition in 2-Gap Companions: Head Recurrence",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = load_rows()
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "phase-transition-head.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
