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
threshold is c=1/2 -- c=0.1 climbs the whole way, c>=0.5 all flatten out.

c=0.3 is included deliberately as a subtle case: it is still climbing at
the right edge of this chart (per the proof, it must diverge, being below
1/2), but far more slowly than c=0.1 -- a real illustration of how close to
the boundary the divergence becomes numerically hard to distinguish from
convergence, not a rendering artifact.

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

C_VALUES = [0.1, 0.3, 0.5, 0.7, 1.0, 1.5]
COLUMN_FOR_C = {c: f"cumsum_c{str(c).replace('.', '_')}" for c in C_VALUES}

COLORS = ["#2a78d6", "#1baf7a", "#eda100", "#008300", "#4a3aa7", "#e34948"]
DASHES = ["1,4", "7,4", "10,3,2,3", "4,2,1,2,1,2", "10,3,2,3,2,3", None]

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
        rows = list(csv.DictReader(f))
    for row in rows:
        row["Q"] = float(row["Q"])
        for c in C_VALUES:
            row[COLUMN_FOR_C[c]] = float(row[COLUMN_FOR_C[c]])
    return rows


def draw(rows):
    left, right, top, bottom = 70, 280, 50, 60
    plot_w, plot_h = 460, 380
    W = left + plot_w + right
    H = top + plot_h + bottom
    canvas = Canvas(W, H)

    log_Q = [math.log10(r["Q"]) for r in rows]
    x_lo, x_hi = min(log_Q), max(log_Q)
    y_max = max(max(r[COLUMN_FOR_C[c]] for c in C_VALUES) for r in rows)
    y_lo, y_hi = 0.0, y_max * 1.08

    def to_x(lq):
        return left + (lq - x_lo) / (x_hi - x_lo) * plot_w

    def to_y(value):
        return top + plot_h - (value / (y_hi - y_lo)) * plot_h

    canvas.line(left, top, left, top + plot_h, stroke=GRID, width=1)
    canvas.line(left, top + plot_h, left + plot_w, top + plot_h, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = top + plot_h - frac * plot_h
        val = frac * (y_hi - y_lo)
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        canvas.text(left - 10, y + 4, f"{val:.0f}", size=11, anchor="end", fill=INK_MUTED)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        x = left + frac * plot_w
        val = x_lo + frac * (x_hi - x_lo)
        canvas.line(x, top, x, top + plot_h, stroke=GRID, width=1)
        canvas.text(x, top + plot_h + 18, f"{val:.1f}", size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, top + plot_h + 38, "log10(Q)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, top + plot_h / 2, "cumulative sum of Pr(head is a 2-gap)", size=12, fill=INK_MUTED)

    def series(c):
        col = COLUMN_FOR_C[c]
        return [(to_x(math.log10(r["Q"])), to_y(r[col])) for r in rows]

    for c, color, dash in zip(C_VALUES, COLORS, DASHES):
        canvas.polyline(series(c), stroke=color, width=2.5 if dash is None else 2, dash=dash)

    legend_x, legend_y = left + plot_w + 24, top + 24
    labels = {
        0.1: "c=0.1 (climbs clearly)",
        0.3: "c=0.3 (climbs, but slowly)",
        0.5: "c=0.5 (boundary: converges)",
        0.7: "c=0.7 (converges fast)",
        1.0: "c=1.0 (converges)",
        1.5: "c=1.5 (converges instantly)",
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
        "A climbing curve = the Borel-Cantelli",
        "sum diverges = infinitely many head",
        "hits, with mixing. A flat curve = only",
        "finitely many, almost surely.",
        "",
        "c=0.3 is still technically climbing at",
        "the right edge -- proved divergent,",
        "just numerically slow near c=1/2.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "Head recurrence: the c=1/2 Borel-Cantelli boundary",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "articles/draft/draft-adversariality-phase-transition-2-gap-companions.md -- Property IV (section 5.2)",
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
