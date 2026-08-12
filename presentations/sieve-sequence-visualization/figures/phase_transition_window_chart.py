"""Phase-transition chart 1: "No finite constant is fatal."

Reads ../../../data/candidates/phase-transition-window.csv (written by
sieve_sequence_empirical.phase_transition_window_cli -- run that first)
rather than recomputing anything.

Plots the expected square-safe-window occupancy lambda(Q), in log10 form,
for several *fixed* relative-hazard factors w (draft article
articles/draft/draft-adversariality-phase-transition-2-gap-companions.md,
Property III, section 5.1) against a constant per-filter adversarial share
(section 7) and the log-growth frontier at c=1 (Property IV, section 5.2).
The article proves every fixed finite w survives (lambda->infinity) no
matter how large -- w=6 and w=10 visibly *dip* before recovering, since Q^2
needs to grow astronomically large before it overtakes (ln Q)^(2w); a
constant positive share, by contrast, is fatal almost immediately and
permanently (lambda->0), because its relative-hazard factor w_r ~ alpha*r/2
grows linearly in r rather than staying fixed. The c=1 frontier sits
exactly on the article's own square-window boundary: still climbs, but at
the slowest possible rate before the regime flips -- it is the actual
threshold this chart is about, so it gets the solid stroke; every other
line is dashed.

This is a purely analytic/asymptotic comparison, not real measured data
(unlike four_lines_chart.py / spacing_chart.py), so Q is pushed to
astronomical values (log10(Q) up to 60) specifically to make the w=10
recovery visible -- something no real measurement could ever reach.

Color is shared with phase_transition_head_chart.py wherever the two
charts describe the same underlying quantity: w=1 here is exactly c=0
there (both mean w_r=1 constant, the true-random baseline), and the c=1
frontier here is exactly the c=1.0 line there -- both share the identical
color in both charts so a reader can carry the mapping between them, even
though the frontier is drawn solid here (it is this chart's own boundary)
and dashed there (that chart's boundary is c=0.5, not c=1.0).

Run: python3 phase_transition_window_chart.py
Output: ./out/phase-transition-window.svg
"""

import csv
import os

from svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")
DATA_PATH = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "candidates", "phase-transition-window.csv"
)

# Categorical palette (references/palette.md in the dataviz skill), same
# family used across the other companion-process charts. Distinct dash
# pattern per line as well as color -- see feedback memory on grayscale/
# print/colorblind safety for multi-series line charts. w=1 and the c=1
# frontier intentionally share color with phase_transition_head_chart.py's
# c=0.0 and c=1.0 -- see module docstring.
COLOR_W1 = "#2a78d6"        # blue -- true-random baseline, matches head chart's c=0.0
COLOR_W3 = "#1baf7a"        # aqua
COLOR_W6 = "#eda100"        # yellow
COLOR_W10 = "#008300"       # dark green
COLOR_SHARE = "#e34948"     # red -- the one that dies
COLOR_FRONTIER = "#4a3aa7"  # violet -- c=1 frontier, matches head chart's c=1.0

DASH_W1 = "1,4"
DASH_W3 = "7,4"
DASH_W6 = "10,3,2,3"
DASH_W10 = "4,2,1,2,1,2"
DASH_SHARE = "2,2"
DASH_FRONTIER = None  # solid -- the article's own exact square-window threshold

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"

Y_FLOOR = -15.0  # below this, a curve is "effectively extinct" -- clip and note it


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
        for col in row:
            row[col] = float(row[col])
    return rows


def draw(rows):
    left, right, top, bottom = 70, 270, 50, 85
    plot_w, plot_h = 480, 380
    W = left + plot_w + right
    H = top + plot_h + bottom
    canvas = Canvas(W, H)

    x_lo = min(r["log10_Q"] for r in rows)
    x_hi = max(r["log10_Q"] for r in rows)
    y_lo, y_hi = Y_FLOOR, 120.0

    def to_x(log10_Q):
        return left + (log10_Q - x_lo) / (x_hi - x_lo) * plot_w

    def to_y(value):
        clipped = max(y_lo, min(y_hi, value))
        return top + plot_h - (clipped - y_lo) / (y_hi - y_lo) * plot_h

    canvas.line(left, top, left, top + plot_h, stroke=GRID, width=1)
    canvas.line(left, top + plot_h, left + plot_w, top + plot_h, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = top + plot_h - frac * plot_h
        val = y_lo + frac * (y_hi - y_lo)
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        canvas.text(left - 10, y + 4, f"{val:.0f}", size=11, anchor="end", fill=INK_MUTED)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        x = left + frac * plot_w
        val = x_lo + frac * (x_hi - x_lo)
        canvas.line(x, top, x, top + plot_h, stroke=GRID, width=1)
        canvas.text(x, top + plot_h + 18, f"{val:.0f}", size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, top + plot_h + 38, "log10(Q)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, top + plot_h / 2, "log10(expected window occupancy)", size=12, fill=INK_MUTED)

    canvas.text(left + 8, to_y(Y_FLOOR) - 8, "clipped floor (effectively extinct below here)",
                size=9, anchor="start", fill=INK_MUTED, style="italic")

    def series(col):
        return [(to_x(r["log10_Q"]), to_y(r[col])) for r in rows]

    canvas.polyline(series("log10_lambda_fixed_w1"), stroke=COLOR_W1, width=2, dash=DASH_W1)
    canvas.polyline(series("log10_lambda_fixed_w3"), stroke=COLOR_W3, width=2, dash=DASH_W3)
    canvas.polyline(series("log10_lambda_fixed_w6"), stroke=COLOR_W6, width=2, dash=DASH_W6)
    canvas.polyline(series("log10_lambda_fixed_w10"), stroke=COLOR_W10, width=2, dash=DASH_W10)
    canvas.polyline(series("log10_lambda_constant_share"), stroke=COLOR_SHARE, width=2, dash=DASH_SHARE)
    canvas.polyline(series("log10_lambda_frontier_c1"), stroke=COLOR_FRONTIER, width=2.5, dash=DASH_FRONTIER)

    legend_x, legend_y = left + plot_w + 24, top + 24
    entries = [
        ("w=1 (true random baseline)", COLOR_W1, DASH_W1),
        ("w=3 (3x worse than random)", COLOR_W3, DASH_W3),
        ("w=6 (dips, then recovers)", COLOR_W6, DASH_W6),
        ("w=10 (dips much longer)", COLOR_W10, DASH_W10),
        ("constant 1% share (dies)", COLOR_SHARE, DASH_SHARE),
        ("c=1 frontier (window threshold)", COLOR_FRONTIER, DASH_FRONTIER),
    ]
    canvas.text(legend_x, legend_y - 14, "relative-hazard factor", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color, dash) in enumerate(entries):
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5 if dash is None else 2, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)
    note_y = legend_y + len(entries) * 22 + 16
    for i, line in enumerate([
        "Every fixed w -- however large --",
        "eventually climbs without bound.",
        "Only a share that GROWS with r",
        "(here: constant %, so w_r~r) dies.",
        "",
        "c=1 (w_r=1+log r) is the article's",
        "own square-window threshold: the",
        "slowest-climbing case that still",
        "survives, right before c>=1 dies.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "No finite relative-hazard factor is fatal to square-window survival",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "Adversariality Phase Transition in 2-Gap Companions: Square-Window Survival",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = load_rows()
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "phase-transition-window.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
