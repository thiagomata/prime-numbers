"""Four-lines chart: friendly ceiling, random projection, adversarial floor,
and the real measured trajectory, all anchored at one real point and plotted
together.

Reads ../../../data/candidates/four-lines-Q101.csv (written by
sieve_sequence_empirical.four_lines_cli -- run that first, which itself reads
lineage-Q101.csv from sieve_sequence_empirical.lineage_cli) rather than
recomputing anything.

See properties/sieve-sequence/realized-filter-adversariality-score.md,
section "Three Compounding Trajectories," for what each line means and what
is proved vs. projected vs. observed. In short:
  - friendly     proved trivial ceiling (survivors can never exceed N_0)
  - adversarial  proved worst-case floor (uses the proved capacity bound)
  - random       a projection under an unproved equidistribution assumption
  - empirical    the real measured counts -- not a projection at all

Solid line = real data. Dashed lines = theoretical projections, matching the
estimated/proven dashed-vs-solid convention already used in gap_heatmap.py's
boundary curves.

Run: python3 four_lines_chart.py
Output: ./out/four-lines-Q101.svg
"""

import csv
import os

from svg_kit import Canvas, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")
DATA_PATH = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "candidates", "four-lines-Q101.csv"
)

# Categorical palette (references/palette.md in the dataviz skill), validated
# for this exact 4-slot set: node scripts/validate_palette.js
# "#2a78d6,#4a3aa7,#008300,#e34948" --mode light -> ALL CHECKS PASS.
COLOR_EMPIRICAL = "#2a78d6"    # blue -- the real data, solid
COLOR_RANDOM = "#4a3aa7"       # violet -- C_p=1/2 projection, dashed
COLOR_FRIENDLY = "#008300"     # green -- C_p=0 ceiling, dashed
COLOR_ADVERSARIAL = "#e34948"  # red -- proved worst-case floor, dashed

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"


def load_rows():
    with open(DATA_PATH, newline="") as f:
        return list(csv.DictReader(f))


def draw(rows):
    left, right, top, bottom = 70, 210, 50, 60
    plot_w, plot_h = 500, 380
    W = left + plot_w + right
    H = top + plot_h + bottom
    canvas = Canvas(W, H)

    layers = [int(r["layer"]) for r in rows]
    x_lo, x_hi = min(layers), max(layers)
    y_max = max(
        max(float(r["N_friendly"]) for r in rows),
        max(float(r["N_empirical_pre"]) for r in rows),
    )
    y_hi = y_max * 1.08

    def to_x(layer):
        span = (x_hi - x_lo) or 1
        return left + (layer - x_lo) / span * plot_w

    def to_y(value):
        return top + plot_h - (value / y_hi) * plot_h

    # axes
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
    canvas.text(18, top + plot_h / 2, "surviving 2-gaps", size=12, anchor="middle", fill=INK_MUTED)

    def series(col):
        return [(to_x(int(r["layer"])), to_y(float(r[col]))) for r in rows]

    canvas.polyline(series("N_friendly"), stroke=COLOR_FRIENDLY, width=2, dash="5,4")
    canvas.polyline(series("N_random"), stroke=COLOR_RANDOM, width=2, dash="5,4")
    canvas.polyline(series("N_adversarial"), stroke=COLOR_ADVERSARIAL, width=2, dash="5,4")
    canvas.polyline(series("N_empirical_post"), stroke=COLOR_EMPIRICAL, width=2.5)

    # anchor marker: all four lines agree here by construction
    ax, ay = to_x(anchor_layer), to_y(float(rows[0]["anchor_n0"]))
    canvas.circle(ax, ay, r=5, fill="white", stroke=INK_PRIMARY, width=2)

    # legend -- lives entirely in the right margin, outside the plot's x-range,
    # so it can never cross a data line (the friendly line in particular is
    # flat across the full plot width, so any legend placed inside the plot
    # collides with it at some x).
    legend_x, legend_y = left + plot_w + 24, top + 24
    entries = [
        ("empirical (real data)", COLOR_EMPIRICAL, None),
        ("random (C_p=1/2)", COLOR_RANDOM, "5,4"),
        ("friendly (C_p=0)", COLOR_FRIENDLY, "5,4"),
        ("adversarial (C_p=1)", COLOR_ADVERSARIAL, "5,4"),
    ]
    canvas.text(legend_x, legend_y - 14, "trajectory", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color, dash) in enumerate(entries):
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5 if dash is None else 2, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)
    canvas.text(
        legend_x, legend_y + len(entries) * 22 + 14,
        "solid = real data", size=10, anchor="start", fill=INK_MUTED,
    )
    canvas.text(
        legend_x, legend_y + len(entries) * 22 + 30,
        "dashed = projection", size=10, anchor="start", fill=INK_MUTED,
    )

    canvas.text(
        W / 2, 22,
        f"Four trajectories from a real anchor (layer {anchor_layer}, r={anchor_r}, Q=101)",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "properties/sieve-sequence/realized-filter-adversariality-score.md -- \"Three Compounding Trajectories\"",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = load_rows()
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "four-lines-Q101.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
