"""Implied-spacing chart: the same four trajectories as four_lines_chart.py,
viewed as spacing between consecutive 2-gaps instead of raw survivor counts.

Reads ../../../data/candidates/spacing-Q101.csv (written by
sieve_sequence_empirical.spacing_cli -- run that first, which itself reads
four-lines-Q101.csv from sieve_sequence_empirical.four_lines_cli) rather than
recomputing anything.

Why this view exists: a survivor *count* trending toward zero reads
visually as extinction, even for a trajectory (like the random projection)
that provably never reaches it. The reciprocal view -- spacing between
consecutive 2-gaps -- grows instead of shrinking, which matches how the
process actually behaves: 2-gaps get rarer, not gone. Only a genuine
extinction (a count that actually hits zero, as the adversarial floor does)
shows up here, as an explicit X marker where the line becomes infinite,
instead of an optical illusion produced by an ordinary shrinking count.

See empirical/sieve-sequence/src/sieve_sequence_empirical/spacing.py for why
this is a reciprocal-scaling transform of the four_lines.py counts, not a
second, independent model.

Run: python3 spacing_chart.py
Output: ./out/spacing-Q101.svg
"""

import csv
import datetime
import os
import subprocess
import sys

from .svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "charts")
DATA_PATH = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "candidates", "spacing-Q101.csv"
)

# Same palette and color-to-trajectory assignment as four_lines_chart.py, for
# visual consistency between the two companion charts.
COLOR_EMPIRICAL = "#2a78d6"    # blue -- the real data, solid
COLOR_RANDOM = "#4a3aa7"       # violet -- C_p=1/2 projection, dashed
COLOR_FRIENDLY = "#008300"     # green -- C_p=0 ceiling, dashed
COLOR_ADVERSARIAL = "#e34948"  # red -- proved worst-case floor, dashed

# Distinct dash pattern per line, matching four_lines_chart.py -- color alone
# doesn't survive grayscale/print/colorblind viewing.
DASH_EMPIRICAL = None
DASH_FRIENDLY = "1,4"
DASH_RANDOM = "7,4"
DASH_ADVERSARIAL = "10,3,2,3"

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"


def vertical_text(canvas, x, y, label, size=12, fill=INK_MUTED):
    """A y-axis label rotated -90deg around (x, y). See four_lines_chart.py
    for why svg_kit.Canvas.text (no rotation option) isn't enough here."""
    canvas.elements.append(
        f'<text x="{x}" y="{y}" font-family="{canvas.font_family}" font-size="{size}" '
        f'font-weight="normal" font-style="normal" fill="{fill}" '
        f'text-anchor="middle" transform="rotate(-90 {x} {y})">{escape(label)}</text>'
    )


def load_rows():
    with open(DATA_PATH, newline="") as f:
        rows = list(csv.DictReader(f))
    for row in rows:
        for col in ("spacing_friendly", "spacing_random", "spacing_adversarial", "spacing_empirical"):
            row[col] = float(row[col])  # float("inf") parses fine
    return rows


def draw(rows):
    left, right, top, bottom = 70, 210, 50, 60
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

    # Scale off the three well-behaved lines only. The adversarial line's
    # finite values right before it hits infinity blow up fast (e.g. into
    # the hundreds, next to the others' tens) -- including them here would
    # let one outlier squash the other three lines down near the bottom.
    # Excluding them means the adversarial line instead visibly clips into
    # the infinite band as it approaches its own extinction, which is an
    # honest picture of "rushing toward infinity," not a scaling artifact.
    well_behaved = [
        row[col] for row in rows
        for col in ("spacing_friendly", "spacing_random", "spacing_empirical")
        if row[col] != float("inf")
    ]
    y_hi = max(well_behaved) * 1.15
    # Reserve the top band of the plot for the "infinite" zone: any value
    # at or above y_hi maps into this band instead of off the canvas.
    infinity_y = top + 14

    def to_x(layer):
        span = (x_hi - x_lo) or 1
        return left + (layer - x_lo) / span * plot_w

    def to_y(value):
        if value == float("inf") or value > y_hi:
            return infinity_y
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
    for row in rows:
        canvas.text(to_x(int(row["layer"])), top + plot_h + 18, row["r"], size=10, anchor="middle", fill=INK_MUTED)
    canvas.text(left + plot_w / 2, top + plot_h + 38, "installed filter r", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, top + plot_h / 2, "implied spacing between 2-gaps", size=12, fill=INK_MUTED)

    def draw_series(col, color, dash):
        """Draw a series up to (and including, as an X) its first infinite
        point, then stop -- an infinite spacing means no further 2-gap is
        predicted, so nothing after it is meaningful to plot as a line."""
        pts = []
        x_marks = []
        for row in rows:
            v = row[col]
            xy = (to_x(int(row["layer"])), to_y(v))
            if v == float("inf"):
                x_marks.append(xy)
                break
            pts.append(xy)
        if len(pts) > 1:
            canvas.polyline(pts, stroke=color, width=2.5 if dash is None else 2, dash=dash)
        for x, y in x_marks:
            canvas.cross(x, y, size=7, stroke=color, width=2.5)

    draw_series("spacing_friendly", COLOR_FRIENDLY, DASH_FRIENDLY)
    draw_series("spacing_random", COLOR_RANDOM, DASH_RANDOM)
    draw_series("spacing_adversarial", COLOR_ADVERSARIAL, DASH_ADVERSARIAL)
    draw_series("spacing_empirical", COLOR_EMPIRICAL, DASH_EMPIRICAL)

    # anchor marker: all four lines agree here by construction
    ax, ay = to_x(anchor_layer), to_y(float(rows[0]["ref_spacing"]))
    canvas.circle(ax, ay, r=5, fill="white", stroke=INK_PRIMARY, width=2)

    canvas.text(left + 8, infinity_y - 6, "infinite (extinction)", size=9, anchor="start", fill=INK_MUTED, style="italic")

    # legend -- right margin, outside the plot's x-range (see
    # four_lines_chart.py for why: the flat friendly line spans the full
    # plot width, so any legend inside the plot collides with it somewhere).
    legend_x, legend_y = left + plot_w + 24, top + 24
    entries = [
        ("empirical (real data)", COLOR_EMPIRICAL, DASH_EMPIRICAL),
        ("random (C_p=1/2)", COLOR_RANDOM, DASH_RANDOM),
        ("friendly (C_p=0)", COLOR_FRIENDLY, DASH_FRIENDLY),
        ("adversarial (C_p=1)", COLOR_ADVERSARIAL, DASH_ADVERSARIAL),
    ]
    canvas.text(legend_x, legend_y - 14, "trajectory", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color, dash) in enumerate(entries):
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5 if dash is None else 2, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)
    cross_y = legend_y + len(entries) * 22 + 14
    canvas.cross(legend_x + 11, cross_y, size=6, stroke=INK_PRIMARY, width=2)
    canvas.text(legend_x + 30, cross_y + 4, "X = extinction (count hit 0)", size=10, anchor="start", fill=INK_MUTED)
    canvas.text(legend_x, cross_y + 26, "solid = real data", size=10, anchor="start", fill=INK_MUTED)
    canvas.text(legend_x, cross_y + 42, "dashed = projection", size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        f"Implied spacing between 2-gaps (layer {anchor_layer}, r={anchor_r}, Q=101)",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "empirical/sieve-sequence/src/sieve_sequence_empirical/spacing.py -- reciprocal view of four-lines-Q101.csv",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = load_rows()
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "spacing-Q101.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
