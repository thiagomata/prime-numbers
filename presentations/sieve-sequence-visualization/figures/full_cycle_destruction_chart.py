"""Full-cycle per-layer destruction rate chart.

Visualizes the exact identity f_cycle = 2/r and the matching neutral benchmark
at every plotted layer, with the c=1 frontier 2(1+ln r)/r for comparison.
No window, no Q parameter, no boundary noise.

Color and legend conventions match frontier_comparison_stages_chart.py:
  blue  = exact-cycle identity
  red   = random benchmark (dashed)
  black = c=1 frontier (dashed)

Run: python3 full_cycle_destruction_chart.py
Output: ./out/full-cycle-destruction.svg
"""

import datetime
import math
import os
import subprocess
import sys

from svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"

COLOR_REAL = "#2a78d6"
COLOR_RANDOM = "#e34948"
COLOR_FRONTIER = "#111111"

DASH_RANDOM = "7,4"
DASH_FRONTIER = "10,3,2,3"


def vertical_text(canvas, x, y, label, size=12, fill=INK_MUTED):
    canvas.elements.append(
        f'<text x="{x}" y="{y}" font-family="{canvas.font_family}" font-size="{size}" '
        f'font-weight="normal" font-style="normal" fill="{fill}" '
        f'text-anchor="middle" transform="rotate(-90 {x} {y})">{escape(label)}</text>'
    )


def compute_layers(max_r=251, min_r=29):
    """Compute exact full-cycle destruction over the valid frontier range."""
    primes = []
    for n in range(min_r, max_r + 1):
        if all(n % p != 0 for p in range(2, int(n**0.5) + 1)) and n >= 2:
            primes.append(n)
    T = 1
    rows = []
    for r in primes:
        expanded = T * r
        T_new = T * (r - 2)
        destroyed = expanded - T_new
        f_real = destroyed / expanded
        f_random = 2.0 / r
        rows.append({"r": r, "f_real": f_real, "f_random": f_random})
        T = T_new
    return rows


def draw(rows):
    left, right, top, bottom = 80, 250, 50, 85
    plot_w = 480
    PANEL_H = 380

    W = left + plot_w + right
    H = top + PANEL_H + bottom
    canvas = Canvas(W, H)

    canvas.comment(f"Generated: {datetime.datetime.now().isoformat()}")
    canvas.comment(f"Script: {os.path.basename(__file__)}")
    canvas.comment(f"Python: {sys.version}")
    try:
        commit = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], text=True).strip()
        canvas.comment(f"Git commit: {commit}")
    except Exception:
        canvas.comment("Git commit: unknown")

    r_values = [row["r"] for row in rows]
    x_lo = math.log(min(r_values))
    x_hi = math.log(max(r_values))

    def to_x(r):
        return left + (math.log(r) - x_lo) / (x_hi - x_lo) * plot_w

    tick_primes = [3, 5, 7, 11, 17, 23, 31, 43, 59, 79, 101, 127, 151,
                   179, 199, 229, 251]

    p_top = top
    p_bottom = p_top + PANEL_H

    y_hi = 0.75
    y_lo = 0.0

    def to_y(v):
        return p_bottom - (v - y_lo) / (y_hi - y_lo) * PANEL_H

    canvas.line(left, p_top, left, p_bottom, stroke=GRID, width=1)
    canvas.line(left, p_bottom, left + plot_w, p_bottom, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = p_bottom - frac * PANEL_H
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        val = y_lo + frac * (y_hi - y_lo)
        canvas.text(left - 10, y + 4, f"{val:.2f}", size=11, anchor="end", fill=INK_MUTED)

    for r in tick_primes:
        if min(r_values) <= r <= max(r_values):
            x = to_x(r)
            canvas.line(x, p_bottom, x, p_bottom + 5, stroke=INK_MUTED, width=1)
            canvas.text(x, p_bottom + 18, str(r), size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, p_bottom + 38, "filter prime r (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, p_top + PANEL_H / 2, "destruction rate f = destroyed / expanded", size=12, fill=INK_MUTED)

    # exact-cycle identity -- solid blue, semi-transparent so benchmark shows through
    pts_real = [(to_x(row["r"]), to_y(row["f_real"])) for row in rows]
    canvas.polyline(pts_real, stroke=COLOR_REAL, width=2, stroke_opacity=0.5)

    # random benchmark 2/r -- dashed red
    pts_rand = [(to_x(row["r"]), to_y(row["f_random"])) for row in rows]
    canvas.polyline(pts_rand, stroke=COLOR_RANDOM, width=2, dash=DASH_RANDOM)

    # c=1 frontier 2(1+ln r)/r -- dashed black
    pts_frontier = [(to_x(row["r"]), to_y(2.0 * (1.0 + math.log(row["r"])) / row["r"]))
                    for row in rows]
    canvas.polyline(pts_frontier, stroke=COLOR_FRONTIER, width=2, dash=DASH_FRONTIER)

    # Legend
    legend_x = left + plot_w + 24
    legend_y = p_top + 24

    entries = [
        ("exact-cycle identity 2/r", COLOR_REAL, None),
        ("random benchmark 2/r (w_r=1)", COLOR_RANDOM, DASH_RANDOM),
        ("c=1 frontier 2(1+ln r)/r", COLOR_FRONTIER, DASH_FRONTIER),
    ]
    for i, (label, color, dash) in enumerate(entries):
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)

    note_y = legend_y + len(entries) * 22 + 16
    for i, line in enumerate([
        "Exact modular cycle:",
        "T_new = T_old * (r - 2),",
        "so destroyed = 2 * T_old,",
        "f_cycle = 2/r exactly",
        "at every layer.",
        "",
        "The c=1 frontier shows what",
        "destruction would be if w_r",
        "grew as 1+ln r instead of 1.",
        "The exact-cycle rate stays below.",
        "",
        "No window, no Q parameter,",
        "no boundary noise.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "Per-layer 2-gap destruction in the exact modular cycle vs benchmarks",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "The exact-cycle destruction fraction equals the neutral 2/r benchmark; this is a count identity, not random placement.",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = compute_layers(max_r=251)
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "full-cycle-destruction.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path} ({len(rows)} layers)")


if __name__ == "__main__":
    main()
