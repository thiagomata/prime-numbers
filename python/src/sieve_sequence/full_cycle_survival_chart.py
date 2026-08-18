"""Normalized full-cycle 2-gap survival chart.

Shows products over 29 <= p <= r for exact-cycle 2-gap survival and the c=1
damage schedule. The r=29 anchor keeps every c=1 factor in (0, 1); changing
the anchor changes only the normalizing constants.

Run: python3 full_cycle_survival_chart.py
Output: ./out/full-cycle-survival.svg
"""

import datetime
import math
import os
import subprocess
import sys

from .svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "charts")

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"

COLOR_SURVIVAL = "#2a78d6"
COLOR_FRONTIER = "#111111"
DASH_FRONTIER = "10,3,2,3"


def vertical_text(canvas, x, y, label, size=12, fill=INK_MUTED):
    canvas.elements.append(
        f'<text x="{x}" y="{y}" font-family="{canvas.font_family}" font-size="{size}" '
        f'font-weight="normal" font-style="normal" fill="{fill}" '
        f'text-anchor="middle" transform="rotate(-90 {x} {y})">{escape(label)}</text>'
    )


def compute_layers(max_r=251, min_r=29):
    """Compute normalized full-cycle survival over the valid frontier range."""
    primes = []
    for n in range(min_r, max_r + 1):
        if all(n % p != 0 for p in range(2, int(n**0.5) + 1)) and n >= 2:
            primes.append(n)
    survival = 1.0
    frontier = 1.0
    rows = []
    for r in primes:
        survival *= (1.0 - 2.0 / r)
        w_f = 1.0 + math.log(r)
        f_f = 2.0 * w_f / r
        frontier *= (1.0 - f_f)
        rows.append({"r": r, "survival": survival, "frontier": frontier})
    return rows


def draw(rows):
    left, right, top, bottom = 82, 260, 88, 78
    plot_w = 560
    PANEL_H = 360

    W = left + plot_w + right
    H = top + PANEL_H + bottom
    canvas = Canvas(W, H)

    canvas.comment(f"Generated: {datetime.datetime.now().isoformat()}")
    canvas.comment(f"Script: {os.path.basename(__file__)}")
    canvas.comment(f"Python: {sys.version}")
    canvas.comment("Source: Computed inline — survival prod(1-2/r), frontier prod(1-2(1+ln r)/r)")
    try:
        commit = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], text=True).strip()
        canvas.comment(f"Git commit: {commit}")
    except Exception:
        canvas.comment("Git commit: unknown")

    r_values = [row["r"] for row in rows]
    surv_vals = [row["survival"] for row in rows]
    frontier_vals = [row["frontier"] for row in rows]

    x_lo = math.log(min(r_values))
    x_hi = math.log(max(r_values))

    def to_x(r):
        return left + (math.log(r) - x_lo) / (x_hi - x_lo) * plot_w

    tick_primes = [3, 5, 7, 11, 17, 23, 31, 43, 59, 79, 101, 127, 151,
                   179, 199, 229, 251]

    p_top = top
    p_bottom = p_top + PANEL_H

    y_hi = 1.0
    y_lo = 0.003

    def to_y(v):
        return p_bottom - (
            (math.log10(v) - math.log10(y_lo)) /
            (math.log10(y_hi) - math.log10(y_lo))
        ) * PANEL_H

    canvas.line(left, p_top, left, p_bottom, stroke=GRID, width=1)
    canvas.line(left, p_bottom, left + plot_w, p_bottom, stroke=GRID, width=1)
    for val, label in (
        (1.0, "100%"),
        (0.3, "30%"),
        (0.1, "10%"),
        (0.03, "3%"),
        (0.01, "1%"),
        (0.003, "0.3%"),
    ):
        y = to_y(val)
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        canvas.text(left - 10, y + 4, label, size=11, anchor="end", fill=INK_MUTED)

    for r in tick_primes:
        if min(r_values) <= r <= max(r_values):
            x = to_x(r)
            canvas.line(x, p_bottom, x, p_bottom + 5, stroke=INK_MUTED, width=1)
            canvas.text(x, p_bottom + 18, str(r), size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, p_bottom + 38, "filter prime r (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, p_top + PANEL_H / 2, "starting population remaining (log scale)", size=12, fill=INK_MUTED)

    # real survival (solid blue)
    pts_surv = [(to_x(row["r"]), to_y(row["survival"])) for row in rows]
    path_surv = " ".join(
        ("M" if i == 0 else "L") + f" {x} {y}"
        for i, (x, y) in enumerate(pts_surv)
    )
    canvas.elements.append(
        f'<path d="{path_surv}" fill="none" stroke="{COLOR_SURVIVAL}" '
        f'stroke-width="4" stroke-linejoin="round" />'
    )

    # c=1 frontier (dashed black)
    pts_front = [(to_x(row["r"]), to_y(row["frontier"])) for row in rows]
    path_front = " ".join(
        ("M" if i == 0 else "L") + f" {x} {y}"
        for i, (x, y) in enumerate(pts_front)
    )
    canvas.elements.append(
        f'<path d="{path_front}" fill="none" stroke="{COLOR_FRONTIER}" '
        f'stroke-width="4" stroke-dasharray="{DASH_FRONTIER}" '
        f'stroke-linejoin="round" />'
    )

    # Match the line-swatch legend used by the other frontier charts.
    legend_x = left + plot_w + 24
    legend_y = p_top + 18
    canvas.text(legend_x, legend_y - 14, "survival schedules", size=11,
                anchor="start", weight="bold", fill=INK_MUTED)
    legend_entries = [
        ("exact cycle: prod(1-2/p)", COLOR_SURVIVAL, None),
        ("c=1: prod(1-2(1+ln p)/p)", COLOR_FRONTIER, DASH_FRONTIER),
    ]
    for i, (label, color, dash) in enumerate(legend_entries):
        y = legend_y + i * 24
        canvas.line(legend_x, y, legend_x + 24, y, stroke=color, width=4,
                    dash=dash)
        canvas.text(legend_x + 32, y + 4, label, size=11,
                    anchor="start", fill=INK_PRIMARY)

    # Direct endpoint labels keep the comparison attached to the curves.
    end = rows[-1]
    label_x = to_x(end["r"]) + 12
    canvas.circle(to_x(end["r"]), to_y(end["survival"]), r=4,
                  fill=COLOR_SURVIVAL, stroke=COLOR_SURVIVAL, width=2)
    canvas.circle(to_x(end["r"]), to_y(end["frontier"]), r=4,
                  fill=COLOR_FRONTIER, stroke=COLOR_FRONTIER, width=2)
    canvas.text(label_x, to_y(end["survival"]) + 4,
                f'exact cycle: {100.0 * end["survival"]:.1f}%',
                size=11, anchor="start", weight="bold", fill=COLOR_SURVIVAL)
    canvas.text(label_x, to_y(end["frontier"]) + 4,
                f'c=1 schedule: {100.0 * end["frontier"]:.3f}%',
                size=11, anchor="start", weight="bold", fill=COLOR_FRONTIER)

    canvas.text(
        W / 2, 22,
        "How Much Complete-Cycle 2-Gap Survival Remains?",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, 44,
        "Both schedules start at 100% immediately before filter 29; each point includes filters through r.",
        size=11, anchor="middle", fill=INK_MUTED,
    )
    canvas.text(
        W / 2, 65,
        f'At r={end["r"]}: exact-cycle survival is {end["survival"] / end["frontier"]:.0f}x the c=1 schedule.',
        size=12, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "Finite reference comparison normalized at r=29; it does not measure head availability or recurrence.",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = compute_layers(max_r=251)
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "full-cycle-survival.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path} ({len(rows)} layers)")


if __name__ == "__main__":
    main()
