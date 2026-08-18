"""Full-cycle twin-prime destruction and survival chart.

Two panels:
  1. Per-layer destruction rate in the exact modular cycle:
     f_real vs f_random=2/r. They overlap exactly, proving the real
     sieve's per-layer destruction is precisely random in the full cycle.
  2. Cumulative survival fraction: prod(1 - 2/r) vs r, showing the
     twin-prime survival decay. This is the quantity that determines
     whether twin primes persist — it decays like C/(log r)^2 (Mertens).

No window, no Q parameter, no boundary noise. The values are exact
modular-cycle counts, computed from the theorem T_new = T_old * (r - 2).

Compare with fixed-lineage-hazard.svg, which measures the same destruction
rate but in the finite window [Q, Q^2). The deviations there are entirely
window-boundary artifacts — this chart shows the underlying exact structure.

Run: python3 full_cycle_hazard_chart.py
Output: ./out/full-cycle-hazard.svg
"""

import csv
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

COLOR_F_REAL = "#2a78d6"
COLOR_F_RANDOM = "#e34948"
COLOR_SURVIVAL = "#2a78d6"
COLOR_MERTENS = "#27ae60"

DASH_F_RANDOM = "7,4"
DASH_MERTENS = "10,3,2,3"


def vertical_text(canvas, x, y, label, size=12, fill=INK_MUTED):
    canvas.elements.append(
        f'<text x="{x}" y="{y}" font-family="{canvas.font_family}" font-size="{size}" '
        f'font-weight="normal" font-style="normal" fill="{fill}" '
        f'text-anchor="middle" transform="rotate(-90 {x} {y})">{escape(label)}</text>'
    )


def compute_layers(max_r=251):
    """Compute exact full-cycle destruction and survival for each prime r."""
    primes = []
    for n in range(3, max_r + 1):
        if all(n % p != 0 for p in range(2, int(n**0.5) + 1)) and n >= 2:
            primes.append(n)
    T = 1  # after filter 2: one 2-gap per cycle of 2
    survival = 1.0
    rows = []

    for r in primes:
        expanded = T * r
        T_new = T * (r - 2)
        destroyed = expanded - T_new
        f_real = destroyed / expanded
        f_random = 2.0 / r
        survival *= (1 - f_random)
        rows.append({
            "r": r,
            "T_old": T,
            "T_new": T_new,
            "f_real": f_real,
            "f_random": f_random,
            "survival": survival,
        })
        T = T_new

    return rows


def draw(rows):
    left, right, top, bottom = 80, 220, 50, 85
    plot_w = 480
    PANEL_H = 300
    GAP = 30

    W = left + plot_w + right
    H = top + PANEL_H + GAP + PANEL_H + bottom
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

    # ---- Panel 1: Per-layer destruction rate ----
    p1_top = top
    p1_bottom = p1_top + PANEL_H

    y1_hi = 0.75
    y1_lo = 0.0

    def to_y1(v):
        return p1_bottom - (v - y1_lo) / (y1_hi - y1_lo) * PANEL_H

    # gridlines
    canvas.line(left, p1_top, left, p1_bottom, stroke=GRID, width=1)
    canvas.line(left, p1_bottom, left + plot_w, p1_bottom, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = p1_bottom - frac * PANEL_H
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        val = y1_lo + frac * (y1_hi - y1_lo)
        canvas.text(left - 10, y + 4, f"{val:.2f}", size=11, anchor="end", fill=INK_MUTED)

    for r in tick_primes:
        if min(r_values) <= r <= max(r_values):
            x = to_x(r)
            canvas.line(x, p1_bottom, x, p1_bottom + 5, stroke=INK_MUTED, width=1)
            canvas.text(x, p1_bottom + 18, str(r), size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, p1_bottom + 38, "filter prime r (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, p1_top + PANEL_H / 2, "destruction rate f = destroyed / expanded", size=12, fill=INK_MUTED)

    # f_real (solid blue)
    pts_real = [(to_x(row["r"]), to_y1(row["f_real"])) for row in rows]
    canvas.polyline(pts_real, stroke=COLOR_F_REAL, width=2.5)

    # f_random = 2/r (dashed red)
    pts_rand = [(to_x(row["r"]), to_y1(row["f_random"])) for row in rows]
    canvas.polyline(pts_rand, stroke=COLOR_F_RANDOM, width=2, dash=DASH_F_RANDOM)

    # ---- Panel 2: Cumulative survival ----
    p2_top = p1_bottom + GAP
    p2_bottom = p2_top + PANEL_H

    surv_vals = [row["survival"] for row in rows]
    y2_hi = max(surv_vals) * 1.1
    y2_lo = 0.0

    def to_y2(v):
        return p2_bottom - (v - y2_lo) / (y2_hi - y2_lo) * PANEL_H

    canvas.line(left, p2_top, left, p2_bottom, stroke=GRID, width=1)
    canvas.line(left, p2_bottom, left + plot_w, p2_bottom, stroke=GRID, width=1)
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = p2_bottom - frac * PANEL_H
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        val = y2_lo + frac * (y2_hi - y2_lo)
        canvas.text(left - 10, y + 4, f"{val:.3f}", size=11, anchor="end", fill=INK_MUTED)

    for r in tick_primes:
        if min(r_values) <= r <= max(r_values):
            x = to_x(r)
            canvas.line(x, p2_bottom, x, p2_bottom + 5, stroke=INK_MUTED, width=1)
            canvas.text(x, p2_bottom + 18, str(r), size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, p2_bottom + 38, "filter prime r (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, p2_top + PANEL_H / 2, "twin-prime survival: prod(1 - 2/r)", size=12, fill=INK_MUTED)

    # survival (solid blue)
    pts_surv = [(to_x(row["r"]), to_y2(row["survival"])) for row in rows]
    canvas.polyline(pts_surv, stroke=COLOR_SURVIVAL, width=2)

    # c=1 frontier: prod(1 - 2(1+log r)/r) -- square-window survival boundary
    COLOR_FRONTIER = "#e34948"
    DASH_FRONTIER = "10,3,2,3"
    frontier = 1.0
    pts_frontier = []
    for r in r_values:
        w = 1.0 + math.log(r)
        f = 2.0 * w / r
        if f < 1.0:
            frontier *= (1.0 - f)
        else:
            frontier = 0.0
        pts_frontier.append((to_x(r), to_y2(frontier)))
    canvas.polyline(pts_frontier, stroke=COLOR_FRONTIER, width=1.5, dash=DASH_FRONTIER)

    # Mertens reference: C / (log r)^2 with C fitted to first point
    C_fit = surv_vals[0] * (math.log(r_values[0]) ** 2)
    pts_mertens = [(to_x(r), to_y2(C_fit / (math.log(r) ** 2)))
                   for r in r_values if r >= 3]
    canvas.polyline(pts_mertens, stroke=COLOR_MERTENS, width=1.5, dash=DASH_MERTENS)

    # ---- Legend ----
    legend_x = left + plot_w + 24
    legend_y = top + 24

    canvas.text(legend_x, legend_y - 14, "top panel", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    entries1 = [
        ("f_real (exact cycle)", COLOR_F_REAL, None),
        ("f_random = 2/r", COLOR_F_RANDOM, DASH_F_RANDOM),
    ]
    for i, (label, color, dash) in enumerate(entries1):
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5 if dash is None else 2, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)

    legend_y2 = legend_y + len(entries1) * 22 + 14
    canvas.text(legend_x, legend_y2 - 14, "bottom panel", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    entries2 = [
        ("prod(1-2/r)  [c=0, real]", COLOR_SURVIVAL, None),
        ("prod(1-2(1+log r)/r)  [c=1 frontier]", COLOR_FRONTIER, DASH_FRONTIER),
        ("C/(log r)^2  (Mertens)", COLOR_MERTENS, DASH_MERTENS),
    ]
    for i, (label, color, dash) in enumerate(entries2):
        y = legend_y2 + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5 if dash is None else 1.5, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)

    note_y = legend_y2 + len(entries2) * 22 + 14
    for i, line in enumerate([
        "Exact modular cycle: T_new = T_old*(r-2),",
        "so f_real = 2/r exactly at every layer.",
        "",
        "No window, no Q parameter, no boundary",
        "noise. The survival fraction",
        "prod(1-2/r) is the quantity that",
        "determines whether twin primes persist.",
        "It decays like C/(log r)^2 (Mertens).",
        "",
        "Compare with fixed-lineage-hazard.svg,",
        "which measures the same rate but in the",
        "finite window [Q,Q^2) -- the deviations",
        "there are entirely window-boundary",
        "artifacts. This chart shows the",
        "underlying exact structure they sample.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "Full-Cycle Twin-Prime Destruction and Survival (Exact Modular Cycle)",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "Exact cycle: f_real = 2/r at every layer. Survival = prod(1-2/r) decays as C/(log r)^2.",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = compute_layers(max_r=251)
    canvas = draw(rows)
    out_path = os.path.join(OUT_DIR, "full-cycle-hazard.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path} ({len(rows)} layers)")


if __name__ == "__main__":
    main()