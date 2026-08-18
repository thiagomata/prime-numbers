"""Fixed-window 2-gap cohort cumulative hazard chart.

Two panels stacked vertically:
  1. Cumulative excess:  D_real - D_random  vs filter r (log x-axis)
     Reference curves at 0, log(r), and 2*log(r).
  2. Effective coefficient: (D_real - D_random) / (2 log r) vs filter r (log x-axis)
     Horizontal references at 0, 1/2, and 1.

Reads one CSV per Q value from ../../../data/candidates/fixed-lineage-hazard-Q{N}.csv.
Supports multiple Q curves in one figure.

Run: python3 fixed_lineage_hazard_chart.py
Output: ./out/fixed-lineage-hazard.svg
"""

import csv
import datetime
import math
import os
import subprocess
import sys

from svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")
DATA_DIR = os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "data", "candidates"
)

COLOR_EMPIRICAL = "#2a78d6"
COLOR_RANDOM = "#e34948"
COLOR_FRONTIER = "#111111"
COLOR_Q17 = "#e67e22"
COLOR_Q101 = "#2a78d6"
COLOR_Q251 = "#27ae60"
COLOR_Q503 = "#8e44ad"

INK_PRIMARY = "#111111"
INK_MUTED = "#555555"
GRID = "#dddddd"

Q_COLORS = {17: COLOR_Q17, 101: COLOR_Q101, 251: COLOR_Q251, 503: COLOR_Q503}


def vertical_text(canvas, x, y, label, size=12, fill=INK_MUTED):
    canvas.elements.append(
        f'<text x="{x}" y="{y}" font-family="{canvas.font_family}" font-size="{size}" '
        f'font-weight="normal" font-style="normal" fill="{fill}" '
        f'text-anchor="middle" transform="rotate(-90 {x} {y})">{escape(label)}</text>'
    )


def data_path(Q):
    return os.path.join(DATA_DIR, f"fixed-lineage-hazard-Q{Q}.csv")


def load_rows(Q_values):
    result = {}
    for Q in Q_values:
        path = data_path(Q)
        if not os.path.exists(path):
            print(f"SKIP Q={Q}: {path} not found")
            continue
        with open(path, newline="") as f:
            result[Q] = list(csv.DictReader(f))
    return result


def draw(all_data, Q_values):
    PANEL_H = 300
    GAP = 30
    left, right, top, bottom = 80, 220, 50, 60
    plot_w = 480

    W = left + plot_w + right
    H = top + PANEL_H + GAP + PANEL_H + bottom
    canvas = Canvas(W, H)

    canvas.comment(f"Generated: {datetime.datetime.now().isoformat()}")
    canvas.comment(f"Script: {os.path.basename(__file__)}")
    canvas.comment(f"Python: {sys.version}")
    canvas.comment(f"Q values: {Q_values}")
    try:
        commit = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], text=True).strip()
        canvas.comment(f"Git commit: {commit}")
    except Exception:
        canvas.comment("Git commit: unknown")

    all_rows = []
    for Q in Q_values:
        if Q in all_data:
            all_rows.extend(all_data[Q])

    r_values = sorted(set(int(row["r"]) for row in all_rows))
    x_lo = math.log(min(r_values))
    x_hi = math.log(max(r_values))

    def to_x(r):
        return left + (math.log(r) - x_lo) / (x_hi - x_lo) * plot_w

    # ---- Panel 1: Cumulative Excess ----
    panel1_top = top
    panel1_bottom = panel1_top + PANEL_H

    excess_vals = []
    for Q in Q_values:
        if Q not in all_data:
            continue
        for row in all_data[Q]:
            v = float(row["excess_hazard"])
            if v == v:
                excess_vals.append(v)
    if not excess_vals:
        excess_vals = [0.0, 1.0]
    y1_lo = min(excess_vals) * 1.15
    y1_hi = max(excess_vals) * 1.15
    span1 = (y1_hi - y1_lo) or 1.0

    def to_y1(v):
        return panel1_bottom - (v - y1_lo) / span1 * PANEL_H

    # reference scale: log(r) values at extremes for slope calibration
    log_r_lo = math.log(min(r_values))
    log_r_hi = math.log(max(r_values))

    # axis frame
    canvas.line(left, panel1_top, left, panel1_bottom, stroke=GRID, width=1)
    canvas.line(left, panel1_bottom, left + plot_w, panel1_bottom, stroke=GRID, width=1)

    # horizontal gridlines
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = panel1_bottom - frac * PANEL_H
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        val = y1_lo + frac * span1
        canvas.text(left - 10, y + 4, f"{val:.2f}", size=11, anchor="end", fill=INK_MUTED)

    # vertical gridlines at tick primes
    tick_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                   53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
                   109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
                   173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
                   233, 239, 241, 251]
    for r in tick_primes:
        if min(r_values) <= r <= max(r_values):
            x = to_x(r)
            canvas.line(x, panel1_bottom, x, panel1_bottom + 5, stroke=INK_MUTED, width=1)
            canvas.text(x, panel1_bottom + 18, str(r), size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, panel1_bottom + 38, "filter prime r (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, panel1_top + PANEL_H / 2, "cumulative excess: D_real - D_random", size=12, fill=INK_MUTED)

    # reference curves on excess panel
    ref_xs = [to_x(r) for r in r_values]
    # 0 line
    canvas.polyline([(x, to_y1(0.0)) for x in [left, left + plot_w]],
                    stroke=INK_MUTED, width=1, dash="4,4")
    # log r curve (c=1/2 head scale: excess = log r)
    ref_log_r = [(to_x(r), to_y1(math.log(r))) for r in r_values]
    canvas.polyline(ref_log_r, stroke=INK_MUTED, width=1.5, dash="7,4")
    # 2 log r curve (c=1 square-window scale: excess = 2 log r)
    ref_2log_r = [(to_x(r), to_y1(2 * math.log(r))) for r in r_values]
    canvas.polyline(ref_2log_r, stroke=INK_MUTED, width=1.5, dash="10,3,2,3")

    # data curves
    for Q in Q_values:
        if Q not in all_data:
            continue
        rows = all_data[Q]
        color = Q_COLORS.get(Q, COLOR_EMPIRICAL)
        pts = [(to_x(int(row["r"])), to_y1(float(row["excess_hazard"]))) for row in rows
               if float(row["excess_hazard"]) == float(row["excess_hazard"])]
        if pts:
            canvas.polyline(pts, stroke=color, width=2)

    # ---- Panel 2: Effective Coefficient ----
    panel2_top = panel1_bottom + GAP
    panel2_bottom = panel2_top + PANEL_H

    c_vals = []
    for Q in Q_values:
        if Q not in all_data:
            continue
        for row in all_data[Q]:
            v = float(row["c_eff"])
            if v == v and v != float("inf"):
                c_vals.append(v)
    if not c_vals:
        c_vals = [0.0, 1.0]
    y2_lo = min(-0.1, min(c_vals) * 1.15)
    y2_hi = max(1.1, max(c_vals) * 1.15)
    span2 = (y2_hi - y2_lo) or 1.0

    def to_y2(v):
        return panel2_bottom - (v - y2_lo) / span2 * PANEL_H

    canvas.line(left, panel2_top, left, panel2_bottom, stroke=GRID, width=1)
    canvas.line(left, panel2_bottom, left + plot_w, panel2_bottom, stroke=GRID, width=1)

    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = panel2_bottom - frac * PANEL_H
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        val = y2_lo + frac * span2
        canvas.text(left - 10, y + 4, f"{val:.3f}", size=11, anchor="end", fill=INK_MUTED)

    for r in tick_primes:
        if min(r_values) <= r <= max(r_values):
            x = to_x(r)
            canvas.line(x, panel2_bottom, x, panel2_bottom + 5, stroke=INK_MUTED, width=1)
            canvas.text(x, panel2_bottom + 18, str(r), size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, panel2_bottom + 38, "filter prime r (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 18, panel2_top + PANEL_H / 2, "effective coefficient: c_eff = excess / (2 log r)", size=12, fill=INK_MUTED)

    # horizontal reference lines at 0, 1/2, 1
    for ref_val, label, dash in [(0.0, "0", "4,4"), (0.5, "1/2", "7,4"), (1.0, "1", "10,3,2,3")]:
        y = to_y2(ref_val)
        canvas.line(left, y, left + plot_w, y, stroke=INK_MUTED, width=1.5, dash=dash)
        canvas.text(left - 10, y + 4, label, size=10, anchor="end", fill=INK_MUTED)

    # data curves
    for Q in Q_values:
        if Q not in all_data:
            continue
        rows = all_data[Q]
        color = Q_COLORS.get(Q, COLOR_EMPIRICAL)
        pts = [(to_x(int(row["r"])), to_y2(float(row["c_eff"]))) for row in rows
               if float(row["c_eff"]) == float(row["c_eff"]) and float(row["c_eff"]) != float("inf")]
        if pts:
            canvas.polyline(pts, stroke=color, width=2)

    # ---- Legend (right margin) ----
    legend_x = left + plot_w + 24
    legend_y = top + 24
    entries = [(f"Q={Q}", Q_COLORS.get(Q, COLOR_EMPIRICAL)) for Q in Q_values if Q in all_data]
    canvas.text(legend_x, legend_y - 14, "fixed-window cohort", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color) in enumerate(entries):
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)

    ref_y = legend_y + len(entries) * 22 + 14
    ref_entries = [
        ("excess = 0", INK_MUTED, "4,4"),
        ("excess = log r (c=1/2 head scale)", INK_MUTED, "7,4"),
        ("excess = 2 log r (c=1 square-window scale)", INK_MUTED, "10,3,2,3"),
    ]
    canvas.text(legend_x, ref_y - 14, "reference scales", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color, dash) in enumerate(ref_entries):
        y = ref_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=1.5, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=10, anchor="start", fill=INK_MUTED)

    note_y = ref_y + len(ref_entries) * 22 + 14
    for i, line in enumerate([
        "Fixed-window 2-gap cohort cumulative",
        "excess hazard. Top: D_real - D_random",
        "vs incoming filter r. Bottom: effective",
        "coefficient c_eff = exc/(2 log r).",
        "Reference scales at c=1/2 (head",
        "recurrence) and c=1 (square-window",
        "occupancy) are comparison scales only --",
        "they are NOT fitted claims about the",
        "real sieve. Negative excess means the",
        "real destruction rate is BELOW the",
        "independent-random benchmark.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "Fixed-Cohort Cumulative Hazard: Real Excess vs Random Benchmark",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "Fixed-window 2-gap cohort: cumulative log-hazard excess over independent-random benchmark (r=2/r per filter)",
        size=10, anchor="middle", fill=INK_MUTED,
    )
    return canvas


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    Q_values = [17, 101]
    # add larger Q values if their CSVs exist
    for q in [251, 503, 1009]:
        if os.path.exists(data_path(q)):
            Q_values.append(q)
    all_data = load_rows(Q_values)
    canvas = draw(all_data, [q for q in Q_values if q in all_data])
    out_path = os.path.join(OUT_DIR, "fixed-lineage-hazard.svg")
    save(canvas, out_path)
    print(f"Wrote {out_path} (Q values: {[q for q in Q_values if q in all_data]})")


if __name__ == "__main__":
    main()
