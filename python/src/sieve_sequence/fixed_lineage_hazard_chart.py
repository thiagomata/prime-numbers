"""Fixed-window 2-gap cohort cumulative hazard chart.

Two panels stacked vertically:
  1. Cumulative excess:  D_real - D_random  vs filter r (log x-axis)
     Reference curves at 0, log(r), and 2*log(r).
  2. Effective coefficient: (D_real - D_random) / (2 log r) vs filter r (log x-axis)
     Horizontal references at 0, 1/2, and 1.

Reads one CSV per Q value from data/candidates/fixed-lineage-hazard-Q{N}.csv.
Supports multiple Q curves in one figure.

Run from python/: .venv/bin/python -m sieve_sequence.fixed_lineage_hazard_chart
Output: ../charts/fixed-lineage-hazard.svg
"""

import csv
import math
import os

from .svg_kit import Canvas, escape, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "charts")
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

PANEL_HEIGHT = 300
PANEL_GAP = 75
PLOT_LEFT = 95
PLOT_RIGHT = 310
PLOT_TOP = 70
PLOT_BOTTOM = 90
PLOT_WIDTH = 560


def _sparse_log_ticks(values, max_ticks=7):
    """Select observed values nearest evenly spaced positions on a log axis."""
    ordered = sorted(set(values))
    if len(ordered) <= max_ticks:
        return ordered

    log_lo = math.log(ordered[0])
    log_hi = math.log(ordered[-1])
    targets = [
        log_lo + (log_hi - log_lo) * i / (max_ticks - 1)
        for i in range(max_ticks)
    ]
    selected = {
        min(ordered, key=lambda value: abs(math.log(value) - target))
        for target in targets
    }
    return sorted(selected)


def _finite_series(rows, key):
    """Return positive filter primes paired with finite values for one column."""
    series = []
    for row in rows:
        r = int(row["r"])
        value = float(row[key])
        if r > 0 and math.isfinite(value):
            series.append((r, value))
    return series


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
    left, right, top, bottom = PLOT_LEFT, PLOT_RIGHT, PLOT_TOP, PLOT_BOTTOM
    plot_w = PLOT_WIDTH

    W = left + plot_w + right
    H = top + PANEL_HEIGHT + PANEL_GAP + PANEL_HEIGHT + bottom
    canvas = Canvas(W, H)

    canvas.comment("Script: python/src/sieve_sequence/fixed_lineage_hazard_chart.py")
    canvas.comment(f"Q values: {Q_values}")
    for Q in Q_values:
        canvas.comment(f"Input: data/candidates/fixed-lineage-hazard-Q{Q}.csv")
    canvas.comment("Formula: excess_hazard = D_real - D_random")
    canvas.comment("Formula: c_eff = excess_hazard / (2 log r)")

    all_rows = []
    for Q in Q_values:
        if Q in all_data:
            all_rows.extend(all_data[Q])

    r_values = sorted({
        int(row["r"])
        for row in all_rows
        if int(row["r"]) > 0
    })
    if not r_values:
        raise ValueError("fixed-lineage hazard chart requires at least one data row")
    x_lo = math.log(min(r_values))
    x_hi = math.log(max(r_values))

    def to_x(r):
        if x_hi == x_lo:
            return left + plot_w / 2
        return left + (math.log(r) - x_lo) / (x_hi - x_lo) * plot_w

    # ---- Panel 1: Cumulative Excess ----
    panel1_top = top
    panel1_bottom = panel1_top + PANEL_HEIGHT

    excess_vals = []
    for Q in Q_values:
        if Q not in all_data:
            continue
        excess_vals.extend(value for _, value in _finite_series(
            all_data[Q], "excess_hazard"
        ))
    if not excess_vals:
        excess_vals = [0.0, 1.0]
    data_lo = min(0.0, min(excess_vals))
    data_hi = max(0.0, max(excess_vals))
    data_span = data_hi - data_lo
    padding = data_span * 0.12 if data_span else 0.05
    y1_lo = data_lo - padding
    y1_hi = data_hi + padding
    span1 = y1_hi - y1_lo

    def to_y1(v):
        return panel1_bottom - (v - y1_lo) / span1 * PANEL_HEIGHT

    canvas.text(
        left,
        panel1_top - 16,
        "Observed boundary effect (zoomed)",
        size=12,
        anchor="start",
        weight="bold",
        fill=INK_PRIMARY,
    )

    # axis frame
    canvas.line(left, panel1_top, left, panel1_bottom, stroke=GRID, width=1)
    canvas.line(left, panel1_bottom, left + plot_w, panel1_bottom, stroke=GRID, width=1)

    # horizontal gridlines
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = panel1_bottom - frac * PANEL_HEIGHT
        canvas.line(left, y, left + plot_w, y, stroke=GRID, width=1)
        val = y1_lo + frac * span1
        canvas.text(left - 10, y + 4, f"{val:.2f}", size=11, anchor="end", fill=INK_MUTED)

    # Sparse observed primes keep the logarithmic axis readable at large Q.
    tick_primes = _sparse_log_ticks(r_values)
    for r in tick_primes:
        if min(r_values) <= r <= max(r_values):
            x = to_x(r)
            canvas.line(x, panel1_bottom, x, panel1_bottom + 5, stroke=INK_MUTED, width=1)
            canvas.text(x, panel1_bottom + 18, str(r), size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, panel1_bottom + 38, "filter prime r (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(canvas, 24, panel1_top + PANEL_HEIGHT / 2, "cumulative excess: D_real - D_random", size=12, fill=INK_MUTED)

    # The upper panel is an empirical zoom. The c=1/2 and c=1 comparisons
    # belong on the normalized lower panel, where their scale is meaningful.
    canvas.polyline([(x, to_y1(0.0)) for x in [left, left + plot_w]],
                    stroke=INK_MUTED, width=1, dash="4,4")

    # data curves
    for Q in Q_values:
        if Q not in all_data:
            continue
        rows = all_data[Q]
        color = Q_COLORS.get(Q, COLOR_EMPIRICAL)
        pts = [
            (to_x(r), to_y1(value))
            for r, value in _finite_series(rows, "excess_hazard")
        ]
        if pts:
            canvas.polyline(pts, stroke=color, width=2)

    # ---- Panel 2: Effective Coefficient ----
    panel2_top = panel1_bottom + PANEL_GAP
    panel2_bottom = panel2_top + PANEL_HEIGHT

    c_vals = []
    for Q in Q_values:
        if Q not in all_data:
            continue
        c_vals.extend(value for _, value in _finite_series(all_data[Q], "c_eff"))
    if not c_vals:
        c_vals = [0.0, 1.0]
    y2_lo = min(-0.05, min(c_vals) * 1.15)
    y2_hi = max(1.05, max(c_vals) * 1.15)
    span2 = (y2_hi - y2_lo) or 1.0

    def to_y2(v):
        return panel2_bottom - (v - y2_lo) / span2 * PANEL_HEIGHT

    canvas.text(
        left,
        panel2_top - 16,
        "Distance from comparison scales (normalized)",
        size=12,
        anchor="start",
        weight="bold",
        fill=INK_PRIMARY,
    )

    canvas.line(left, panel2_top, left, panel2_bottom, stroke=GRID, width=1)
    canvas.line(left, panel2_bottom, left + plot_w, panel2_bottom, stroke=GRID, width=1)

    canvas.line(left, to_y2(y2_lo), left + plot_w, to_y2(y2_lo), stroke=GRID, width=1)
    canvas.text(left - 10, to_y2(y2_lo) + 4, f"{y2_lo:.2f}", size=11, anchor="end", fill=INK_MUTED)

    for r in tick_primes:
        if min(r_values) <= r <= max(r_values):
            x = to_x(r)
            canvas.line(x, panel2_bottom, x, panel2_bottom + 5, stroke=INK_MUTED, width=1)
            canvas.text(x, panel2_bottom + 18, str(r), size=10, anchor="middle", fill=INK_MUTED)

    canvas.text(left + plot_w / 2, panel2_bottom + 38, "filter prime r (log scale)", size=12, anchor="middle", fill=INK_MUTED)
    vertical_text(
        canvas,
        17,
        panel2_top + PANEL_HEIGHT / 2,
        "effective coefficient c_eff",
        size=11,
        fill=INK_MUTED,
    )
    vertical_text(
        canvas,
        35,
        panel2_top + PANEL_HEIGHT / 2,
        "excess / (2 log r)",
        size=11,
        fill=INK_MUTED,
    )

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
        pts = [
            (to_x(r), to_y2(value))
            for r, value in _finite_series(rows, "c_eff")
        ]
        if pts:
            canvas.polyline(pts, stroke=color, width=2)

    # ---- Legend (right margin) ----
    legend_x = left + plot_w + 24
    legend_y = top + 24
    entries = [(f"Q={Q}", Q_COLORS.get(Q, COLOR_EMPIRICAL)) for Q in Q_values if Q in all_data]
    canvas.text(legend_x, legend_y - 14, "cohort endpoint", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color) in enumerate(entries):
        y = legend_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=2.5)
        canvas.text(legend_x + 30, y + 4, label, size=11, anchor="start", fill=INK_PRIMARY)

    ref_y = legend_y + len(entries) * 22 + 14
    ref_entries = [
        ("zero", INK_MUTED, "4,4"),
        ("head scale (c=1/2)", INK_MUTED, "7,4"),
        ("square-window scale (c=1)", INK_MUTED, "10,3,2,3"),
    ]
    canvas.text(legend_x, ref_y - 14, "reference scales", size=11, anchor="start", weight="bold", fill=INK_MUTED)
    for i, (label, color, dash) in enumerate(ref_entries):
        y = ref_y + i * 22
        canvas.line(legend_x, y, legend_x + 22, y, stroke=color, width=1.5, dash=dash)
        canvas.text(legend_x + 30, y + 4, label, size=10, anchor="start", fill=INK_MUTED)

    note_y = ref_y + len(ref_entries) * 22 + 14
    for i, line in enumerate([
        "Top: measured real-minus-random",
        "cumulative log-hazard excess.",
        "Bottom: the same excess normalized",
        "as c_eff = excess / (2 log r).",
        "The c=1/2 and c=1 lines are",
        "comparison scales, not fitted claims.",
        "Negative values mean less destruction",
        "than the independent-random benchmark.",
    ]):
        canvas.text(legend_x, note_y + i * 15, line, size=10, anchor="start", fill=INK_MUTED)

    canvas.text(
        W / 2, 22,
        "Fixed-Window 2-Gap Cohort: Real Excess vs Random Benchmark",
        size=15, anchor="middle", weight="bold", fill=INK_PRIMARY,
    )
    canvas.text(
        W / 2, H - 12,
        "Cumulative log-hazard excess over the independent-random benchmark 2/r at each incoming filter r",
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
