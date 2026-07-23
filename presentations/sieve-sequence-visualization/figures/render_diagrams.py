"""Generates the 10 figures proposed in ../06-article-diagram-ideas.md.

Run: python3 render_diagrams.py
Output lands in ./out/*.svg. Each function below is plain data (coordinates,
labels) plus calls into svg_kit -- edit a function directly to retune one
figure without touching the others.
"""

import math
import os

from svg_kit import Canvas, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")


def diagram_01_copy_or_merge_strip() -> Canvas:
    c = Canvas(640, 300)
    xs = {"i": 90, "i1": 320, "i2": 550}

    c.text(320, 30, "Before filtering", size=16, weight="bold")
    y = 90
    c.line(xs["i"], y, xs["i1"], y)
    c.line(xs["i1"], y, xs["i2"], y)
    c.circle(xs["i"], y, fill="#222")
    c.circle(xs["i2"], y, fill="#222")
    c.circle(xs["i1"], y, r=8, fill="white", stroke="#c0392b", width=2.5)
    c.cross(xs["i1"], y, size=9)
    c.text_sub(xs["i"], y + 26, "e", "i")
    c.text_sub(xs["i1"], y + 26, "e", "i+1")
    c.text_sub(xs["i2"], y + 26, "e", "i+2")
    c.text_sub((xs["i"] + xs["i1"]) // 2, y - 14, "g", "i")
    c.text_sub((xs["i1"] + xs["i2"]) // 2, y - 14, "g", "i+1")

    y2 = 220
    c.text(320, y2 - 60, "After filtering", size=16, weight="bold")
    c.line(xs["i"], y2, xs["i2"], y2)
    c.circle(xs["i"], y2, fill="#222")
    c.circle(xs["i2"], y2, fill="#222")
    c.text_sub(xs["i"], y2 + 26, "e", "i")
    c.text_sub(xs["i2"], y2 + 26, "e", "i+2")
    c.text((xs["i"] + xs["i2"]) // 2, y2 - 14, "g_i + g_{i+1}", size=15)
    return c


def diagram_02_repeated_period_before_filtering() -> Canvas:
    c = Canvas(820, 280)
    c.text(410, 30, "Old period", size=16, weight="bold")
    c.rect(340, 46, 140, 46, fill="#eef2ff")
    c.text_sub(410, 74, "S", "k")

    c.text(410, 128, "expanded by new head h", size=14, style="italic")

    labels = ["copy 0", "copy 1", "...", "copy h-1"]
    box_w, gap, y = 160, 14, 150
    total = len(labels) * box_w + (len(labels) - 1) * gap
    x = (c.width - total) / 2
    for label in labels:
        c.rect(x, y, box_w, 46, fill="#f7f7f7")
        c.text(x + box_w / 2, y + 28, label, size=13)
        if label != "...":
            tick_x = x + box_w * 0.4
            c.line(tick_x, y - 8, tick_x, y + 54, stroke="#c0392b", width=2, dash="4,3")
        x += box_w + gap

    c.text(410, 234, "dashed ticks: the new filter removes one fixed", size=13, fill="#555")
    c.text(410, 252, "congruence class across every copy", size=13, fill="#555")
    return c


def diagram_03_candidate_composite_certified() -> Canvas:
    c = Canvas(700, 320)
    xs = [90, 170, 250, 330, 410, 490, 570, 650]

    c.text(370, 30, "stage k", size=16, weight="bold")
    y = 110
    c.rect(70, y - 34, 300, 68, fill="#eafaf1", stroke="#27ae60", width=1.5, rx=6)
    c.text(220, y - 46, "safe zone", size=13, fill="#1e8449")
    for i, x in enumerate(xs):
        certified = x <= 330
        c.circle(x, y, r=8, fill="#27ae60" if certified else "white",
                  stroke="#27ae60" if certified else "#333")

    c.text(370, 210, "later stage", size=16, weight="bold")
    y2 = 260
    c.rect(70, y2 - 34, 300, 68, fill="#eafaf1", stroke="#27ae60", width=1.5, rx=6)
    for i, x in enumerate(xs):
        certified = x <= 330
        rejected = x == 490
        c.circle(x, y2, r=8, fill="#27ae60" if certified else "white",
                  stroke="#27ae60" if certified else "#333")
        if rejected:
            c.cross(x, y2, size=9)
    c.text(490, y2 + 34, "rejected by p_j", size=12, fill="#c0392b")
    return c


def diagram_04_safe_zone_boundary() -> Canvas:
    c = Canvas(700, 300)
    x_p, x_p2 = 100, 560
    y = 70
    c.line(x_p, y, x_p2, y, width=3)
    for x, label in ((x_p, "p"), (x_p2, "p^2")):
        c.line(x, y - 10, x, y + 10, width=2)
        c.text(x, y - 20, label, size=15, weight="bold")
    c.text((x_p + x_p2) / 2, y + 30, "certified window", size=14)

    y2 = 160
    x1, x2 = 200, 320
    c.line(x1, y2, x2, y2, width=2)
    c.circle(x1, y2, fill="#27ae60", stroke="#27ae60")
    c.circle(x2, y2, fill="#27ae60", stroke="#27ae60")
    c.text((x1 + x2) / 2, y2 - 14, "2", size=13)
    c.text_sub(x1, y2 + 26, "x", "")
    c.text(x2, y2 + 26, "x+2", size=14)
    c.text((x1 + x2) / 2, y2 + 50, "certifies a twin-prime pair", size=13, fill="#1e8449")

    y3 = 250
    x3, x4 = 470, 590
    c.line(x3, y3, x4, y3, width=2)
    c.circle(x3, y3, fill="white", stroke="#e67e22")
    c.circle(x4, y3, fill="white", stroke="#e67e22")
    c.text((x3 + x4) / 2, y3 - 14, "2", size=13)
    c.text(x3, y3 + 26, "y", size=14)
    c.text(x4, y3 + 26, "y+2", size=14)
    c.text((x3 + x4) / 2, y3 + 50, "survives filters, not yet certified", size=13, fill="#af601a")
    return c


def diagram_05_full_period_vs_local_window() -> Canvas:
    c = Canvas(760, 240)
    y = 80
    c.line(60, y, 700, y, width=3)
    c.text(380, y - 46, "one huge period", size=15, weight="bold")
    tick_xs = [110, 170, 230, 310, 360, 430, 470, 540, 610, 660]
    for x in tick_xs:
        c.line(x, y - 8, x, y + 8, stroke="#7f8c8d", width=2)
    c.text(380, y + 30, "many 2-gaps across the full cycle", size=13, fill="#555")

    y2 = 190
    c.rect(60, y2 - 12, 180, 24, fill="#eafaf1", stroke="#27ae60", width=2)
    c.text(150, y2 - 24, "front safe window (p^2)", size=13, fill="#1e8449")
    c.text(150, y2 + 40, "does a 2-gap land here?", size=13, fill="#555", style="italic")
    return c


def diagram_06_two_gap_descendant_fan() -> Canvas:
    c = Canvas(700, 360)
    root = (350, 50)
    c.circle(*root, r=8, fill="#222")
    c.text(root[0], root[1] - 20, "one old 2-gap", size=14, weight="bold")

    labels = ["copy 0", "copy 1", "copy 2", "...", "copy r", "..."]
    states = ["survives", "removed (left endpoint div. by q)", "survives", "", "removed (right endpoint div. by q)", ""]
    n = len(labels)
    xs_children = [140 + i * (420 / (n - 1)) for i in range(n)]
    y_child = 190
    for x, label, state in zip(xs_children, labels, states):
        c.line(root[0], root[1] + 8, x, y_child - 10, stroke="#999", width=1.5)
        ok = state.startswith("survives")
        removed = state.startswith("removed")
        color = "#27ae60" if ok else ("#c0392b" if removed else "#999")
        c.circle(x, y_child, r=7, fill=color if ok else "white", stroke=color)
        if removed:
            c.cross(x, y_child, size=7, stroke=color)
        c.text(x, y_child + 26, label, size=12)
        if state:
            words = state.split(" ", 1)
            c.text(x, y_child + 44, words[0], size=11, fill=color)
            if len(words) > 1:
                c.text(x, y_child + 60, words[1], size=10, fill="#666")

    c.text(350, 330, "odd new prime q: 2 forbidden copy classes, q - 2 descendants survive", size=13, fill="#555")
    return c


def diagram_07_two_focused_compression() -> Canvas:
    c = Canvas(760, 260)
    full_gaps = [6, 4, 2, 4, 2, 4, 6, 2]
    compressed = [10, 2, 4, 2, 10, 2]

    c.text(380, 30, "full gaps", size=16, weight="bold")
    box_w, y1 = 80, 60
    total = len(full_gaps) * box_w
    x0 = (c.width - total) / 2
    full_positions = []
    for i, g in enumerate(full_gaps):
        x = x0 + i * box_w
        is_two = g == 2
        c.rect(x, y1, box_w - 6, 44, fill="#eafaf1" if is_two else "#f7f7f7",
               stroke="#27ae60" if is_two else "#999")
        c.text(x + (box_w - 6) / 2, y1 + 28, str(g), size=15)
        full_positions.append(x + (box_w - 6) / 2)

    c.text(380, 170, "2-focused compression", size=16, weight="bold")
    box_w2, y2 = 106, 200
    total2 = len(compressed) * box_w2
    x0b = (c.width - total2) / 2
    for i, g in enumerate(compressed):
        x = x0b + i * box_w2
        is_two = g == 2
        c.rect(x, y2, box_w2 - 6, 44, fill="#eafaf1" if is_two else "#f7f7f7",
               stroke="#27ae60" if is_two else "#999")
        c.text(x + (box_w2 - 6) / 2, y2 + 28, str(g), size=15)
    return c


def diagram_08_stage_summary_ladder() -> Canvas:
    rows = [
        ("S_1", 3, 1, 1),
        ("S_2", 5, 2, 1),
        ("S_3", 7, 8, 3),
        ("S_4", 11, 48, 15),
    ]
    c = Canvas(880, 320)
    c.text(440, 30, "stage summary", size=16, weight="bold")

    table_rows = [["stage", "head", "period", "2-gaps"]] + [
        [s, str(h), str(p), str(g)] for s, h, p, g in rows
    ]
    c.table(40, 50, [100, 80, 100, 80], table_rows, row_height=30)

    chart_x0, chart_y0, chart_w = 540, 60, 220
    max_log = math.log10(max(p for _, _, p, _ in rows))
    for i, (s, h, p, g) in enumerate(rows):
        y = chart_y0 + i * 34
        bar_w = chart_w * (math.log10(p) / max_log) if p > 1 else 4
        c.rect(chart_x0, y, bar_w, 14, fill="#5b8def")
        c.text(chart_x0 - 10, y + 12, s, size=12, anchor="end")
        c.text(chart_x0 + bar_w + 8, y + 12, f"period={p}", size=11, anchor="start", fill="#555")
    c.text(chart_x0 + chart_w / 2, chart_y0 - 20, "period (log scale)", size=12, fill="#555")

    c.text(380, 240, "period grows explosively; 2-gaps stay visible in absolute count", size=13, fill="#555")
    c.text(380, 260, "(full-period statistic -- not a claim about local safe-zone occupancy)", size=12, fill="#888")
    return c


def diagram_09_rotation_is_change_of_view() -> Canvas:
    c = Canvas(760, 240)
    before = [4, 2, 4, 6, 2]
    after = [2, 4, 6, 2, 4]
    box_w = 90

    def row(gaps, y, title, marker_label):
        total = len(gaps) * box_w
        x0 = (c.width - total) / 2
        c.text(c.width / 2, y - 30, title, size=15, weight="bold")
        for i, g in enumerate(gaps):
            x = x0 + i * box_w
            c.rect(x, y, box_w - 6, 40, fill="#f7f7f7")
            c.text(x + (box_w - 6) / 2, y + 26, str(g), size=15)
        c.text(x0 + (box_w - 6) / 2, y + 62, "^", size=16, anchor="middle")
        c.text(x0 + (box_w - 6) / 2, y + 80, marker_label, size=11, fill="#555")
        return x0

    row(before, 60, "before rotation", "arbitrary start")
    row(after, 160, "after rotation", "next head start")
    return c


def diagram_10_article_figure_map() -> Canvas:
    rows = [
        ["Article Area", "Best Diagrams"],
        ["Sieve sequence construction", "Repeated Period, Rotation View"],
        ["Copy-or-merge theorem", "Copy-Or-Merge Strip"],
        ["Acceptance vs primality", "Candidate/Composite/Certified"],
        ["Gap dynamics, 2-gap survival", "Descendant Fan, Full-Period vs Local"],
        ["Safe-zone discussion", "Safe-Zone Boundary"],
        ["Empirical Spark section", "Stage Ladder, 2-Focused Compression"],
    ]
    c = Canvas(820, 60 + 32 * len(rows))
    c.text(410, 30, "article figure map", size=16, weight="bold")
    c.table(30, 50, [280, 510], rows, row_height=32)
    return c


DIAGRAMS = {
    "01-copy-or-merge-strip": diagram_01_copy_or_merge_strip,
    "02-repeated-period-before-filtering": diagram_02_repeated_period_before_filtering,
    "03-candidate-composite-certified": diagram_03_candidate_composite_certified,
    "04-safe-zone-boundary": diagram_04_safe_zone_boundary,
    "05-full-period-vs-local-window": diagram_05_full_period_vs_local_window,
    "06-two-gap-descendant-fan": diagram_06_two_gap_descendant_fan,
    "07-two-focused-compression": diagram_07_two_focused_compression,
    "08-stage-summary-ladder": diagram_08_stage_summary_ladder,
    "09-rotation-is-change-of-view": diagram_09_rotation_is_change_of_view,
    "10-article-figure-map": diagram_10_article_figure_map,
}


def main() -> None:
    os.makedirs(OUT_DIR, exist_ok=True)
    for name, build in DIAGRAMS.items():
        canvas = build()
        path = os.path.join(OUT_DIR, f"{name}.svg")
        save(canvas, path)
        print(f"wrote {path}")


if __name__ == "__main__":
    main()
