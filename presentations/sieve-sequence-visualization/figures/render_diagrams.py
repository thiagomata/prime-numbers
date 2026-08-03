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
    """Before/after strip showing one survivor removed by filtering, and its
    two neighboring gaps merging into one (the copy-or-merge theorem)."""
    canvas = Canvas(640, 300)
    xs = {"i": 90, "i1": 320, "i2": 550}

    canvas.text(320, 30, "Before filtering", size=16, weight="bold")
    y = 90
    canvas.line(xs["i"], y, xs["i1"], y)
    canvas.line(xs["i1"], y, xs["i2"], y)
    canvas.circle(xs["i"], y, fill="#222")
    canvas.circle(xs["i2"], y, fill="#222")
    canvas.circle(xs["i1"], y, r=8, fill="white", stroke="#c0392b", width=2.5)
    canvas.cross(xs["i1"], y, size=9)
    canvas.text_sub(xs["i"], y + 26, "e", "i")
    canvas.text_sub(xs["i1"], y + 26, "e", "i+1")
    canvas.text_sub(xs["i2"], y + 26, "e", "i+2")
    canvas.text_sub((xs["i"] + xs["i1"]) // 2, y - 14, "g", "i")
    canvas.text_sub((xs["i1"] + xs["i2"]) // 2, y - 14, "g", "i+1")

    y2 = 220
    canvas.text(320, y2 - 60, "After filtering", size=16, weight="bold")
    canvas.line(xs["i"], y2, xs["i2"], y2)
    canvas.circle(xs["i"], y2, fill="#222")
    canvas.circle(xs["i2"], y2, fill="#222")
    canvas.text_sub(xs["i"], y2 + 26, "e", "i")
    canvas.text_sub(xs["i2"], y2 + 26, "e", "i+2")
    canvas.text((xs["i"] + xs["i2"]) // 2, y2 - 14, "g_i + g_{i+1}", size=15)
    return canvas


def diagram_02_repeated_period_before_filtering() -> Canvas:
    """The old stage's period tiled h times (h = new head) before the new
    filter is applied, with dashed ticks marking the one congruence class
    the new filter removes from every copy."""
    canvas = Canvas(820, 280)
    canvas.text(410, 30, "Old period", size=16, weight="bold")
    canvas.rect(340, 46, 140, 46, fill="#eef2ff")
    canvas.text_sub(410, 74, "S", "k")

    canvas.text(410, 128, "expanded by new head h", size=14, style="italic")

    labels = ["copy 0", "copy 1", "...", "copy h-1"]
    box_w, gap, y = 160, 14, 150
    total = len(labels) * box_w + (len(labels) - 1) * gap
    x = (canvas.width - total) / 2
    for label in labels:
        canvas.rect(x, y, box_w, 46, fill="#f7f7f7")
        canvas.text(x + box_w / 2, y + 28, label, size=13)
        if label != "...":
            tick_x = x + box_w * 0.4
            canvas.line(tick_x, y - 8, tick_x, y + 54, stroke="#c0392b", width=2, dash="4,3")
        x += box_w + gap

    canvas.text(410, 234, "dashed ticks: the new filter removes one fixed", size=13, fill="#555")
    canvas.text(410, 252, "congruence class across every copy", size=13, fill="#555")
    return canvas


def diagram_03_candidate_composite_certified() -> Canvas:
    """Two rows of candidates at different stages: the safe zone's certified
    survivors stay certified, while a later-rejected candidate outside it
    shows how acceptance can still be overturned by a future prime."""
    canvas = Canvas(700, 320)
    xs = [90, 170, 250, 330, 410, 490, 570, 650]

    canvas.text(370, 30, "stage k", size=16, weight="bold")
    y = 110
    canvas.rect(70, y - 34, 300, 68, fill="#eafaf1", stroke="#27ae60", width=1.5, rx=6)
    canvas.text(220, y - 46, "safe zone", size=13, fill="#1e8449")
    for i, x in enumerate(xs):
        certified = x <= 330
        canvas.circle(x, y, r=8, fill="#27ae60" if certified else "white",
                  stroke="#27ae60" if certified else "#333")

    canvas.text(370, 210, "later stage", size=16, weight="bold")
    y2 = 260
    canvas.rect(70, y2 - 34, 300, 68, fill="#eafaf1", stroke="#27ae60", width=1.5, rx=6)
    for i, x in enumerate(xs):
        certified = x <= 330
        rejected = x == 490
        canvas.circle(x, y2, r=8, fill="#27ae60" if certified else "white",
                  stroke="#27ae60" if certified else "#333")
        if rejected:
            canvas.cross(x, y2, size=9)
    canvas.text(490, y2 + 34, "rejected by p_j", size=12, fill="#c0392b")
    return canvas


def diagram_04_safe_zone_boundary() -> Canvas:
    """The [p, p^2) certified window, contrasted with a twin-prime pair
    inside it (certified) versus one outside it (survives filters but not
    yet certified)."""
    canvas = Canvas(700, 300)
    x_p, x_p2 = 100, 560
    y = 70
    canvas.line(x_p, y, x_p2, y, width=3)
    for x, label in ((x_p, "p"), (x_p2, "p^2")):
        canvas.line(x, y - 10, x, y + 10, width=2)
        canvas.text(x, y - 20, label, size=15, weight="bold")
    canvas.text((x_p + x_p2) / 2, y + 30, "certified window", size=14)

    y2 = 160
    x1, x2 = 200, 320
    canvas.line(x1, y2, x2, y2, width=2)
    canvas.circle(x1, y2, fill="#27ae60", stroke="#27ae60")
    canvas.circle(x2, y2, fill="#27ae60", stroke="#27ae60")
    canvas.text((x1 + x2) / 2, y2 - 14, "2", size=13)
    canvas.text_sub(x1, y2 + 26, "x", "")
    canvas.text(x2, y2 + 26, "x+2", size=14)
    canvas.text((x1 + x2) / 2, y2 + 50, "certifies a twin-prime pair", size=13, fill="#1e8449")

    y3 = 250
    x3, x4 = 470, 590
    canvas.line(x3, y3, x4, y3, width=2)
    canvas.circle(x3, y3, fill="white", stroke="#e67e22")
    canvas.circle(x4, y3, fill="white", stroke="#e67e22")
    canvas.text((x3 + x4) / 2, y3 - 14, "2", size=13)
    canvas.text(x3, y3 + 26, "y", size=14)
    canvas.text(x4, y3 + 26, "y+2", size=14)
    canvas.text((x3 + x4) / 2, y3 + 50, "survives filters, not yet certified", size=13, fill="#af601a")
    return canvas


def diagram_05_full_period_vs_local_window() -> Canvas:
    """Contrasts the full (huge) period, which has many 2-gaps scattered
    across it, with the much smaller front safe-zone window that local
    observation is actually limited to."""
    canvas = Canvas(760, 240)
    y = 80
    canvas.line(60, y, 700, y, width=3)
    canvas.text(380, y - 46, "one huge period", size=15, weight="bold")
    tick_xs = [110, 170, 230, 310, 360, 430, 470, 540, 610, 660]
    for x in tick_xs:
        canvas.line(x, y - 8, x, y + 8, stroke="#7f8c8d", width=2)
    canvas.text(380, y + 30, "many 2-gaps across the full cycle", size=13, fill="#555")

    y2 = 190
    canvas.rect(60, y2 - 12, 180, 24, fill="#eafaf1", stroke="#27ae60", width=2)
    canvas.text(150, y2 - 24, "front safe window (p^2)", size=13, fill="#1e8449")
    canvas.text(150, y2 + 40, "does a 2-gap land here?", size=13, fill="#555", style="italic")
    return canvas


def diagram_06_two_gap_descendant_fan() -> Canvas:
    """One old 2-gap fanning out into its copies under a new prime q: exactly
    two forbidden congruence classes are removed, so q - 2 descendants survive."""
    canvas = Canvas(700, 360)
    root = (350, 50)
    canvas.circle(*root, r=8, fill="#222")
    canvas.text(root[0], root[1] - 20, "one old 2-gap", size=14, weight="bold")

    labels = ["copy 0", "copy 1", "copy 2", "...", "copy r", "..."]
    states = ["survives", "removed (left endpoint div. by q)", "survives", "", "removed (right endpoint div. by q)", ""]
    n = len(labels)
    xs_children = [140 + i * (420 / (n - 1)) for i in range(n)]
    y_child = 190
    for x, label, state in zip(xs_children, labels, states):
        canvas.line(root[0], root[1] + 8, x, y_child - 10, stroke="#999", width=1.5)
        ok = state.startswith("survives")
        removed = state.startswith("removed")
        color = "#27ae60" if ok else ("#c0392b" if removed else "#999")
        canvas.circle(x, y_child, r=7, fill=color if ok else "white", stroke=color)
        if removed:
            canvas.cross(x, y_child, size=7, stroke=color)
        canvas.text(x, y_child + 26, label, size=12)
        if state:
            words = state.split(" ", 1)
            canvas.text(x, y_child + 44, words[0], size=11, fill=color)
            if len(words) > 1:
                canvas.text(x, y_child + 60, words[1], size=10, fill="#666")

    canvas.text(350, 330, "odd new prime q: 2 forbidden copy classes, q - 2 descendants survive", size=13, fill="#555")
    return canvas


def diagram_07_two_focused_compression() -> Canvas:
    """Full gap sequence on top, its 2-focused compression below: every 2-gap
    kept as its own cell, runs between them collapsed into one summed cell."""
    canvas = Canvas(760, 260)
    full_gaps = [6, 4, 2, 4, 2, 4, 6, 2]
    compressed = [10, 2, 4, 2, 10, 2]

    canvas.text(380, 30, "full gaps", size=16, weight="bold")
    box_w, y1 = 80, 60
    total = len(full_gaps) * box_w
    x0 = (canvas.width - total) / 2
    full_positions = []
    for i, gap in enumerate(full_gaps):
        x = x0 + i * box_w
        is_two = gap == 2
        canvas.rect(x, y1, box_w - 6, 44, fill="#eafaf1" if is_two else "#f7f7f7",
               stroke="#27ae60" if is_two else "#999")
        canvas.text(x + (box_w - 6) / 2, y1 + 28, str(gap), size=15)
        full_positions.append(x + (box_w - 6) / 2)

    canvas.text(380, 170, "2-focused compression", size=16, weight="bold")
    box_w2, y2 = 106, 200
    total2 = len(compressed) * box_w2
    x0b = (canvas.width - total2) / 2
    for i, gap in enumerate(compressed):
        x = x0b + i * box_w2
        is_two = gap == 2
        canvas.rect(x, y2, box_w2 - 6, 44, fill="#eafaf1" if is_two else "#f7f7f7",
               stroke="#27ae60" if is_two else "#999")
        canvas.text(x + (box_w2 - 6) / 2, y2 + 28, str(gap), size=15)
    return canvas


def diagram_08_stage_summary_ladder() -> Canvas:
    """Table plus log-scale bar chart of illustrative stage/head/period/2-gap
    figures, showing period growing explosively while 2-gap count stays visible."""
    rows = [
        ("S_1", 3, 1, 1),
        ("S_2", 5, 2, 1),
        ("S_3", 7, 8, 3),
        ("S_4", 11, 48, 15),
    ]
    canvas = Canvas(880, 320)
    canvas.text(440, 30, "stage summary", size=16, weight="bold")

    table_rows = [["stage", "head", "period", "2-gaps"]] + [
        [stage, str(head), str(period), str(two_gaps)] for stage, head, period, two_gaps in rows
    ]
    canvas.table(40, 50, [100, 80, 100, 80], table_rows, row_height=30)

    chart_x0, chart_y0, chart_w = 540, 60, 220
    max_log = math.log10(max(period for _, _, period, _ in rows))
    for i, (stage, head, period, two_gaps) in enumerate(rows):
        y = chart_y0 + i * 34
        bar_w = chart_w * (math.log10(period) / max_log) if period > 1 else 4
        canvas.rect(chart_x0, y, bar_w, 14, fill="#5b8def")
        canvas.text(chart_x0 - 10, y + 12, stage, size=12, anchor="end")
        canvas.text(chart_x0 + bar_w + 8, y + 12, f"period={period}", size=11, anchor="start", fill="#555")
    canvas.text(chart_x0 + chart_w / 2, chart_y0 - 20, "period (log scale)", size=12, fill="#555")

    canvas.text(380, 240, "period grows explosively; 2-gaps stay visible in absolute count", size=13, fill="#555")
    canvas.text(380, 260, "(full-period statistic -- not a claim about local safe-zone occupancy)", size=12, fill="#888")
    return canvas


def diagram_09_rotation_is_change_of_view() -> Canvas:
    """Same gap cycle drawn twice: once from an arbitrary start, once rotated
    to start at the next stage's head -- rotation is a change of view, not new data."""
    canvas = Canvas(760, 240)
    before = [4, 2, 4, 6, 2]
    after = [2, 4, 6, 2, 4]
    box_w = 90

    def row(gaps, y, title, marker_label):
        """Draws one horizontal row of gap boxes with a title and a marker label below it."""
        total = len(gaps) * box_w
        x0 = (canvas.width - total) / 2
        canvas.text(canvas.width / 2, y - 30, title, size=15, weight="bold")
        for i, gap in enumerate(gaps):
            x = x0 + i * box_w
            canvas.rect(x, y, box_w - 6, 40, fill="#f7f7f7")
            canvas.text(x + (box_w - 6) / 2, y + 26, str(gap), size=15)
        canvas.text(x0 + (box_w - 6) / 2, y + 62, "^", size=16, anchor="middle")
        canvas.text(x0 + (box_w - 6) / 2, y + 80, marker_label, size=11, fill="#555")
        return x0

    row(before, 60, "before rotation", "arbitrary start")
    row(after, 160, "after rotation", "next head start")
    return canvas


def diagram_10_article_figure_map() -> Canvas:
    """Reference table mapping each article area to the diagram(s) above best
    suited to illustrate it."""
    rows = [
        ["Article Area", "Best Diagrams"],
        ["Sieve sequence construction", "Repeated Period, Rotation View"],
        ["Copy-or-merge theorem", "Copy-Or-Merge Strip"],
        ["Acceptance vs primality", "Candidate/Composite/Certified"],
        ["Gap dynamics, 2-gap survival", "Descendant Fan, Full-Period vs Local"],
        ["Safe-zone discussion", "Safe-Zone Boundary"],
        ["Empirical Spark section", "Stage Ladder, 2-Focused Compression"],
    ]
    canvas = Canvas(820, 60 + 32 * len(rows))
    canvas.text(410, 30, "article figure map", size=16, weight="bold")
    canvas.table(30, 50, [280, 510], rows, row_height=32)
    return canvas


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
    """Builds and writes every diagram in DIAGRAMS to OUT_DIR as an SVG file."""
    os.makedirs(OUT_DIR, exist_ok=True)
    for name, build in DIAGRAMS.items():
        canvas = build()
        path = os.path.join(OUT_DIR, f"{name}.svg")
        save(canvas, path)
        print(f"wrote {path}")


if __name__ == "__main__":
    main()
