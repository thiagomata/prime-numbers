"""Hit/miss matrices: which sieve-sequence survivors are actually prime, one
small 10x10 grid per early stage, shown as small multiples in a 3-column,
2-row layout (6 stages total, starting from stage 0 -- head=2, no filtering
applied yet at all).

Stage 0 isn't in generate_gaps.py's own output (it deliberately starts
numbering at head=3, "stage 0" being trivial -- see its heads = first_k_primes(...)[1:]),
so it's synthesized here directly: with no prime filter applied yet, every
integer survives, so the "gap cycle" is the constant [1] and every integer
from head=2 upward is a candidate. Stages 1 up are read from the small
public sample (../../../data/sieve-sequence/first_gaps_per_seq.sample.csv,
100 stages x 100 gaps each), taking only the first NUM_MATRICES-1 of them.

Each stage's leading 100 survivors are reshaped into a 10x10 grid so every
individual number (and its color) is legible at a glance. This replaces an
earlier version that put all 100 stages into one 100x100 grid: at that
density (10,000 cells) individual values were illegible and the misses were
too fine to actually read; a single-row-of-panels version was legible but
didn't comfortably fit six stages side by side, hence the 3-column, 2-row
layout here.

Each cell shows the survivor's own value: green (references/palette.md
"good") if it's actually prime, red ("critical") if the filter accepted it
anyway even though it's composite (for stage 0, that's simply "is this
integer composite," since no filter has been applied yet) -- same
distinction as gap_heatmap.py's single-red-pixel-per-row mark, but
classifying every cell here instead of only the first.

Each panel's caption states two things this project already proves/derives
elsewhere, not fit to this chart specifically:
- "flagged": the exact fraction of all integers that reach this stage at all
  -- product of (1-1/q) over every prime q below the stage's head (see
  estimated_boundary_indices in gap_heatmap.py). Stage 0's is 1 (nothing
  filtered yet); stage 1's is exactly 1/2, since its only filter is "not
  even."
- the stage's exact periodic gap cycle (generate_gaps.py's
  compute_full_period), printed in full where short enough (stage 0: [1],
  stage 1: [2], stage 2: [2,4], stage 3: [4,2,4,2,4,6,2,6]) and by length
  only once it grows primorial-fast (stage 4: 48, stage 5: 480).

Run: python3 hit_miss_heatmap.py
Output: ./out/hit-miss-matrices.svg
"""

import csv
import os
from fractions import Fraction

from generate_gaps import compute_full_period, is_prime
from svg_kit import Canvas, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")
DATA_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "data", "sieve-sequence")
SAMPLE_CSV_PATH = os.path.join(DATA_DIR, "first_gaps_per_seq.sample.csv")

# Status colors (references/palette.md) -- reserved, fixed regardless of
# theme: green = the finite filter and true primality agree (hit), red = they
# disagree, i.e. a composite the filter let through (miss).
HIT_COLOR = "#0ca30c"
MISS_COLOR = "#d03b3b"
CELL_TEXT_COLOR = "#ffffff"

NUM_MATRICES = 6  # stage 0 (head=2) plus stages 1..5 (heads 3,5,7,11,13)
GRID_N = 10  # 10x10 = first 100 survivors of the stage
PANELS_PER_ROW = 3
CELL = 40
GAP = 3  # px left as background between adjacent fills
FILL = CELL - GAP
MAX_PRINTED_PERIOD = 8


def load_stages(path, n):
    """Returns n stages in order, stage 0 (head=2) synthesized directly since
    generate_gaps.py never generates it, stages 1..n-1 read from the CSV."""
    stages = [{"head": 2, "survivors": list(range(2, 2 + GRID_N * GRID_N))}]
    by_index = {}
    with open(path, newline="") as csv_file:
        for row in csv.DictReader(csv_file):
            idx = int(row["stage_index"])
            if idx > n - 1:
                continue
            entry = by_index.setdefault(idx, {"head": int(row["head"]), "survivors": []})
            entry["survivors"].append(int(row["survivor"]))
    stages.extend(by_index[i] for i in sorted(by_index))
    return stages


def stage_captions(stages):
    """Returns {stage_index: (flagged_fraction_str, gap_cycle_str)}, derived
    the same way generate_gaps.py's own main() builds up `tail` -- each
    stage's tail is every prior stage's head. Stage 0 starts from an empty
    tail (no filter applied yet), which is exactly what makes
    compute_full_period(2, []) come out to the constant gap cycle [1]."""
    captions = {}
    tail = []
    for i, stage in enumerate(stages):
        head = stage["head"]
        period = compute_full_period(head, tail)
        density = Fraction(1, 1)
        for p in tail:
            density *= Fraction(p - 1, p)
        period_str = (
            "gaps repeat: [" + ",".join(str(gap) for gap in period) + "]"
            if len(period) <= MAX_PRINTED_PERIOD
            else f"period length {len(period)} (too long to print)"
        )
        captions[i] = (f"flagged fraction: {density}", period_str)
        tail.append(head)
    return captions


def build_panel(canvas, x0, y0, stage_index, head, survivors, flagged_str, period_str):
    """Draws one stage's title, captions, and GRID_N x GRID_N hit/miss grid onto `canvas`."""
    canvas.text(x0 + GRID_N * CELL / 2, y0, f"Stage {stage_index} (head={head})", size=14, weight="bold")
    canvas.text(x0 + GRID_N * CELL / 2, y0 + 18, flagged_str, size=11, fill="#555")
    canvas.text(x0 + GRID_N * CELL / 2, y0 + 33, period_str, size=11, fill="#555")

    grid_y0 = y0 + 46
    for i, value in enumerate(survivors[:GRID_N * GRID_N]):
        row, col = divmod(i, GRID_N)
        x = x0 + col * CELL
        y = grid_y0 + row * CELL
        color = HIT_COLOR if is_prime(value) else MISS_COLOR
        canvas.rect(x, y, FILL, FILL, fill=color, stroke="none", width=0)
        canvas.text(x + FILL / 2, y + FILL / 2 + 4, str(value), size=10, fill=CELL_TEXT_COLOR)


def build_figure(stages) -> Canvas:
    """Lays out all stages' panels in a PANELS_PER_ROW-wide grid plus a bottom legend."""
    captions = stage_captions(stages)
    panel_w = GRID_N * CELL
    panel_h = 46 + GRID_N * CELL
    col_gutter = 40
    row_gutter = 30
    side_margin = 30
    top_margin = 50
    legend_h = 60

    n_cols = min(PANELS_PER_ROW, len(stages))
    n_rows = -(-len(stages) // PANELS_PER_ROW)  # ceil division

    canvas_w = side_margin * 2 + n_cols * panel_w + (n_cols - 1) * col_gutter
    canvas_h = top_margin + n_rows * panel_h + (n_rows - 1) * row_gutter + legend_h

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 24,
           "Hit/miss matrices: sieve survivors that are actually prime, first 100 of each stage (sample)",
           size=16, weight="bold")

    for i, stage in enumerate(stages):
        stage_index = i
        row, col = divmod(i, PANELS_PER_ROW)
        x0 = side_margin + col * (panel_w + col_gutter)
        y0 = top_margin + row * (panel_h + row_gutter)
        flagged_str, period_str = captions[stage_index]
        build_panel(canvas, x0, y0, stage_index, stage["head"], stage["survivors"], flagged_str, period_str)

    legend_y = top_margin + n_rows * panel_h + (n_rows - 1) * row_gutter + 24
    legend_x0 = side_margin
    swatch = 18
    canvas.rect(legend_x0, legend_y, swatch, swatch, fill=HIT_COLOR, stroke="#999", width=1)
    canvas.text(legend_x0 + swatch + 8, legend_y + 14,
           "hit -- actually prime", size=12, anchor="start", fill="#555")
    canvas.rect(legend_x0 + 220, legend_y, swatch, swatch, fill=MISS_COLOR, stroke="#999", width=1)
    canvas.text(legend_x0 + 220 + swatch + 8, legend_y + 14,
           "miss -- filter accepted a composite", size=12, anchor="start", fill="#555")

    return canvas


def main() -> None:
    """Loads NUM_MATRICES stages from the sample CSV and writes the hit/miss figure."""
    if not os.path.exists(SAMPLE_CSV_PATH):
        raise SystemExit(f"{SAMPLE_CSV_PATH} not found")
    os.makedirs(OUT_DIR, exist_ok=True)
    stages = load_stages(SAMPLE_CSV_PATH, NUM_MATRICES)
    canvas = build_figure(stages)
    path = os.path.join(OUT_DIR, "hit-miss-matrices.svg")
    save(canvas, path)
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
