"""Gap-cycle heatmap: one row per sieve stage, one cell per gap.

Reads ../../../data/sieve-sequence/first_gaps_per_seq.csv (written by
generate_gaps.py -- run that first) rather than recomputing anything.

The grid itself (one real pixel per gap, e.g. 2000 x 200) is rendered as a
raster PNG and embedded as a base64 data: URI inside the SVG -- one SVG
<rect> per cell doesn't scale (hundreds of thousands of elements, tens of MB
of markup for a grid this size). Row labels and the legend stay as ordinary
SVG text/rects on top, since there are only a few dozen of those.

Cell color is a sequential (one-hue, light to dark) encoding of the gap's
magnitude -- a fixed gap value always renders as the same shade wherever it
appears. The value -> position-on-ramp mapping is histogram-equalized rather
than linear: gap values are heavily right-skewed (a handful of small values
account for most of the data), so a plain min-max scale crams the common
range into the first couple of ramp steps and makes them indistinguishable.
Equalizing spreads ramp position by empirical frequency instead of raw
magnitude, so the crowded common values spread apart and the rare tail
compresses -- order is still preserved (still sequential), just not linear.

Run: python3 gap_heatmap.py
Output: ./out/gap-heatmap.svg (plain grid) and ./out/gap-heatmap-staggered.svg
(each row shifted 1px further right than the last -- a purely cosmetic shear,
no data meaning, that breaks up the diagonal streaking from the plain version
into something easier to visually parse). Each has a matching .png alongside
it with just the raw grid.
"""

import base64
import bisect
import csv
import os
from collections import Counter

from generate_gaps import is_prime
from png_writer import encode_png
from svg_kit import Canvas, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "out")
DATA_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "data", "sieve-sequence")
CSV_PATH = os.path.join(DATA_DIR, "first_gaps_per_seq.csv")

# Sequential blue ramp, light -> dark (references/palette.md in the dataviz skill).
SEQUENTIAL_BLUE = [
    "#cde2fb", "#b7d3f6", "#9ec5f4", "#86b6ef", "#6da7ec", "#5598e7",
    "#3987e5", "#2a78d6", "#256abf", "#1c5cab", "#184f95", "#104281", "#0d366b",
]

# Status red (references/palette.md "critical") -- reserved, never a series color,
# so it can't be confused with a magnitude value on the sequential ramp.
NOT_PRIME_MARK = "#d03b3b"

# Age view: orange (young/just-reset) -> blue (old/stable). Two hues instead of
# one specifically because "unknown" is rendered as pure white, and a single-hue
# ramp's lightest step (a pale, near-white blue) was too close to that to tell
# apart at a glance -- orange at the low end can never be confused with white.
AGE_RAMP = [
    "#f3ac7c", "#eb6834", "#c14f1e", "#8a5a3a",
    "#6b6070", "#4a5a8a", "#2a5486", "#184f95", "#0d366b",
]

# Independent of how much raw data generate_gaps.py produces (PREFIX_LEN can
# be in the hundreds of thousands, e.g. to widen the age view's known-data
# window) -- each chart still only *displays* this many columns. Without this
# cap, one real pixel per data cell means the SVG's embedded PNG grows exactly
# as wide as PREFIX_LEN, which produced literal 12-14MB files at
# PREFIX_LEN=100000. Charts that need less than this show their true width
# unpadded (e.g. the age view's known-prefix, usually well under this cap);
# charts with more available data than this are simply truncated to it.
MAX_DISPLAY_WIDTH = 1400

# Diverging pair for the row-to-row diff view (references/palette.md "blue <-> red";
# gray is the palette's "baseline/axis" neutral, not the diverging pair's own
# near-white midpoint -- that midpoint sits only a few RGB steps from pure white,
# which is also used for "no data", making the two indistinguishable at this scale).
# blue = this gap grew vs the previous stage, red = it shrank, gray = unchanged.
DIVERGING_GRAY = "#c3c2b7"
DIVERGING_BLUE_POLE = "#0d366b"
DIVERGING_RED_POLE = "#6a130c"

# Merge-count view: mostly "copied" (light neutral background), rare "merged"
# cells picked out in orange (categorical slot 8, references/palette.md) -- a
# short light->dark ramp in case a run ever merges 3+ old gaps, though in this
# dataset every merge observed is exactly a pair (count 2).
COPY_COLOR = "#dedcd5"
MERGE_ACCENT_RAMP = ["#fbdcc9", "#f3ac7c", "#eb6834", "#c14f1e", "#8a3712"]

# 2-focused compression view: every 2-gap keeps this fixed reserved color (the
# whole point of the view is to make 2-gaps immediately identifiable, so they
# get their own color, not a slot on the sequential ramp); everything between
# consecutive 2-gaps (the collapsed run of non-2 gaps) uses the sequential
# ramp instead, same equalization approach as the base heatmap.
TWO_GAP_COLOR = "#0ca30c"

# 2-gap frequency/cluster-size line charts: categorical slot 1 (blue) for the
# single-series frequency line and the "average" series; categorical slot 8
# (orange, same hex as MERGE_ACCENT_RAMP's midpoint) for the "max" series --
# validated pair (references/palette.md), floor-band CVD separation legal
# here since both lines carry a text-labeled legend (secondary encoding).
LINE_COLOR_PRIMARY = "#2a78d6"
LINE_COLOR_SECONDARY = "#eb6834"


def compress_around_two(gaps):
    """06-article-diagram-ideas.md, Diagram 7: keep every 2-gap as-is, sum
    consecutive runs of non-2 gaps into a single value representing the
    distance between consecutive 2-gaps. [6,4,2,4,2,4,6,2] -> [10,2,4,2,10,2].
    Linear, not cyclic (this data is a prefix, not a complete period) -- unlike
    GapLineage.scala's compressAround2, the leading/trailing runs are not
    wrapped together."""
    out = []
    run = 0
    for gap in gaps:
        if gap == 2:
            if run:
                out.append(run)
                run = 0
            out.append(2)
        else:
            run += gap
    if run:
        out.append(run)
    return out


def compress_around_two_with_anchor(gaps):
    """Like compress_around_two, but also returns, for each compressed
    output value, the index into `gaps` of the LAST raw gap that produced
    it -- the position whose lineage state (age, see compute_ages_per_row)
    a compressed unit inherits, since that's the same closing boundary
    lineage_walk anchors a run's merge/copy status on."""
    out = []
    anchors = []
    run = 0
    for i, gap in enumerate(gaps):
        if gap == 2:
            if run:
                out.append(run)
                anchors.append(i - 1)
                run = 0
            out.append(2)
            anchors.append(i)
        else:
            run += gap
    if run:
        out.append(run)
        anchors.append(len(gaps) - 1)
    return out, anchors


def load_stages():
    """Returns a list of {"head", "gaps": [...], "survivors": [...]} in stage_index order."""
    by_index = {}
    with open(CSV_PATH, newline="") as csv_file:
        for row in csv.DictReader(csv_file):
            idx = int(row["stage_index"])
            entry = by_index.setdefault(idx, {"head": int(row["head"]), "gaps": [], "survivors": []})
            entry["gaps"].append(int(row["gap"]))
            entry["survivors"].append(int(row["survivor"]))
    return [by_index[i] for i in sorted(by_index)]


def first_composite_index(survivors):
    """Index of the first survivor that passed the finite sieve filter but is
    not actually prime -- the point where "current acceptance" and "certified
    prime" first diverge for this stage (see 06-article-diagram-ideas.md,
    Diagram 3). Returns None if every survivor in the prefix is genuinely prime."""
    for i, survivor in enumerate(survivors):
        if not is_prime(survivor):
            return i
    return None


def estimated_boundary_indices(stages):
    """Dashed line: exact finite density (product of (1-1/q) over every prime
    q < head, computed exactly -- no asymptotic formula needed for this part)
    times the value-range (head^2 - head). This is a good fit (see
    properties/sieve-sequence/safe-zone-exhaustion-curve.md) but NOT proven:
    it assumes survivors are evenly spread across that range, which is true on
    average but not guaranteed at any specific point. One value per stage,
    always computed (never None)."""
    indices = []
    density = 1.0 - 1.0 / 2  # every stage's head is odd, so 2 is always in its filter set
    for stage in stages:
        p = stage["head"]
        indices.append(density * (p * p - p))
        density *= (1 - 1.0 / p)
    return indices


def proven_safe_boundary_indices(stages):
    """Solid line: a genuine mathematical guarantee, not an estimate --
    "every column left of this is certainly still inside the safe zone," true
    for any prime p, not fit to this dataset. Built from two proven facts:
    (1) the first composite survivor of stage p is exactly p^2 (elementary,
    provable directly, see safe-window-two-gaps-certify-twin-primes.md);
    (2) Schroeder's explicit, unconditional lower bound on rough-number
    counts (J.Z. Schroeder, "A lower bound on the number of rough numbers,"
    arXiv:1705.04831, 2017): for every prime p >= 11 and every n >= 2p,

        Phi(n, p) >= floor(2n/p) + 1

    where Phi(n,p) counts integers in [1,n] with no prime factor < p. Applied
    with n = p^2-1 (comfortably satisfies n >= 2p for every p in this
    dataset), adjusted by -1 for the single rough number (1 itself) below p.

    This is considerably LOOSER than estimated_boundary_indices -- Schroeder's
    bound grows linearly in p, the true count grows like p^2/ln(p) -- which is
    the expected price of a bound proven for every prime unconditionally,
    rather than one merely observed to fit this dataset (see
    properties/sieve-sequence/safe-zone-exhaustion-curve.md for the full
    derivation and why an earlier attempt using Rosser & Schoenfeld's density
    bound was withdrawn: it bounds a global/periodic average, not a specific
    short interval, and closing that gap needs more than this repo attempted).
    Returns None for p < 11, outside the theorem's proven range."""
    indices = []
    for stage in stages:
        p = stage["head"]
        if p < 11:
            indices.append(None)
            continue
        n = p * p - 1
        indices.append(float((2 * n) // p + 1 - 1))
    return indices


def draw_boundary_curves(canvas, stages, label_w, top_margin, cell_w_display, cell_h_display, stagger, prefix_len, legend_y):
    """Draws both chaos-to-order boundary curves and cites their sources
    directly on the chart. See properties/sieve-sequence/safe-zone-exhaustion-curve.md
    for the full derivation of both, including why an earlier attempted proof
    (Rosser & Schoenfeld's density bound applied naively to a short interval)
    was withdrawn as unjustified."""
    def to_xy(row, idx):
        """Converts a (row, column-index) pair into canvas (x, y) pixel coordinates for this grid."""
        col = min(idx, prefix_len)
        x = label_w + stagger * row + col * cell_w_display
        y = top_margin + row * cell_h_display + cell_h_display / 2
        return (x, y)

    estimated_points = [to_xy(row, boundary_idx) for row, boundary_idx in enumerate(estimated_boundary_indices(stages))]
    canvas.polyline(estimated_points, stroke="#000000", width=1.5, dash="6,4")

    run = []
    for row, boundary_idx in enumerate(proven_safe_boundary_indices(stages)):
        if boundary_idx is None:
            if len(run) > 1:
                canvas.polyline(run, stroke="#000000", width=3)
            run = []
        else:
            run.append(to_xy(row, boundary_idx))
    if len(run) > 1:
        canvas.polyline(run, stroke="#000000", width=3)

    canvas.text(label_w, legend_y, "- - - estimated boundary (good fit, not proven)", size=11, anchor="start", fill="#555")
    canvas.link_text(label_w, legend_y + 16,
                "— proven safe boundary, any prime p≥11 (Schroeder 2017, arXiv:1705.04831)",
                "https://arxiv.org/abs/1705.04831", size=11, anchor="start")


def hex_to_rgb(hex_color: str):
    """Converts a "#rrggbb" hex color string into an (r, g, b) integer tuple."""
    hex_color = hex_color.lstrip("#")
    return tuple(int(hex_color[i:i + 2], 16) for i in (0, 2, 4))


def ramp_color(position: float, ramp=SEQUENTIAL_BLUE):
    """Continuous interpolation across the ramp anchors, position in [0, 1]."""
    n = len(ramp)
    scaled = min(max(position, 0.0), 1.0) * (n - 1)
    i0 = int(scaled)
    i1 = min(i0 + 1, n - 1)
    frac = scaled - i0
    c0, c1 = hex_to_rgb(ramp[i0]), hex_to_rgb(ramp[i1])
    return tuple(round(c0[k] + (c1[k] - c0[k]) * frac) for k in range(3))


def build_equalized_color_map(all_values, ramp=SEQUENTIAL_BLUE):
    """Maps each distinct value to a ramp position by empirical cumulative
    frequency (histogram equalization) instead of linear magnitude, so ramp
    usage matches how much data actually sits at each value."""
    counts = Counter(all_values)
    total = sum(counts.values())
    color_by_value = {}
    cum = 0
    for value in sorted(counts):
        position = (cum + counts[value] / 2) / total
        color_by_value[value] = ramp_color(position, ramp)
        cum += counts[value]
    return color_by_value


def lerp_rgb(c0, c1, frac: float):
    """Linearly interpolates between two (r, g, b) tuples at the given fraction."""
    return tuple(round(c0[k] + (c1[k] - c0[k]) * frac) for k in range(3))


def build_diverging_color_map(all_diffs):
    """Maps each distinct diff to a color: exactly 0 is neutral gray, positive
    diffs equalize (by empirical frequency, same reasoning as the sequential
    map) toward the blue pole, negative diffs equalize toward the red pole --
    each arm scaled independently so rare-but-large changes on one side don't
    wash out common-but-small changes on the other."""
    gray = hex_to_rgb(DIVERGING_GRAY)
    blue_pole = hex_to_rgb(DIVERGING_BLUE_POLE)
    red_pole = hex_to_rgb(DIVERGING_RED_POLE)

    def equalized_position(magnitudes):
        """Maps each distinct magnitude to its empirical cumulative-frequency
        position in [0, 1] (same equalization approach as build_equalized_color_map)."""
        counts = Counter(magnitudes)
        total = sum(counts.values())
        position_by_magnitude = {}
        cum = 0
        for magnitude in sorted(counts):
            position_by_magnitude[magnitude] = (cum + counts[magnitude] / 2) / total
            cum += counts[magnitude]
        return position_by_magnitude

    color_by_diff = {0: gray}
    for magnitude, position in equalized_position([diff for diff in all_diffs if diff > 0]).items():
        color_by_diff[magnitude] = lerp_rgb(gray, blue_pole, position)
    for magnitude, position in equalized_position([-diff for diff in all_diffs if diff < 0]).items():
        color_by_diff[-magnitude] = lerp_rgb(gray, red_pole, position)
    return color_by_diff


def lineage_walk(prev, cur):
    """Compares `cur` against `prev` via the true copy-or-merge lineage, not
    same-column index -- row `cur` starts at a bigger head than `prev`, so
    "same index" in each row points at unrelated regions of the number line.

    Every stage adds exactly one new filter prime (its own previous head), so
    `cur`'s survivors (from `cur`'s head onward) are exactly `prev`'s
    survivors with multiples of `prev`'s head removed. Walking `prev`'s own
    gaps from the point its value reaches `cur`'s head, accumulating a run
    until hitting a survivor NOT divisible by `prev`'s head (a kept
    boundary), reconstructs exactly which `prev` gaps map to each `cur` gap:
    a lone gap means "copied" (merge_count=1), several summed means "merged"
    (merge_count=2+). Per the copy-or-merge theorem, `diff` recovers exactly 0
    everywhere it can be computed -- the only reason to fall short of that is
    running out of `prev` gaps to keep accumulating before the run closes,
    since older (smaller-head) stages consume more than one `prev` gap per
    `cur` gap on average. `merge_count` is where the actual visual interest
    is: mostly 1 (copy), rarely 2+ (merge), varying cell to cell. `anchor_idx`
    is the index into `prev["gaps"]` of the run's closing (kept) boundary --
    the position whose lineage state (e.g. age, see compute_ages_per_row)
    this `cur` gap directly continues from. Returns a list of
    (diff, merge_count, anchor_idx) no longer than len(cur["gaps"]), possibly
    shorter if the window runs out.
    """
    prev_left_endpoints = [prev["head"]] + prev["survivors"][:-1]
    j = bisect.bisect_left(prev_left_endpoints, cur["head"])
    out = []
    for cur_gap in cur["gaps"]:
        if j >= len(prev["gaps"]):
            break
        acc = prev["gaps"][j]
        merge_count = 1
        while prev["survivors"][j] % prev["head"] == 0:
            j += 1
            if j >= len(prev["gaps"]):
                return out
            acc += prev["gaps"][j]
            merge_count += 1
        out.append((cur_gap - acc, merge_count, j))
        j += 1
    return out


def simple_shift_row_diff(prev, cur):
    """The cheaper alternative to lineage_walk: shift `prev` by a single
    constant offset (found once, the same way lineage_walk finds its starting
    point -- where prev's own value reaches cur's head) and compare index for
    index, with no further correction as merges occur along the row.

    This matches lineage_walk exactly up to the row's first real merge, since
    before that point every gap is a plain copy and the constant offset IS
    the true one. After a merge, the true offset permanently steps by one
    more than the constant assumes, so every position from there on reads as
    a mismatch (even though the underlying gap values are, per the theorem,
    still exactly explained by copy-or-merge -- the mismatch here is an
    artifact of not tracking that step, not a real deviation).

    Whether a row shows any mismatch at all within a fixed-length prefix
    therefore isn't about "merges got rarer" so much as whether the row's
    first possible merge point (prev's head squared, see
    first_composite_index) falls inside the window this prefix reaches.
    Returns a list no longer than len(cur["gaps"])."""
    prev_left_endpoints = [prev["head"]] + prev["survivors"][:-1]
    shift = bisect.bisect_left(prev_left_endpoints, cur["head"])
    n = min(len(cur["gaps"]), len(prev["gaps"]) - shift)
    return [cur["gaps"][i] - prev["gaps"][i + shift] for i in range(n)]


def compute_ages_per_row(stages, walks_per_row=None):
    """Cumulative gap age, per the intent documented in the project's own
    GapLineage.scala ("consecutive stages persisted; resets to 1 on merge") --
    not yet actually wired up there (SieveStage.scala's trackLineage hardcodes
    age=1 for every gap), so this carries it forward properly across all
    stages: age=1 right after a merge, age=(ancestor's age)+1 for a plain
    copy. Row 0 has no prior lineage, so every one of its gaps starts at
    age=1. A position with unknown age (the lineage_walk window ran out
    before reaching it, or its ancestor's age was itself unknown) is None.

    walks_per_row, if given, must be lineage_walk(stages[row-1], stages[row])
    for each row >= 1 (row 0 unused) -- pass this in when the caller already
    computed it (see build_diff_heatmap/build_merge_heatmap in main()) so the
    same O(stages x prefix_len) lineage isn't walked a second time."""
    ages_per_row = [[1] * len(stages[0]["gaps"])]
    for row in range(1, len(stages)):
        prev_ages = ages_per_row[-1]
        walk = walks_per_row[row] if walks_per_row is not None else lineage_walk(stages[row - 1], stages[row])
        new_ages = [None] * len(stages[row]["gaps"])
        for i, (_diff, merge_count, anchor_idx) in enumerate(walk):
            if merge_count > 1:
                new_ages[i] = 1
            elif anchor_idx < len(prev_ages) and prev_ages[anchor_idx] is not None:
                new_ages[i] = prev_ages[anchor_idx] + 1
        ages_per_row.append(new_ages)
    return ages_per_row


def build_diff_grid_png(stages, color_by_diff, diffs_per_row, display_width, stagger=0):
    """Row 0 has no previous row and is left blank (white). Every other row's
    diffs (see aligned_row_diff) render gray wherever the copy-or-merge
    theorem's exact-preservation holds (the overwhelming case), colored only
    at a genuine deviation, and blank past the point the comparison window
    ran out of previous-row data to keep checking. Rows are truncated to
    `display_width` regardless of how much underlying data exists -- see
    MAX_DISPLAY_WIDTH."""
    width = display_width + stagger * (len(stages) - 1)
    rows_rgb = []
    for row_idx, row_diffs in enumerate(diffs_per_row):
        offset = stagger * row_idx
        row = bytearray(b"\xff\xff\xff" * width)
        for i, diff in enumerate(row_diffs[:display_width]):
            red, green, blue = color_by_diff[diff]
            pos = offset + i
            row[pos * 3:pos * 3 + 3] = bytes((red, green, blue))
        rows_rgb.append(bytes(row))
    return width, len(stages), rows_rgb


def build_grid_png(stages, color_by_value, display_width, stagger=0):
    """stagger: extra pixels of blank (white) padding prepended to row i, times
    i -- i.e. row i starts at column i*stagger instead of column 0. Purely a
    display shear with no data meaning: it exists only to break up the diagonal
    streaking that makes a straight (unstaggered) grid hard to visually parse,
    by turning near-diagonal runs into near-vertical ones. Rows are truncated
    to `display_width` regardless of how much underlying data exists -- see
    MAX_DISPLAY_WIDTH."""
    width = display_width + stagger * (len(stages) - 1)
    not_prime_rgb = hex_to_rgb(NOT_PRIME_MARK)
    rows_rgb = []
    for row_idx, stage in enumerate(stages):
        offset = stagger * row_idx
        row = bytearray(b"\xff\xff\xff" * width)
        for i, gap in enumerate(stage["gaps"][:display_width]):
            red, green, blue = color_by_value[gap]
            pos = offset + i
            row[pos * 3:pos * 3 + 3] = bytes((red, green, blue))
        composite_at = first_composite_index(stage["survivors"])
        if composite_at is not None and composite_at < display_width:
            pos = offset + composite_at
            row[pos * 3:pos * 3 + 3] = bytes(not_prime_rgb)
        rows_rgb.append(bytes(row))
    return width, len(stages), rows_rgb


def calibration_values(rows, target_width, exclude=None):
    """Flattened values from the first `target_width` entries of each row --
    exactly what the matching build_*_grid_png actually draws for that row.
    The frequency-equalized color ramp must be calibrated on this same slice,
    not on the full (possibly much longer) row data, or its ramp positions
    stop matching what's actually on screen (see MAX_DISPLAY_WIDTH). `exclude`,
    if given, is a value skipped everywhere (e.g. TWO_GAP_COLOR's fixed 2,
    which never uses the ramp); None entries (unknown/not-yet-computed) are
    always skipped."""
    return [
        value for row in rows for value in row[:target_width]
        if value is not None and value != exclude
    ]


def run_ages_for_calibration(compressed_per_row, ages_2focused_per_row, target_width):
    """Like calibration_values, but for the 2-focused age view specifically:
    only non-2-gap runs use the age ramp (see build_age_2focused_grid_png),
    so calibration must walk `compressed_per_row` and `ages_2focused_per_row`
    together, in lockstep, both sliced to target_width."""
    return [
        age
        for compressed, ages in zip(compressed_per_row, ages_2focused_per_row)
        for value, age in zip(compressed[:target_width], ages[:target_width])
        if value != 2 and age is not None
    ]


def sample_for_legend(distinct_values, cap=24, keep=()):
    """Caps a legend to at most `cap` swatches: every distinct value if there
    are few enough to fit, otherwise a stride through them, always keeping
    `keep` (e.g. 0 for a diverging legend) plus the first and last values."""
    distinct_values = list(distinct_values)
    if len(distinct_values) <= cap:
        return distinct_values
    stride = max(1, len(distinct_values) // cap)
    return sorted({*distinct_values[::stride], *keep, distinct_values[0], distinct_values[-1]})


def heatmap_cell_size(display_width, num_stages):
    """Shared cell sizing for every heatmap view: the grid is scaled toward
    roughly 2000 x 900 real pixels, with a floor so cells never round down to
    nothing and a ceiling so a small number of stages doesn't produce huge rows."""
    cell_w_display = max(1, 2000 // display_width)
    cell_h_display = max(2, min(20, 900 // num_stages))
    return cell_w_display, cell_h_display


def heatmap_canvas_width(label_w, grid_w, legend_slot_count, legend_slot_w=32, extra=20):
    """Canvas must be wide enough for the grid AND for however many legend
    swatches get laid out left-to-right -- whichever is wider. Every heatmap
    view must apply this safeguard: a view that skipped it clipped its own
    legend off the right edge whenever legend_slot_count grew past what the
    grid alone would need."""
    return max(label_w + grid_w + extra, label_w + legend_slot_count * legend_slot_w)


def draw_row_head_labels(canvas, stages, label_w, top_margin, cell_h_display):
    """Sparse 'h=<head>' labels down the left edge, roughly one per 40 rows,
    shared by every heatmap view."""
    label_every = max(1, len(stages) // 40)
    for row, stage in enumerate(stages):
        if row % label_every == 0:
            y = top_margin + row * cell_h_display + cell_h_display / 2 + 4
            canvas.text(label_w - 12, y, f"h={stage['head']}", size=11, anchor="end")


def render_grid_png(png_path, width_px, height_px, rows_rgb) -> str:
    """Encodes the grid once, writes it to png_path (the committed .png
    alongside each .svg), and returns those same bytes as a base64 data: URI
    ready to embed in the SVG -- avoids writing the file and then reopening it
    just to get bytes already sitting in memory."""
    png_bytes = encode_png(width_px, height_px, rows_rgb)
    with open(png_path, "wb") as png_file:
        png_file.write(png_bytes)
    return f"data:image/png;base64,{base64.b64encode(png_bytes).decode('ascii')}"


def build_heatmap(stages, stagger=0, png_name="gap-heatmap.png", title_suffix="") -> Canvas:
    """Builds the base gap-value heatmap: raster grid, row head labels, both
    boundary curves, and a frequency-equalized legend."""
    prefix_len = len(stages[0]["gaps"])
    display_width = min(prefix_len, MAX_DISPLAY_WIDTH)
    all_values = calibration_values([stage["gaps"] for stage in stages], display_width)
    color_by_value = build_equalized_color_map(all_values)
    distinct_values = sorted(color_by_value)

    grid_w_px, grid_h_px, rows_rgb = build_grid_png(stages, color_by_value, display_width, stagger=stagger)
    image_uri = render_grid_png(os.path.join(OUT_DIR, png_name), grid_w_px, grid_h_px, rows_rgb)

    cell_w_display, cell_h_display = heatmap_cell_size(display_width, len(stages))
    label_w = 90
    legend_h = 122
    top_margin = 50

    grid_w = grid_w_px * cell_w_display
    grid_h = len(stages) * cell_h_display
    canvas_w = heatmap_canvas_width(label_w, grid_w, len(distinct_values))
    canvas_h = top_margin + grid_h + legend_h

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"Gap heatmap: first {display_width} of {prefix_len} generated gaps across {len(stages)} stages{title_suffix}",
           size=16, weight="bold")

    canvas.image(label_w, top_margin, grid_w, grid_h, image_uri)
    canvas.rect(label_w, top_margin, grid_w, grid_h, fill="none", stroke="#ccc", width=1)

    draw_row_head_labels(canvas, stages, label_w, top_margin, cell_h_display)

    draw_boundary_curves(canvas, stages, label_w, top_margin, cell_w_display, cell_h_display, stagger, display_width,
                          legend_y=top_margin + grid_h + 20)

    legend_y = top_margin + grid_h + 62
    legend_x0 = label_w
    swatch_w = 26
    canvas.text(legend_x0, legend_y - 10,
           "gap value (color spread by frequency, not raw magnitude)",
           size=12, fill="#555", anchor="start")
    for i, value in enumerate(distinct_values):
        x = legend_x0 + i * (swatch_w + 4)
        red, green, blue = color_by_value[value]
        canvas.rect(x, legend_y, swatch_w, 20, fill=f"rgb({red},{green},{blue})", stroke="#999", width=1)
        canvas.text(x + swatch_w / 2, legend_y + 34, str(value), size=10)

    mark_x = legend_x0 + len(distinct_values) * (swatch_w + 4) + 20
    canvas.rect(mark_x, legend_y, swatch_w, 20, fill=NOT_PRIME_MARK, stroke="#999", width=1)
    canvas.text(mark_x + swatch_w + 8, legend_y + 15, "first survivor that isn't actually prime", size=12, anchor="start", fill="#555")

    return canvas


def choose_compressed_width(compressed_per_row, percentile=0):
    """Compression ratio varies a lot: the first couple of stages barely
    compress at all (nearly every gap is a 2-gap), while the rest plateau at
    a much shorter, tightly clustered length. Sizing the canvas to the single
    longest row stretches everything else out with mostly blank padding.
    Default percentile=0 -- the shortest row -- guarantees every single row
    fills the canvas completely with real data and none shows any white
    padding at all; every row longer than that gets truncated (a small loss
    for the bulk of rows clustered near the plateau, a larger one for the
    handful of low-head outliers, whose tail is repetitive anyway)."""
    lens = sorted(len(row) for row in compressed_per_row)
    idx = min(len(lens) - 1, int(len(lens) * percentile / 100))
    return lens[idx]


def build_compressed_grid_png(stages, compressed_per_row, color_by_value, width, stagger=0):
    """Rows longer than `width` are truncated to it; rows shorter are padded
    with blank (white) on the right -- rare once `width` is chosen well (see
    choose_compressed_width), but still possible for the very shortest rows."""
    full_width = width + stagger * (len(stages) - 1)
    two_gap_rgb = hex_to_rgb(TWO_GAP_COLOR)
    rows_rgb = []
    for row_idx, compressed in enumerate(compressed_per_row):
        offset = stagger * row_idx
        row = bytearray(b"\xff\xff\xff" * full_width)
        for i, value in enumerate(compressed[:width]):
            rgb = two_gap_rgb if value == 2 else color_by_value[value]
            pos = offset + i
            row[pos * 3:pos * 3 + 3] = bytes(rgb)
        rows_rgb.append(bytes(row))
    return full_width, len(stages), rows_rgb


def build_compressed_heatmap(stages, stagger=0, png_name="gap-heatmap-2focused.png", title_suffix="") -> Canvas:
    """Builds the 2-focused compression heatmap: 2-gaps rendered standalone in
    a fixed color, runs between consecutive 2-gaps collapsed and colored by
    the equalized sequential ramp."""
    compressed_per_row = [compress_around_two(stage["gaps"]) for stage in stages]
    target_width = min(choose_compressed_width(compressed_per_row), MAX_DISPLAY_WIDTH)
    non_two_values = calibration_values(compressed_per_row, target_width, exclude=2)
    color_by_value = build_equalized_color_map(non_two_values)
    distinct_values = sorted(color_by_value)
    legend_values = sample_for_legend(distinct_values)

    grid_w_px, grid_h_px, rows_rgb = build_compressed_grid_png(
        stages, compressed_per_row, color_by_value, target_width, stagger=stagger)
    image_uri = render_grid_png(os.path.join(OUT_DIR, png_name), grid_w_px, grid_h_px, rows_rgb)

    cell_w_display, cell_h_display = heatmap_cell_size(target_width, len(stages))
    label_w = 90
    legend_h = 90
    top_margin = 50

    grid_w = grid_w_px * cell_w_display
    grid_h = len(stages) * cell_h_display
    # +1 legend slot: the fixed "2" swatch drawn before the loop occupies one
    # slot of its own (see the loop's (i + 1) offset below).
    canvas_w = heatmap_canvas_width(label_w, grid_w, len(legend_values) + 1)
    canvas_h = top_margin + grid_h + legend_h

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"2-focused compression heatmap: {len(stages)} stages, {target_width} units per row (shortest row, longer rows truncated){title_suffix}",
           size=16, weight="bold")

    canvas.image(label_w, top_margin, grid_w, grid_h, image_uri)
    canvas.rect(label_w, top_margin, grid_w, grid_h, fill="none", stroke="#ccc", width=1)

    draw_row_head_labels(canvas, stages, label_w, top_margin, cell_h_display)

    legend_y = top_margin + grid_h + 30
    legend_x0 = label_w
    swatch_w = 26
    canvas.text(legend_x0, legend_y - 10,
           "green = a 2-gap; blue = distance between consecutive 2-gaps (color spread by frequency)",
           size=12, fill="#555", anchor="start")
    canvas.rect(legend_x0, legend_y, swatch_w, 20, fill=TWO_GAP_COLOR, stroke="#999", width=1)
    canvas.text(legend_x0 + swatch_w / 2, legend_y + 34, "2", size=10)
    for i, value in enumerate(legend_values):
        x = legend_x0 + (i + 1) * (swatch_w + 4)
        red, green, blue = color_by_value[value]
        canvas.rect(x, legend_y, swatch_w, 20, fill=f"rgb({red},{green},{blue})", stroke="#999", width=1)
        canvas.text(x + swatch_w / 2, legend_y + 34, str(value), size=10)

    return canvas


def build_diff_heatmap(stages, stagger=0, png_name="gap-heatmap-diff.png", title_suffix="", walks_per_row=None) -> Canvas:
    """Builds the rigorous copy-or-merge diff heatmap: each cell is a gap's
    change vs the previous stage per lineage_walk, colored on the diverging
    ramp (see build_diverging_color_map).

    walks_per_row, if given, must be lineage_walk(stages[row-1], stages[row])
    for each row >= 1 (row 0 unused) -- pass this in when the caller already
    computed it (see main(), which shares one pass across this and
    build_merge_heatmap) instead of walking the same lineage twice."""
    prefix_len = len(stages[0]["gaps"])
    display_width = min(prefix_len, MAX_DISPLAY_WIDTH)
    walks_per_row = walks_per_row if walks_per_row is not None else (
        [[]] + [lineage_walk(stages[row - 1], stages[row]) for row in range(1, len(stages))]
    )
    diffs_per_row = [[diff for diff, _merge_count, _anchor_idx in walk] for walk in walks_per_row]
    all_diffs = calibration_values(diffs_per_row, display_width)
    color_by_diff = build_diverging_color_map(all_diffs)
    distinct_diffs = sorted(color_by_diff)
    legend_values = sample_for_legend(distinct_diffs, keep=(0,))

    grid_w_px, grid_h_px, rows_rgb = build_diff_grid_png(stages, color_by_diff, diffs_per_row, display_width, stagger=stagger)
    image_uri = render_grid_png(os.path.join(OUT_DIR, png_name), grid_w_px, grid_h_px, rows_rgb)

    cell_w_display, cell_h_display = heatmap_cell_size(display_width, len(stages))
    label_w = 90
    legend_h = 90
    top_margin = 50

    grid_w = grid_w_px * cell_w_display
    grid_h = len(stages) * cell_h_display
    canvas_w = heatmap_canvas_width(label_w, grid_w, len(legend_values))
    canvas_h = top_margin + grid_h + legend_h

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"Gap diff heatmap: change vs previous stage, {display_width} of {prefix_len} gaps x {len(stages)} stages{title_suffix}",
           size=16, weight="bold")

    canvas.image(label_w, top_margin, grid_w, grid_h, image_uri)
    canvas.rect(label_w, top_margin, grid_w, grid_h, fill="none", stroke="#ccc", width=1)

    draw_row_head_labels(canvas, stages, label_w, top_margin, cell_h_display)

    legend_y = top_margin + grid_h + 30
    legend_x0 = label_w
    swatch_w = 26
    canvas.text(legend_x0, legend_y - 10,
           "true copy-or-merge lineage vs previous stage (gray = exact match, blue = grew, red = shrank, "
           "white = ran out of previous-stage data to check)",
           size=12, fill="#555", anchor="start")
    for i, diff in enumerate(legend_values):
        x = legend_x0 + i * (swatch_w + 4)
        red, green, blue = color_by_diff[diff]
        canvas.rect(x, legend_y, swatch_w, 20, fill=f"rgb({red},{green},{blue})", stroke="#999", width=1)
        canvas.text(x + swatch_w / 2, legend_y + 34, ("+" if diff > 0 else "") + str(diff), size=10)

    return canvas


def build_simple_shift_diff_heatmap(stages, stagger=0, png_name="gap-heatmap-diff-simple-shift.png", title_suffix="") -> Canvas:
    """Same rendering as build_diff_heatmap, but using simple_shift_row_diff
    (one constant offset per row, no merge tracking) instead of lineage_walk.
    Matches the rigorous version exactly up to each row's first real merge;
    every position after that reads as a mismatch, not because the gap values
    actually diverge (they don't -- see simple_shift_row_diff's docstring) but
    because the naive constant offset falls one step behind at that point and
    stays behind for the rest of the row."""
    prefix_len = len(stages[0]["gaps"])
    display_width = min(prefix_len, MAX_DISPLAY_WIDTH)
    diffs_per_row = [[]] + [simple_shift_row_diff(stages[row - 1], stages[row]) for row in range(1, len(stages))]
    all_diffs = calibration_values(diffs_per_row, display_width)
    color_by_diff = build_diverging_color_map(all_diffs)
    distinct_diffs = sorted(color_by_diff)
    legend_values = sample_for_legend(distinct_diffs, keep=(0,))

    grid_w_px, grid_h_px, rows_rgb = build_diff_grid_png(stages, color_by_diff, diffs_per_row, display_width, stagger=stagger)
    image_uri = render_grid_png(os.path.join(OUT_DIR, png_name), grid_w_px, grid_h_px, rows_rgb)

    cell_w_display, cell_h_display = heatmap_cell_size(display_width, len(stages))
    label_w = 90
    legend_h = 122
    top_margin = 50

    grid_w = grid_w_px * cell_w_display
    grid_h = len(stages) * cell_h_display
    canvas_w = heatmap_canvas_width(label_w, grid_w, len(legend_values))
    canvas_h = top_margin + grid_h + legend_h

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"Gap diff heatmap (simple constant shift, no merge tracking): {display_width} of {prefix_len} gaps x {len(stages)} stages{title_suffix}",
           size=16, weight="bold")

    canvas.image(label_w, top_margin, grid_w, grid_h, image_uri)
    canvas.rect(label_w, top_margin, grid_w, grid_h, fill="none", stroke="#ccc", width=1)

    draw_row_head_labels(canvas, stages, label_w, top_margin, cell_h_display)

    draw_boundary_curves(canvas, stages, label_w, top_margin, cell_w_display, cell_h_display, stagger, display_width,
                          legend_y=top_margin + grid_h + 20)

    legend_y = top_margin + grid_h + 62
    legend_x0 = label_w
    swatch_w = 26
    canvas.text(legend_x0, legend_y - 10,
           "constant-offset diff vs previous stage (gray = matches so far, color = one step behind "
           "after the row's first real merge, white = ran out of data)",
           size=12, fill="#555", anchor="start")
    for i, diff in enumerate(legend_values):
        x = legend_x0 + i * (swatch_w + 4)
        red, green, blue = color_by_diff[diff]
        canvas.rect(x, legend_y, swatch_w, 20, fill=f"rgb({red},{green},{blue})", stroke="#999", width=1)
        canvas.text(x + swatch_w / 2, legend_y + 34, ("+" if diff > 0 else "") + str(diff), size=10)

    return canvas


def color_for_merge_count(n: int):
    """COPY_COLOR for a plain copy (n <= 1); otherwise a step along
    MERGE_ACCENT_RAMP, clamped to its last entry once n exceeds the ramp's length."""
    if n <= 1:
        return hex_to_rgb(COPY_COLOR)
    return hex_to_rgb(MERGE_ACCENT_RAMP[min(n - 2, len(MERGE_ACCENT_RAMP) - 1)])


def build_merge_grid_png(stages, walks_per_row, display_width, stagger=0):
    """Row 0 has no previous row and is left blank (white). Every other row
    is mostly COPY_COLOR (a merge_count of 1 -- the overwhelming majority),
    with rare accent-colored cells wherever the new stage's filter actually
    merged two or more of the previous stage's gaps into one. Blank past the
    point the comparison window ran out of previous-row data to check. Rows
    are truncated to `display_width` regardless of how much underlying data
    exists -- see MAX_DISPLAY_WIDTH."""
    width = display_width + stagger * (len(stages) - 1)
    rows_rgb = []
    for row_idx, walk in enumerate(walks_per_row):
        offset = stagger * row_idx
        row = bytearray(b"\xff\xff\xff" * width)
        for i, (_diff, merge_count, _anchor_idx) in enumerate(walk[:display_width]):
            red, green, blue = color_for_merge_count(merge_count)
            pos = offset + i
            row[pos * 3:pos * 3 + 3] = bytes((red, green, blue))
        rows_rgb.append(bytes(row))
    return width, len(stages), rows_rgb


def build_merge_heatmap(stages, stagger=0, png_name="gap-heatmap-merges.png", title_suffix="", walks_per_row=None) -> Canvas:
    """Builds the merge-count heatmap: each cell colored by how many previous-stage
    gaps fed into it (see color_for_merge_count), mostly a copy (1) with rare merges.

    walks_per_row: see build_diff_heatmap."""
    prefix_len = len(stages[0]["gaps"])
    display_width = min(prefix_len, MAX_DISPLAY_WIDTH)
    walks_per_row = walks_per_row if walks_per_row is not None else (
        [[]] + [lineage_walk(stages[row - 1], stages[row]) for row in range(1, len(stages))]
    )
    max_merge = max((merge_count for walk in walks_per_row for _diff, merge_count, _anchor_idx in walk[:display_width]), default=1)

    grid_w_px, grid_h_px, rows_rgb = build_merge_grid_png(stages, walks_per_row, display_width, stagger=stagger)
    image_uri = render_grid_png(os.path.join(OUT_DIR, png_name), grid_w_px, grid_h_px, rows_rgb)

    cell_w_display, cell_h_display = heatmap_cell_size(display_width, len(stages))
    label_w = 90
    legend_h = 122
    top_margin = 50

    grid_w = grid_w_px * cell_w_display
    grid_h = len(stages) * cell_h_display
    canvas_w = heatmap_canvas_width(label_w, grid_w, max_merge)
    canvas_h = top_margin + grid_h + legend_h

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"Merge-count heatmap: how many old gaps fed each new one, {display_width} of {prefix_len} gaps x {len(stages)} stages{title_suffix}",
           size=16, weight="bold")

    canvas.image(label_w, top_margin, grid_w, grid_h, image_uri)
    canvas.rect(label_w, top_margin, grid_w, grid_h, fill="none", stroke="#ccc", width=1)

    draw_row_head_labels(canvas, stages, label_w, top_margin, cell_h_display)

    draw_boundary_curves(canvas, stages, label_w, top_margin, cell_w_display, cell_h_display, stagger, display_width,
                          legend_y=top_margin + grid_h + 20)

    legend_y = top_margin + grid_h + 62
    legend_x0 = label_w
    swatch_w = 26
    canvas.text(legend_x0, legend_y - 10,
           "old gaps merged into this one (1 = copied unchanged; white = ran out of data to check)",
           size=12, fill="#555", anchor="start")
    for n in range(1, max_merge + 1):
        x = legend_x0 + (n - 1) * (swatch_w + 4)
        red, green, blue = color_for_merge_count(n)
        canvas.rect(x, legend_y, swatch_w, 20, fill=f"rgb({red},{green},{blue})", stroke="#999", width=1)
        canvas.text(x + swatch_w / 2, legend_y + 34, str(n), size=10)

    return canvas


def known_prefix_len(ages):
    """How many leading positions of a row are real (non-None) data -- the
    point where age=None (unknown) first appears, or the full row length if
    it never does."""
    for i, age in enumerate(ages):
        if age is None:
            return i
    return len(ages)


def choose_age_width(ages_per_row, percentile=0):
    """Age is chained across every prior stage (see compute_ages_per_row), so
    once a row's lineage_walk runs out anywhere, every later row inherits
    that gap and the unknown region only grows going down the rows -- not a
    simple per-row shortfall like the 2-focused view, but the same fix
    applies: size the canvas to the amount of real data actually available
    (percentile=0 -- the worst row's known-prefix length -- guarantees zero
    white anywhere), and truncate the rest rather than padding it out."""
    lens = sorted(known_prefix_len(row) for row in ages_per_row)
    idx = min(len(lens) - 1, int(len(lens) * percentile / 100))
    return lens[idx]


def build_age_grid_png(stages, ages_per_row, color_by_age, width, stagger=0):
    """Rows are truncated to `width`; since every kept column is guaranteed
    real (non-None) data when width = choose_age_width(..., percentile=0),
    white padding should not occur here at all in practice."""
    full_width = width + stagger * (len(stages) - 1)
    rows_rgb = []
    for row_idx, ages in enumerate(ages_per_row):
        offset = stagger * row_idx
        row = bytearray(b"\xff\xff\xff" * full_width)
        for i, age in enumerate(ages[:width]):
            if age is None:
                continue
            red, green, blue = color_by_age[age]
            pos = offset + i
            row[pos * 3:pos * 3 + 3] = bytes((red, green, blue))
        rows_rgb.append(bytes(row))
    return full_width, len(stages), rows_rgb


def build_age_heatmap(stages, stagger=0, png_name="gap-heatmap-age.png", title_suffix="", ages_per_row=None) -> Canvas:
    """Builds the gap-age heatmap: each cell colored by how many consecutive
    stages its lineage survived without merging (see compute_ages_per_row).

    ages_per_row, if given, must be compute_ages_per_row(stages) -- pass this
    in when the caller already computed it (see main(), which shares one pass
    across this and build_age_2focused_heatmap) instead of recomputing the
    same full-data lineage walk again."""
    ages_per_row = ages_per_row if ages_per_row is not None else compute_ages_per_row(stages)
    target_width = min(choose_age_width(ages_per_row), MAX_DISPLAY_WIDTH)
    all_ages = calibration_values(ages_per_row, target_width)
    color_by_age = build_equalized_color_map(all_ages, ramp=AGE_RAMP)
    distinct_ages = sorted(color_by_age)
    legend_values = sample_for_legend(distinct_ages)

    grid_w_px, grid_h_px, rows_rgb = build_age_grid_png(stages, ages_per_row, color_by_age, target_width, stagger=stagger)
    image_uri = render_grid_png(os.path.join(OUT_DIR, png_name), grid_w_px, grid_h_px, rows_rgb)

    cell_w_display, cell_h_display = heatmap_cell_size(target_width, len(stages))
    label_w = 90
    legend_h = 122
    top_margin = 50

    grid_w = grid_w_px * cell_w_display
    grid_h = len(stages) * cell_h_display
    canvas_w = heatmap_canvas_width(label_w, grid_w, len(legend_values))
    canvas_h = top_margin + grid_h + legend_h

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"Gap age heatmap: consecutive stages survived without merging, {target_width} known gaps x {len(stages)} stages{title_suffix}",
           size=16, weight="bold")

    canvas.image(label_w, top_margin, grid_w, grid_h, image_uri)
    canvas.rect(label_w, top_margin, grid_w, grid_h, fill="none", stroke="#ccc", width=1)

    draw_row_head_labels(canvas, stages, label_w, top_margin, cell_h_display)

    draw_boundary_curves(canvas, stages, label_w, top_margin, cell_w_display, cell_h_display, stagger, target_width,
                          legend_y=top_margin + grid_h + 20)

    legend_y = top_margin + grid_h + 62
    legend_x0 = label_w
    swatch_w = 26
    canvas.text(legend_x0, legend_y - 10,
           "gap age: stages survived since last merge (1 = just merged/new; white = ran out of data to check)",
           size=12, fill="#555", anchor="start")
    for i, age in enumerate(legend_values):
        x = legend_x0 + i * (swatch_w + 4)
        red, green, blue = color_by_age[age]
        canvas.rect(x, legend_y, swatch_w, 20, fill=f"rgb({red},{green},{blue})", stroke="#999", width=1)
        canvas.text(x + swatch_w / 2, legend_y + 34, str(age), size=10)

    return canvas


def build_age_2focused_grid_png(stages, compressed_per_row, ages_2focused_per_row, color_by_age, width, stagger=0):
    """Rows are truncated to `width`. A standalone 2-gap always renders as
    TWO_GAP_COLOR (fixed, reserved -- same convention as
    build_compressed_grid_png), regardless of its own age; only runs
    (compressed value != 2) use the age color ramp. Without this split, a
    2-gap and a similarly-young run land at nearly the same ramp position
    and become visually indistinguishable, defeating the point of a combined
    view -- the whole point here is making the (rare, interesting) runs'
    age stand out, not diluting the ramp with the (common, expected) 2s."""
    full_width = width + stagger * (len(stages) - 1)
    two_gap_rgb = hex_to_rgb(TWO_GAP_COLOR)
    rows_rgb = []
    for row_idx, (compressed, ages) in enumerate(zip(compressed_per_row, ages_2focused_per_row)):
        offset = stagger * row_idx
        row = bytearray(b"\xff\xff\xff" * full_width)
        for i in range(min(width, len(compressed))):
            if compressed[i] == 2:
                rgb = two_gap_rgb
            else:
                age = ages[i]
                if age is None:
                    continue
                rgb = color_by_age[age]
            pos = offset + i
            row[pos * 3:pos * 3 + 3] = bytes(rgb)
        rows_rgb.append(bytes(row))
    return full_width, len(stages), rows_rgb


def build_age_2focused_heatmap(stages, stagger=0, png_name="gap-heatmap-2focused-age.png", title_suffix="", ages_per_row=None) -> Canvas:
    """Combines the other two views: x-axis is 2-focused compression (every
    2-gap its own unit, runs between consecutive 2-gaps collapsed into one).
    2-gaps render in a fixed reserved color (TWO_GAP_COLOR); only runs are
    colored by age -- not of the compressed unit itself (a summed run isn't
    a single gap with one lineage), but of the raw gap that CLOSES it
    (compress_around_two_with_anchor's anchor index), the same closing
    boundary compute_ages_per_row's lineage_walk already anchors merge/copy
    status on for the next stage.

    ages_per_row: see build_age_heatmap."""
    ages_per_row = ages_per_row if ages_per_row is not None else compute_ages_per_row(stages)
    compressed_per_row = []
    ages_2focused_per_row = []
    for row, stage in enumerate(stages):
        compressed, anchors = compress_around_two_with_anchor(stage["gaps"])
        row_ages = ages_per_row[row]
        ages_2focused = [row_ages[anchor_idx] if anchor_idx < len(row_ages) else None for anchor_idx in anchors]
        compressed_per_row.append(compressed)
        ages_2focused_per_row.append(ages_2focused)

    target_width = min(choose_age_width(ages_2focused_per_row), MAX_DISPLAY_WIDTH)
    # Ramp is calibrated on run ages only -- 2-gaps don't use it at all, so
    # including their (numerous) ages here would just waste ramp resolution.
    all_ages = run_ages_for_calibration(compressed_per_row, ages_2focused_per_row, target_width)
    color_by_age = build_equalized_color_map(all_ages, ramp=AGE_RAMP)
    distinct_ages = sorted(color_by_age)
    legend_values = sample_for_legend(distinct_ages)

    grid_w_px, grid_h_px, rows_rgb = build_age_2focused_grid_png(
        stages, compressed_per_row, ages_2focused_per_row, color_by_age, target_width, stagger=stagger)
    image_uri = render_grid_png(os.path.join(OUT_DIR, png_name), grid_w_px, grid_h_px, rows_rgb)

    cell_w_display, cell_h_display = heatmap_cell_size(target_width, len(stages))
    label_w = 90
    # No boundary-curve caption in this view (unlike build_age_heatmap) --
    # this view's x-axis is 2-focused compression, not raw gap index, so the
    # boundary curves' indices wouldn't line up with it. Same legend_h as
    # build_compressed_heatmap, its true sibling on that x-axis.
    legend_h = 90
    top_margin = 50

    grid_w = grid_w_px * cell_w_display
    grid_h = len(stages) * cell_h_display
    # +1 legend slot: the fixed "2" swatch drawn before the loop occupies one
    # slot of its own (see the loop's (i + 1) offset below).
    canvas_w = heatmap_canvas_width(label_w, grid_w, len(legend_values) + 1)
    canvas_h = top_margin + grid_h + legend_h

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"2-focused age heatmap: age of the gap anchoring each compressed unit, "
           f"{target_width} units x {len(stages)} stages{title_suffix}",
           size=16, weight="bold")

    canvas.image(label_w, top_margin, grid_w, grid_h, image_uri)
    canvas.rect(label_w, top_margin, grid_w, grid_h, fill="none", stroke="#ccc", width=1)

    draw_row_head_labels(canvas, stages, label_w, top_margin, cell_h_display)

    legend_y = top_margin + grid_h + 30
    legend_x0 = label_w
    swatch_w = 26
    canvas.text(legend_x0, legend_y - 10,
           "x-axis: 2-focused compression (2-gaps standalone, runs between them collapsed); "
           "green = a 2-gap (fixed color, age not shown); ramp = a run's closing gap's age (1 = just merged/new)",
           size=12, fill="#555", anchor="start")
    canvas.rect(legend_x0, legend_y, swatch_w, 20, fill=TWO_GAP_COLOR, stroke="#999", width=1)
    canvas.text(legend_x0 + swatch_w / 2, legend_y + 34, "2", size=10)
    for i, age in enumerate(legend_values):
        x = legend_x0 + (i + 1) * (swatch_w + 4)
        red, green, blue = color_by_age[age]
        canvas.rect(x, legend_y, swatch_w, 20, fill=f"rgb({red},{green},{blue})", stroke="#999", width=1)
        canvas.text(x + swatch_w / 2, legend_y + 34, str(age), size=10)

    return canvas


def draw_line_chart_frame(canvas, left, top, plot_w, plot_h, y_max, n_gridlines, y_fmt=str):
    """Recessive horizontal gridlines + a y-axis label at each, plus the
    x-axis baseline -- the shared scaffolding both line charts below draw
    their series on top of."""
    for i in range(n_gridlines + 1):
        frac_y = i / n_gridlines
        y = top + plot_h - frac_y * plot_h
        canvas.line(left, y, left + plot_w, y, stroke="#e1e0d9", width=1)
        canvas.text(left - 10, y + 4, y_fmt(frac_y * y_max), size=10, anchor="end", fill="#898781")
    canvas.line(left, top + plot_h, left + plot_w, top + plot_h, stroke="#c3c2b7", width=1)


def draw_line_series(canvas, stages, values, left, top, plot_w, plot_h, y_max, color, width=2):
    """Draws one polyline series across the plot area, one point per stage,
    x evenly spaced and y clamped to y_max."""
    n = len(stages)
    points = []
    for i, value in enumerate(values):
        x = left + (i / (n - 1)) * plot_w if n > 1 else left
        y = top + plot_h - min(value, y_max) / y_max * plot_h
        points.append((x, y))
    canvas.polyline(points, stroke=color, width=width)


def draw_x_axis_labels(canvas, stages, left, top, plot_w, plot_h, label_every=None):
    """Draws sparse x-axis "h=<head>" labels below the plot area, roughly
    every label_every-th stage (default: about 12 across the whole width),
    always including the last stage."""
    n = len(stages)
    label_every = label_every or max(1, n // 12)
    for i, stage in enumerate(stages):
        if i % label_every == 0 or i == n - 1:
            x = left + (i / (n - 1)) * plot_w if n > 1 else left
            canvas.text(x, top + plot_h + 18, f"h={stage['head']}", size=9, anchor="middle", fill="#555")


def build_two_gap_frequency_chart(stages) -> Canvas:
    """Answers one half of "why does the 2-focused age view look like solid
    green with occasional colored streaks": what fraction of a stage's own
    gaps are exactly 2 (i.e. render green in that view) vs everything else.
    A single series -- per the dataviz convention, needs no legend box, the
    title names it. Declines from 100% (stage 1, head=3, every gap is a
    2 -- consecutive odd numbers) toward roughly 10% by head~1200, computed
    directly from this dataset's own prefix, not a theoretical asymptote."""
    frac = [sum(1 for gap in stage["gaps"] if gap == 2) / len(stage["gaps"]) for stage in stages]

    canvas_w, canvas_h = 1100, 480
    left, right, top, bottom = 70, 30, 60, 60
    plot_w, plot_h = canvas_w - left - right, canvas_h - top - bottom

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"2-gap frequency: fraction of gaps equal to 2, per stage ({len(stages)} stages)",
           size=16, weight="bold")

    draw_line_chart_frame(canvas, left, top, plot_w, plot_h, y_max=1.0, n_gridlines=5,
                           y_fmt=lambda value: f"{round(value * 100)}%")
    draw_line_series(canvas, stages, frac, left, top, plot_w, plot_h, y_max=1.0, color=LINE_COLOR_PRIMARY)
    draw_x_axis_labels(canvas, stages, left, top, plot_w, plot_h)

    return canvas


def build_two_gap_run_size_chart(stages) -> Canvas:
    """The other half of the story: when consecutive 2-gaps aren't adjacent
    (a "run" in the 2-focused view -- see compress_around_two), how far
    apart are they? This is the SUM of the non-2 gaps between one 2-gap and
    the next, not each individual non-2 gap on its own -- a run of e.g.
    [4, 6] between two 2-gaps is one distance of 10, not two separate values
    4 and 6. Using compress_around_two (the same function the 2-focused
    heatmap itself uses) instead of a plain per-gap filter is what makes this
    the right statistic: an earlier version of this chart filtered individual
    gaps directly, silently reporting "average non-2 gap size" instead of
    "average distance between consecutive 2-gaps" -- numerically very
    different once runs start spanning more than one raw gap (which becomes
    common quickly: by head=17, most runs already combine multiple gaps).

    Two series sharing one y-axis (same unit, gap-distance -- never split
    into dual axes for this): the average run distance and the max run
    distance. The average grows steadily (4 -> 100+); the max grows much
    faster still (4 -> 1000+), diverging further from the average as head
    increases. The average's floor is always exactly 4, never lower: once
    the filter includes 3 (stage 2 onward), three consecutive survivors
    spaced 2 apart is impossible (they would cover all three residues mod 3,
    so one is always a multiple of 3) -- the smallest possible non-2 gap,
    and therefore the smallest possible run, is thus 4, the classic
    prime-quadruplet spacing [2,4,2]."""
    avg_run, max_run = [], []
    for stage in stages:
        runs = [value for value in compress_around_two(stage["gaps"]) if value != 2]
        avg_run.append(sum(runs) / len(runs) if runs else 0)
        max_run.append(max(runs) if runs else 0)

    canvas_w, canvas_h = 1100, 480
    left, right, top, bottom = 70, 30, 60, 90
    plot_w, plot_h = canvas_w - left - right, canvas_h - top - bottom
    y_max = max(max_run) * 1.05 if max(max_run) > 0 else 1

    canvas = Canvas(canvas_w, canvas_h)
    canvas.text(canvas_w / 2, 28,
           f"2-gap cluster size: typical (avg) and largest (max) distance between consecutive "
           f"2-gaps, per stage ({len(stages)} stages)",
           size=16, weight="bold")

    draw_line_chart_frame(canvas, left, top, plot_w, plot_h, y_max=y_max, n_gridlines=5,
                           y_fmt=lambda value: str(round(value)))
    draw_line_series(canvas, stages, max_run, left, top, plot_w, plot_h, y_max, color=LINE_COLOR_SECONDARY)
    draw_line_series(canvas, stages, avg_run, left, top, plot_w, plot_h, y_max, color=LINE_COLOR_PRIMARY)
    draw_x_axis_labels(canvas, stages, left, top, plot_w, plot_h)

    legend_y = top + plot_h + 40
    legend_x0 = left
    swatch = 16
    canvas.rect(legend_x0, legend_y, swatch, 3, fill=LINE_COLOR_PRIMARY, stroke="none", width=0)
    canvas.text(legend_x0 + swatch + 8, legend_y + 5, "average run value", size=11, anchor="start", fill="#555")
    canvas.rect(legend_x0 + 200, legend_y, swatch, 3, fill=LINE_COLOR_SECONDARY, stroke="none", width=0)
    canvas.text(legend_x0 + 200 + swatch + 8, legend_y + 5, "max run value", size=11, anchor="start", fill="#555")

    return canvas


def main() -> None:
    """Loads the generated stages and writes every heatmap and line-chart
    figure this module produces to OUT_DIR."""
    if not os.path.exists(CSV_PATH):
        raise SystemExit(f"{CSV_PATH} not found -- run generate_gaps.py first")
    os.makedirs(OUT_DIR, exist_ok=True)
    stages = load_stages()
    if not stages:
        raise SystemExit(
            f"{CSV_PATH} exists but has no stage rows -- generate_gaps.py may have "
            "been interrupted before finishing its first stage; rerun it"
        )

    # Computed once and shared across every consumer below instead of each
    # independently re-walking the same O(stages x prefix_len) lineage.
    walks_per_row = [[]] + [lineage_walk(stages[row - 1], stages[row]) for row in range(1, len(stages))]
    ages_per_row = compute_ages_per_row(stages, walks_per_row=walks_per_row)

    canvas = build_heatmap(stages)
    path = os.path.join(OUT_DIR, "gap-heatmap.svg")
    save(canvas, path)
    print(f"wrote {path}")

    staggered = build_heatmap(
        stages, stagger=1, png_name="gap-heatmap-staggered.png",
        title_suffix=" (each row shifted 1px right -- display-only, breaks up the diagonals)",
    )
    staggered_path = os.path.join(OUT_DIR, "gap-heatmap-staggered.svg")
    save(staggered, staggered_path)
    print(f"wrote {staggered_path}")

    diff_canvas = build_diff_heatmap(stages, walks_per_row=walks_per_row)
    diff_path = os.path.join(OUT_DIR, "gap-heatmap-diff.svg")
    save(diff_canvas, diff_path)
    print(f"wrote {diff_path}")

    diff_staggered = build_diff_heatmap(
        stages, stagger=1, png_name="gap-heatmap-diff-staggered.png",
        title_suffix=" (each row shifted 1px right)", walks_per_row=walks_per_row,
    )
    diff_staggered_path = os.path.join(OUT_DIR, "gap-heatmap-diff-staggered.svg")
    save(diff_staggered, diff_staggered_path)
    print(f"wrote {diff_staggered_path}")

    simple_diff_canvas = build_simple_shift_diff_heatmap(stages)
    simple_diff_path = os.path.join(OUT_DIR, "gap-heatmap-diff-simple-shift.svg")
    save(simple_diff_canvas, simple_diff_path)
    print(f"wrote {simple_diff_path}")

    merge_canvas = build_merge_heatmap(stages, walks_per_row=walks_per_row)
    merge_path = os.path.join(OUT_DIR, "gap-heatmap-merges.svg")
    save(merge_canvas, merge_path)
    print(f"wrote {merge_path}")

    age_canvas = build_age_heatmap(stages, ages_per_row=ages_per_row)
    age_path = os.path.join(OUT_DIR, "gap-heatmap-age.svg")
    save(age_canvas, age_path)
    print(f"wrote {age_path}")

    age_staggered = build_age_heatmap(
        stages, stagger=1, png_name="gap-heatmap-age-staggered.png",
        title_suffix=" (each row shifted 1px right)", ages_per_row=ages_per_row,
    )
    age_staggered_path = os.path.join(OUT_DIR, "gap-heatmap-age-staggered.svg")
    save(age_staggered, age_staggered_path)
    print(f"wrote {age_staggered_path}")

    compressed_canvas = build_compressed_heatmap(stages)
    compressed_path = os.path.join(OUT_DIR, "gap-heatmap-2focused.svg")
    save(compressed_canvas, compressed_path)
    print(f"wrote {compressed_path}")

    compressed_staggered = build_compressed_heatmap(
        stages, stagger=1, png_name="gap-heatmap-2focused-staggered.png",
        title_suffix=" (each row shifted 1px right)",
    )
    compressed_staggered_path = os.path.join(OUT_DIR, "gap-heatmap-2focused-staggered.svg")
    save(compressed_staggered, compressed_staggered_path)
    print(f"wrote {compressed_staggered_path}")

    age_2focused_canvas = build_age_2focused_heatmap(stages, ages_per_row=ages_per_row)
    age_2focused_path = os.path.join(OUT_DIR, "gap-heatmap-2focused-age.svg")
    save(age_2focused_canvas, age_2focused_path)
    print(f"wrote {age_2focused_path}")

    age_2focused_staggered = build_age_2focused_heatmap(
        stages, stagger=1, png_name="gap-heatmap-2focused-age-staggered.png",
        title_suffix=" (each row shifted 1px right)", ages_per_row=ages_per_row,
    )
    age_2focused_staggered_path = os.path.join(OUT_DIR, "gap-heatmap-2focused-age-staggered.svg")
    save(age_2focused_staggered, age_2focused_staggered_path)
    print(f"wrote {age_2focused_staggered_path}")

    freq_canvas = build_two_gap_frequency_chart(stages)
    freq_path = os.path.join(OUT_DIR, "gap-two-frequency.svg")
    save(freq_canvas, freq_path)
    print(f"wrote {freq_path}")

    run_size_canvas = build_two_gap_run_size_chart(stages)
    run_size_path = os.path.join(OUT_DIR, "gap-two-cluster-size.svg")
    save(run_size_canvas, run_size_path)
    print(f"wrote {run_size_path}")


if __name__ == "__main__":
    main()
