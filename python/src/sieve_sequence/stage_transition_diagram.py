"""Gaps -> generated numbers -> repeat -> rotate -> candidate values -> filter
-> gaps -> generated numbers: how stage k's proven periodic gap cycle turns
into stage k+1's, as eight literal steps that start and end on the same kind
of object (a gap cycle, then its generated sequence), closing the loop --
stage k+1's own output gaps and numbers are exactly what a *next* transition
would start from as its own steps 1-2. Renders TRANSITIONS (by default, both
stage 0->1 and stage 1->2) stacked as independent, fully-labeled blocks in
one figure.

Every step shows exactly what its own operation produces and nothing more --
no step is padded with extra repeats "for visual clarity." Two kinds of row
are deliberately NOT bounded, though, and are marked with a trailing "..."
rather than silently stopping: "Generated numbers" (steps 2 and 8) are
genuine, infinite members of a stage's actual sequence -- the periodic gap
cycle that produced them repeats forever, so the window shown is only ever a
prefix, never the whole thing. "Candidate values" (step 5) are deliberately
NOT called "numbers": they're unfiltered, some are about to be dropped in
step 6, so they aren't yet confirmed members of anything.

Rotate (step 4) is the key move that avoids a separate reframing step later:
`head_after` is always exactly one gap-step past `head_before` (it's
literally the next term in stage k's own sequence), so the first element of
`repeat_unit` -- the gap already spent getting from head_before to
head_after -- can be dropped to the back of the list. Walking that rotated
list forward from head_after (step 5) is then already correctly framed from
the start; no extra "reframe from the new head" step is needed afterward,
the way an earlier version of this diagram did it. For a period-1 base unit
(this file's stage 0->1 and stage 1->2 examples) the rotation is invisible
-- [2,2,2] rotated is still [2,2,2] -- since a constant list is unchanged by
any cyclic shift; for a longer period (e.g. stage 2->3's [2,4,2,4,...]) the
same operation visibly reorders the list.

1. Gaps               -- stage k's own minimal periodic gap cycle
   (generate_gaps.py's compute_full_period -- the ground truth, e.g. [2] for
   stage 1, [1] for stage 0), shown at its true length, not padded.
2. Generated numbers   -- walking that cycle forward from stage k's head
   expands it back into concrete, genuine survivors (e.g. 3,5,7,...) --
   infinite, so the row ends in "..." rather than stopping arbitrarily.
3. Repeat              -- the same gap cycle tiled exactly `new_prime` times
   (stage k's own head, the prime stage k+1 newly excludes) -- a bounded
   operation that spans exactly one new modulus, no more.
4. Rotate              -- shift that tiled list left by exactly one position,
   so it's ready to be walked from stage k+1's own head directly (see above).
5. Candidate values    -- walking the rotated list forward from stage k+1's
   own head (included as the first entry, same convention as steps 2/8)
   turns it into concrete numbers -- candidates only, not yet confirmed.
6. Filter              -- the one real structural change: candidates
   divisible by `new_prime` are struck through and dropped; everything else
   (including the head itself, which can never be a multiple of it) survives
   untouched.
7. Gaps                -- stage k+1's own minimal periodic gap cycle,
   computed the same rigorous way as step 1 -- and because step 5 already
   walked from the correctly-rotated, correctly-anchored starting point,
   this always matches what filtering the kept survivors above would give,
   exactly, not just a partial prefix of it.
8. Generated numbers   -- walking stage k+1's own new cycle forward from its
   own head, the same way step 2 did for stage k -- the new sequence's
   genuine, infinite members; also ends in "...".

TRANSITIONS lists which stage_before values to render, each as its own
independent, fully-labeled 8-step block, stacked top to bottom. Default:
[1, 2] -- stage 1 (head=3, gap cycle [2]) becoming stage 2 (head=5, gap
cycle [2,4]), then stage 2 becoming stage 3 (head=7). The second block is
the first one where Rotate is visibly non-trivial: base unit [2,4] has
period 2, so shifting it left by 1 actually reorders the list
([2,4,2,4,...] -> [4,2,4,2,...]), unlike period-1 base units where rotation
is invisible.

Run: python3 stage_transition_diagram.py
Output: ./out/stage-transition-repeat-filter-rotate.svg
"""

import datetime
import os
import subprocess
import sys
import textwrap

from .generate_gaps import compute_full_period, first_k_primes
from .svg_kit import Canvas, save

OUT_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "charts")

TRANSITIONS = [1, 2]  # stage_before values to render, each its own 8-step block
NUMBERS_SAMPLES = 5  # how many chips steps 2 and 8's illustrative windows show before the trailing "..."

# Status colors (references/palette.md): green = kept ("good"), red = removed
# ("critical"). Blue (categorical slot 1) is the neutral "just a number, not
# yet judged" color used for numbers before filtering exists at all (steps
# 2, 5, 8). Orange (categorical slot 8, also AGE_RAMP's low end in
# gap_heatmap.py) marks "this row's content IS a gap cycle" in the steps
# where gaps are the main subject (1, 3, 4, 7), not just an annotation
# beside a number chip.
NUMBER_COLOR = "#2a78d6"
GAP_EMPHASIS_COLOR = "#eb6834"
KEPT_COLOR = "#0ca30c"
REMOVED_COLOR = "#d03b3b"
GAP_PILL_FILL = "#f3f1ea"
GAP_PILL_TEXT = "#52514e"

CHIP_W = 54
CHIP_H = 42
CHIP_GAP = 40
GAP_PILL_W = 34
GAP_PILL_H = 22
LABEL_W = 250
LABEL_WRAP_CHARS = 34
STEP_H = 118
BLOCK_HEADING_H = 34
BLOCK_GUTTER = 26


def build_transition(stage_before):
    """The head/tail/modulus facts describing the transition from stage
    `stage_before` to stage `stage_before + 1`."""
    if stage_before == 0:
        tail_before, head_before, head_after = [], 2, 3
    else:
        heads = first_k_primes(stage_before + 2)[1:]  # skip 2; numbering starts at head=3
        tail_before = [2] + heads[:stage_before - 1]
        head_before = heads[stage_before - 1]
        head_after = heads[stage_before]
    new_prime = head_before
    modulus_before = 1
    for p in tail_before:
        modulus_before *= p
    modulus_after = modulus_before * new_prime
    tail_after = tail_before + [new_prime]
    return {
        "stage_before": stage_before,
        "tail_before": tail_before, "tail_after": tail_after,
        "head_before": head_before, "head_after": head_after,
        "new_prime": new_prime, "modulus_before": modulus_before, "modulus_after": modulus_after,
    }


def generate_numbers_window(head, base_unit, count):
    """Walks the (infinite, proven-periodic) gap cycle forward from `head`
    for `count` chips -- a prefix of the true, unending sequence, not the
    whole thing (see draw_interleaved_row's trailing-"..." support)."""
    period_len = len(base_unit)
    numbers = [head]
    running = head
    for i in range(count - 1):
        running += base_unit[i % period_len]
        numbers.append(running)
    gaps = [numbers[i + 1] - numbers[i] for i in range(len(numbers) - 1)]
    return numbers, gaps


def compute_steps(transition):
    """Derives every intermediate value the 8-step diagram draws (steps 1-8's
    gap cycles, generated numbers, repeat/rotate/filter results) from `transition`."""
    tail_before, tail_after = transition["tail_before"], transition["tail_after"]
    head_before, head_after = transition["head_before"], transition["head_after"]
    new_prime = transition["new_prime"]

    base_unit = compute_full_period(head_before, tail_before)
    numbers1, gaps1 = generate_numbers_window(head_before, base_unit, NUMBERS_SAMPLES)

    # Exactly one new-modulus span -- new_prime copies of base_unit, no more.
    repeat_unit = base_unit * new_prime

    # head_after is always exactly one base_unit-step past head_before (it's
    # literally the next survivor of stage k's own sequence), so shifting the
    # tape left by 1 always realigns it to start counting from head_after
    # instead of head_before -- no separate reframing step needed once you
    # walk from here.
    rotated_unit = repeat_unit[1:] + repeat_unit[:1]

    values = [head_after]
    running = head_after
    for gap in rotated_unit:
        running += gap
        values.append(running)
    value_gaps = [values[i + 1] - values[i] for i in range(len(values) - 1)]

    kept = [value for value in values if value % new_prime != 0]
    kept_gaps = [kept[i + 1] - kept[i] for i in range(len(kept) - 1)]

    new_base_unit = compute_full_period(head_after, tail_after)
    new_numbers, new_gaps = generate_numbers_window(head_after, new_base_unit, NUMBERS_SAMPLES)

    return {
        "base_unit": base_unit, "numbers1": numbers1, "gaps1": gaps1,
        "repeat_unit": repeat_unit, "rotated_unit": rotated_unit,
        "values": values, "value_gaps": value_gaps,
        "kept": kept, "kept_gaps": kept_gaps, "new_base_unit": new_base_unit,
        "new_numbers": new_numbers, "new_gaps": new_gaps,
    }


def draw_chip(canvas, x, y, label, fill, w=CHIP_W, h=CHIP_H, text_size=17,
              rx=8, text_color="#ffffff", strike=False):
    """A single rounded-rect number/gap chip at (x, y), optionally struck
    through (for candidates the filter rejects)."""
    canvas.rect(x, y, w, h, fill=fill, stroke="none", width=0, rx=rx)
    canvas.text(x + w / 2, y + h / 2 + text_size * 0.32, str(label), size=text_size,
            weight="bold", fill=text_color)
    if strike:
        canvas.line(x + w * 0.12, y + h * 0.18, x + w * 0.88, y + h * 0.82, stroke="#5c1414", width=2.5)
        canvas.line(x + w * 0.12, y + h * 0.82, x + w * 0.88, y + h * 0.18, stroke="#5c1414", width=2.5)


def draw_gap_pill(canvas, x, y, value, fill=GAP_PILL_FILL, text_color=GAP_PILL_TEXT):
    """A small pill-shaped chip annotating a gap (drawn as "+value")."""
    draw_chip(canvas, x, y, f"+{value}", fill, w=GAP_PILL_W, h=GAP_PILL_H,
              text_size=10, rx=GAP_PILL_H / 2, text_color=text_color)


def row_width(n_chips, w=CHIP_W, gap=CHIP_GAP):
    """Total pixel width of a row of n_chips chips of width w, separated by gap."""
    return n_chips * w + max(0, n_chips - 1) * gap


def draw_interleaved_row(canvas, x0, y, numbers, gaps, colors, strikes=None, ellipsis=False):
    """Alternates number chips and small gap pills on the connecting
    segment between them, so each gap is drawn directly beside the two
    numbers it was computed from -- the literal "numbers next to their
    gaps" pairing, not a separate abstract list. `ellipsis=True` appends a
    trailing "..." after the last chip, for rows that are a prefix of a
    genuinely infinite sequence rather than the row's complete content."""
    pill_y = y + (CHIP_H - GAP_PILL_H) / 2
    x = x0
    for i, number in enumerate(numbers):
        color = colors[i] if isinstance(colors, list) else colors
        strike = strikes[i] if strikes else False
        draw_chip(canvas, x, y, number, color, strike=strike)
        x += CHIP_W
        if i < len(numbers) - 1:
            canvas.line(x, y + CHIP_H / 2, x + CHIP_GAP, y + CHIP_H / 2, stroke="#ccc", width=1.5)
            pill_x = x + (CHIP_GAP - GAP_PILL_W) / 2
            draw_gap_pill(canvas, pill_x, pill_y, gaps[i])
            x += CHIP_GAP
    if ellipsis:
        canvas.text(x + 14, y + CHIP_H / 2 + 7, "...", size=22, weight="bold", fill="#999", anchor="start")


def draw_gap_value_row(canvas, x0, y, gaps):
    """The gap cycle itself as the row's primary content (steps 1, 3, 4, 7)
    -- bigger emphasis-colored chips, not small annotation pills."""
    w = CHIP_W - 10
    conn_gap = 22
    x = x0
    for i, gap in enumerate(gaps):
        draw_chip(canvas, x, y, gap, GAP_EMPHASIS_COLOR, w=w, text_size=15)
        x += w
        if i < len(gaps) - 1:
            canvas.line(x, y + CHIP_H / 2, x + conn_gap, y + CHIP_H / 2, stroke="#ccc", width=1.5)
            x += conn_gap


def draw_block(canvas, x0, y0, transition, steps) -> float:
    """Draws one transition's full 8-step pipeline starting at y0. Returns
    the y position immediately below the block (before any inter-block
    gutter is added)."""
    head_before, head_after, new_prime = transition["head_before"], transition["head_after"], transition["new_prime"]
    modulus_before, modulus_after = transition["modulus_before"], transition["modulus_after"]
    base_unit, new_base_unit = steps["base_unit"], steps["new_base_unit"]
    stage_before = transition["stage_before"]

    canvas.text(x0, y0 + 16, f"Stage {stage_before} (head={head_before}) becoming stage {stage_before + 1} (head={head_after})",
           size=15, weight="bold", anchor="start")
    y = y0 + BLOCK_HEADING_H

    def step_label(title, desc):
        """Draws a bold step title at the current y, with desc word-wrapped below it."""
        canvas.text(x0, y + 8, title, size=14, weight="bold", anchor="start")
        lines = textwrap.wrap(desc, width=LABEL_WRAP_CHARS)
        for i, line in enumerate(lines[:4]):
            canvas.text(x0, y + 26 + i * 13, line, size=10, fill="#555", anchor="start")

    x1 = x0 + LABEL_W

    # Step 1: Gaps
    step_label("1. Gaps", f"stage {stage_before}'s own minimal proven periodic gap cycle (period {len(base_unit)})")
    draw_gap_value_row(canvas, x1, y, base_unit)
    y += STEP_H

    # Step 2: Generated numbers
    step_label("2. Generated numbers",
                f"walking that cycle forward from head={head_before} -- genuine, infinite sequence members")
    draw_interleaved_row(canvas, x1, y, steps["numbers1"], steps["gaps1"], NUMBER_COLOR, ellipsis=True)
    y += STEP_H

    # Step 3: Repeat
    step_label("3. Repeat",
                f"cycle repeated exactly ×{new_prime} (stage {stage_before}'s head) -- spans exactly one "
                f"new modulus ({modulus_before}×{new_prime}={modulus_after}), no more")
    draw_gap_value_row(canvas, x1, y, steps["repeat_unit"])
    y += STEP_H

    # Step 4: Rotate
    step_label("4. Rotate",
                f"shift left by 1 -- head={head_after} is always one step past head={head_before}, "
                f"already anchored, no reframe needed")
    draw_gap_value_row(canvas, x1, y, steps["rotated_unit"])
    y += STEP_H

    # Step 5: Candidate values
    step_label("5. Candidate values",
                f"walk the rotated list forward from stage {stage_before + 1}'s own head ({head_after}) "
                f"-- unfiltered, not yet confirmed")
    draw_interleaved_row(canvas, x1, y, steps["values"], steps["value_gaps"], NUMBER_COLOR)
    y += STEP_H

    # Step 6: Filter
    step_label("6. Filter", f"drop candidates divisible by {new_prime} (stage {stage_before}'s own head)")
    colors = [KEPT_COLOR if value % new_prime != 0 else REMOVED_COLOR for value in steps["values"]]
    strikes = [value % new_prime == 0 for value in steps["values"]]
    draw_interleaved_row(canvas, x1, y, steps["values"], steps["value_gaps"], colors, strikes=strikes)
    y += STEP_H

    # Step 7: Gaps (closes the loop)
    step_label("7. Gaps",
                f"stage {stage_before + 1}'s TRUE periodic gap cycle (period {len(new_base_unit)}) -- "
                f"exactly what filtering the kept survivors above already gives")
    draw_gap_value_row(canvas, x1, y, new_base_unit)
    y += STEP_H

    # Step 8: Generated numbers (the new sequence, mirrors step 2)
    step_label("8. Generated numbers",
                f"walking stage {stage_before + 1}'s own new cycle forward from head={head_after} -- the new "
                f"sequence's genuine, infinite members")
    draw_interleaved_row(canvas, x1, y, steps["new_numbers"], steps["new_gaps"], NUMBER_COLOR, ellipsis=True)
    y += STEP_H

    return y


def build_diagram(blocks) -> Canvas:
    """`blocks` is a list of (transition, steps) pairs, one per transition,
    rendered stacked top to bottom, each as its own independent,
    fully-labeled 8-step pipeline."""
    title = "Gaps -> generated numbers -> repeat -> rotate -> candidate values -> filter -> gaps -> generated numbers"

    max_chips = max(
        max(len(steps["numbers1"]), len(steps["repeat_unit"]), len(steps["rotated_unit"]),
            len(steps["values"]), len(steps["new_numbers"]))
        for _, steps in blocks
    )
    content_w = row_width(max_chips) + 80  # extra room for the trailing "..." on infinite rows
    side_margin = 30
    title_w = len(title) * 8  # rough bold-15px-Helvetica estimate, wide enough to avoid clipping
    canvas_w = max(side_margin * 2 + LABEL_W + content_w, title_w + side_margin * 2)

    top_margin = 56
    block_h = BLOCK_HEADING_H + STEP_H * 8
    canvas_h = top_margin + len(blocks) * block_h + (len(blocks) - 1) * BLOCK_GUTTER + 20

    canvas = Canvas(canvas_w, canvas_h)

    canvas.comment(f"Generated: {datetime.datetime.now().isoformat()}")
    canvas.comment(f"Script: {os.path.basename(__file__)}")
    canvas.comment(f"Python: {sys.version}")
    canvas.comment(f"Source: Computed via generate_gaps.compute_full_period (no external data)")
    try:
        commit = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], text=True).strip()
        canvas.comment(f"Git commit: {commit}")
    except Exception:
        canvas.comment("Git commit: unknown")

    canvas.text(canvas_w / 2, 26, title, size=15, weight="bold")

    y = top_margin
    for transition, steps in blocks:
        y = draw_block(canvas, side_margin, y, transition, steps)
        y += BLOCK_GUTTER

    return canvas


def main() -> None:
    """Builds every transition in TRANSITIONS and writes the stacked diagram to OUT_DIR."""
    os.makedirs(OUT_DIR, exist_ok=True)
    blocks = []
    for stage_before in TRANSITIONS:
        transition = build_transition(stage_before)
        steps = compute_steps(transition)
        blocks.append((transition, steps))
    canvas = build_diagram(blocks)
    path = os.path.join(OUT_DIR, "stage-transition-repeat-filter-rotate.svg")
    save(canvas, path)
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
