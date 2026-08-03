# Sieve Sequence Gap Heatmaps

Static figures showing how gaps between sieve-sequence survivors evolve
across stages, built from real generated data (not illustrative numbers).
See `../06-article-diagram-ideas.md` for the original figure proposals this
grew out of, and
[`properties/sieve-sequence/safe-zone-exhaustion-curve.md`](../../../properties/sieve-sequence/safe-zone-exhaustion-curve.md)
for the math behind the boundary curves drawn on several of these charts.

Three independent pieces live here, split by how much data they need:

1. **`gap_heatmap.py`** -- the full-dataset heatmaps and line charts, reading
   the large generated (gitignored) CSV. Everything in "Pipeline" and most of
   "Output Files" below is this.
2. **`hit_miss_heatmap.py`** -- a small, committed-data figure (see
   "Small public-sample figures" below).
3. **`stage_transition_diagram.py`** -- a pure-computation figure with no data
   dependency at all (see the same section).

## Pipeline

Three scripts, run in this order:

```
python3 generate_gaps.py   # writes ../../../data/sieve-sequence/first_gaps_per_seq.csv (the only persisted data)
python3 gap_heatmap.py     # reads data/sieve-sequence/first_gaps_per_seq.csv, writes all out/gap-heatmap*.svg + .png
python3 verify.py          # re-checks every proven claim against data/sieve-sequence/first_gaps_per_seq.csv
```

**`data/sieve-sequence/first_gaps_per_seq.csv` is not committed** (see `.gitignore`) -- at
current settings it's several hundred MB, well past what's reasonable to
check in. Run `generate_gaps.py` to produce it locally; everything else in
the pipeline reads from that file, not from anything committed.

A small, committed sample of the same data --
[`data/sieve-sequence/first_gaps_per_seq.sample.csv`](../../../data/sieve-sequence/first_gaps_per_seq.sample.csv)
(100 stages x 100 gaps each, ~190KB) -- exists separately for figures that
don't need the full dataset; see "Small public-sample figures" below.

`generate_gaps.py` is resumable: it can be killed at any point (mid-row, even
mid-write) and rerunning picks up exactly where it left off, by re-deriving
its resume point from the last complete line of `first_gaps_per_seq.csv`
itself -- no
separate progress file. Deleting `data/sieve-sequence/first_gaps_per_seq.csv` and rerunning
starts fresh.

Current parameters (top of `generate_gaps.py`): `NUM_STAGES = 200`,
`PREFIX_LEN = 100000` -- 200 sieve stages (heads = the 2nd through 201st
primes), the first 100,000 gaps of each (takes roughly 4-5 minutes; expect a
similarly long run for `gap_heatmap.py`, since several views recompute
lineage across the full dataset). Full periods are not an option for most
stages: periods grow primorial-style (each stage multiplies by roughly its
own head), and the project's earlier Spark-based full-period pipeline already
reached 3GB by stage 10. Sampling a fixed-length prefix instead keeps
generation bounded regardless of how many stages are requested, at the cost
of only ever seeing a prefix, never a guaranteed-complete period -- except for
the first several stages (small enough primorial), where `generate_gaps.py`
computes one exact period directly and tiles it, which is exact (not an
approximation) and cheap regardless of how deep `PREFIX_LEN` goes. Those
early, high-consumption-ratio stages are also the bottleneck that limits how
far lineage tracking (e.g. the age view) can trace forward before running
out of data, which is why pushing `PREFIX_LEN` deep specifically pays off
there.

Every chart caps its **displayed** width at `MAX_DISPLAY_WIDTH` (currently
1400, near the top of `gap_heatmap.py`), independent of how much underlying
data exists -- without this, one real pixel per data cell means the SVG
grows exactly as wide as the data itself, which produced literal 12-15MB
files at `PREFIX_LEN=100000`. Charts with less real data than the cap show
their true (unpadded) width; charts with more are simply truncated to it,
never padded with white to fill the gap.

### `giant/` -- full-detail versions

A parallel, uncapped set of the same charts (rendered by temporarily setting
`MAX_DISPLAY_WIDTH` far higher, e.g. to `PREFIX_LEN` itself) lives in
`../giant/`, committed despite its size (~95MB total, no single file over
100MB) for anyone who wants to see the full depth rather than the
article-ready crop in `out/`. Regenerate it by bumping `MAX_DISPLAY_WIDTH`,
rerunning `gap_heatmap.py`, and copying `out/*` into `giant/`.

## Output Files

### The real data series (`out/gap-heatmap*.{svg,png}`, `out/gap-two-*.svg`)

Each grid `.svg` embeds a matching `.png` (the actual pixel grid, one pixel
per gap) as a base64 `<image>`, with row labels, legends, and (where
relevant) boundary curves added as ordinary SVG text/lines on top. The two
`gap-two-*.svg` line charts are plain SVG (no embedded raster -- one line per
series, not one mark per data point). Regenerating `gap_heatmap.py`
overwrites all of these together.

| File | What it shows |
|---|---|
| `gap-heatmap.svg` | One row per stage, one pixel per gap. Color = gap value, sequential ramp, histogram-equalized (not linear -- gap values are heavily right-skewed). Red pixel = the first survivor in that row that isn't actually prime (always exactly `head^2`, see the properties file). |
| `gap-heatmap-staggered.svg` | Same data, each row shifted 1px further right than the last. Purely cosmetic (breaks up diagonal moire), no data meaning. |
| `gap-heatmap-diff.svg` | Row-to-row diff using the *true* copy-or-merge lineage (not same-column index, which points at unrelated regions of the number line between rows starting at different heads). Renders as flat gray almost everywhere -- that's the expected result: the copy-or-merge theorem forces the diff to be exactly 0 wherever it can be computed. See `verify.py`'s `check_copy_or_merge_theorem_is_exact`. |
| `gap-heatmap-diff-staggered.svg` | Staggered variant of the diff view. |
| `gap-heatmap-diff-simple-shift.svg` | The naive version of the diff view: one constant per-row offset, no merge tracking. Matches the rigorous version until a row's first real merge, then reads as a persistent mismatch for the rest of the row -- which only happens where a merge is possible within the window at all, making the colored region a direct visual trace of the `head^2` boundary. |
| `gap-heatmap-merges.svg` | Per-cell: how many old gaps fed into this one (1 = copied unchanged, 2+ = merged). Mostly uniform background with rare accent-colored merge cells, concentrated in the early (small-head) rows where merges are relatively frequent. |
| `gap-heatmap-age.svg` | Per-cell: how many consecutive stages a gap has survived without being merged (resets to 1 on merge). Implements the concept documented but not yet wired up in the Scala codebase (`GapLineage.scala`'s `age` field is currently hardcoded to 1 everywhere). Row width is capped to the *shortest* row's real (non-`None`) data, not padded -- age is chained across every prior stage, so once any row's lineage runs out anywhere, every later row inherits that gap and white space would otherwise cascade and widen going down the rows. |
| `gap-heatmap-age-staggered.svg` | Staggered variant of the age view. |
| `gap-heatmap-2focused.svg` | 06-article-diagram-ideas.md's "2-Focused Compression": every 2-gap kept as its own cell (green), runs of non-2-gaps between consecutive 2-gaps collapsed into one summed cell (blue ramp). Row width is capped to the shortest row's compressed length, not padded, for the same no-white-space reason as the age view. |
| `gap-heatmap-2focused-staggered.svg` | Staggered variant of the 2-focused view. |
| `gap-heatmap-2focused-age.svg` | Combines the two views above: x-axis is the 2-focused compression, but color is age, not magnitude. A standalone 2-gap always renders as the same fixed green (its own age is not shown); only merged runs are colored via the age ramp (equalized over run-ages only, not diluted by the far more numerous 2-gap ages). Without this split, a 2-gap and a similarly-young run land at nearly the same ramp position and become indistinguishable -- the whole point of a combined view is making the rare, interesting runs' age stand out. |
| `gap-heatmap-2focused-age-staggered.svg` | Staggered variant of the 2-focused age view. |
| `gap-two-frequency.svg` | Line chart, one point per stage: what fraction of that stage's gaps are exactly 2. Declines sharply from 100% (stage 1, head=3 -- every gap between consecutive odd numbers is 2) toward roughly 10% by head~1200, computed directly from this dataset's own prefix. |
| `gap-two-cluster-size.svg` | Line chart, two series sharing one y-axis (same unit, gap-distance): the average and max *distance between consecutive 2-gaps*, per stage -- i.e. the average/max value of `compress_around_two`'s summed runs (the same function the 2-focused heatmap itself uses), not each individual non-2 gap on its own (a run of `[4, 6]` between two 2-gaps is one distance of 10, not two separate values 4 and 6 -- an earlier version of this chart used individual gaps directly, under-reporting both series once runs started spanning more than one raw gap, which happens quickly). The average grows steadily (4 -> ~125); the max grows much faster still (4 -> ~1450), diverging further from the average as head increases. The average's floor is always exactly 4, never lower: once the filter includes 3 (stage 2 onward), three consecutive survivors spaced 2 apart is impossible (they'd cover all three residues mod 3, so one is always a multiple of 3) -- the smallest possible non-2 gap, and therefore the smallest possible run, is the classic prime-quadruplet spacing `[2,4,2]`. A companion fact this dataset also confirms: a *raw* run of two-or-more consecutive 2-gaps is impossible for the same reason, so this file doesn't chart "2-gap cluster length" literally -- it's always exactly 1 (except the trivial stage 1, where every gap is 2). |

`gap-heatmap.svg`, `gap-heatmap-merges.svg`, `gap-heatmap-age.svg`, and
`gap-heatmap-diff-simple-shift.svg` all draw two overlay curves where
applicable: a dashed unproven-but-tight estimate, and a solid proven-but-loose
safe lower bound (citation link included on the chart itself). Full
derivation of both in the properties file linked above.

### Small public-sample figures (`out/hit-miss-matrices.svg`, `out/stage-transition-repeat-filter-rotate.svg`)

Two more figures live alongside the full-dataset ones above but don't depend
on the large generated CSV:

| Script | Output | Depends on | What it shows |
|---|---|---|---|
| `hit_miss_heatmap.py` | `out/hit-miss-matrices.svg` | `data/sieve-sequence/first_gaps_per_seq.sample.csv` (the small, committed sample) | Six 10x10 grids (stage 0, head=2 through stage 5, head=13), one per early stage, each cell showing a survivor's own value: green if actually prime, red (struck) if the finite filter accepted a composite. Row 1 is plain odd numbers (no filter beyond "not even") -- the natural hit/miss baseline every later stage thins out from. Each panel is captioned with its exact flagged fraction and periodic gap cycle. |
| `stage_transition_diagram.py` | `out/stage-transition-repeat-filter-rotate.svg` | nothing -- pure computation via `generate_gaps.py`'s `compute_full_period` | Renders one or more stage transitions (`TRANSITIONS` list, default `[1, 2]`) as eight literal steps each: Gaps -> Generated numbers -> Repeat -> Rotate -> Candidate values -> Filter -> Gaps -> Generated numbers. Every step shows exactly what its own operation produces, nothing padded "for clarity" -- e.g. the Repeat step tiles the base gap cycle exactly `new_prime` times, never more. Rotate (shifting the tiled cycle left by exactly one position, since the new stage's head is always exactly one gap-step past the old one) is what lets Candidate Values walk forward from the *new* head directly, with no separate reframing step needed afterward -- invisible for a period-1 base unit ([2,2,2] rotated is still [2,2,2]), visibly non-trivial for period-2+ ones (stage 2->3's `[2,4,2,4,...]` rotates to `[4,2,4,2,...]`). |

Run either script directly (`python3 hit_miss_heatmap.py` /
`python3 stage_transition_diagram.py`) -- neither needs `generate_gaps.py` to
have been run first for the full dataset; `hit_miss_heatmap.py` only needs
the committed sample CSV, and `stage_transition_diagram.py` needs nothing at
all beyond this directory's own `generate_gaps.py` import.

### Early placeholder diagrams (`out/01-*.svg` through `10-*.svg`)

These predate the real-data heatmap series and use illustrative/synthetic
numbers, not generated data -- built from `render_diagrams.py`, a separate,
smaller script for the original ten article-figure concepts (copy-or-merge
strip, safe-zone boundary, etc.) in `06-article-diagram-ideas.md`. Useful as
concept sketches; **do not cite numeric values from these** -- they aren't
computed from real sieve-sequence data.

## Verification

`verify.py` re-derives, from the actual generated data, every claim these
figures depend on:

- The three smallest stages' gap cycles match hand-verified values.
- The first non-prime survivor of every stage is exactly `head^2` (Property 1
  in the properties file), wherever the window reaches far enough to observe
  it.
- The copy-or-merge theorem holds with zero exceptions across every
  compared position in the dataset (currently ~19.7 million, at
  `PREFIX_LEN=100000`).
- The Schroeder (2017) proven safe bound (Property 2) is never violated,
  wherever there's ground truth to check it against.

It also reports (but does not fail on) how well the unproven estimate
(Property 3) fits -- that curve is explicitly a conjecture, not a guarantee,
so a mismatch there is informational, not a bug.

Run it after regenerating data, and before citing any number from these
figures in an article.

## Unit Tests

`verify.py` checks the generated *data* against this project's mathematical
claims; it does not exercise the rendering/plumbing code itself (`svg_kit.py`,
`png_writer.py`, `gap_heatmap.py`'s helpers, etc.). `tests/` covers that code
directly with plain `unittest`-style tests run via `pytest`, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md)'s testing policy.

This directory's scripts are deliberately stdlib-only, so `pytest` is a
dev-only dependency, isolated in a local virtualenv rather than installed
system-wide:

```
python3 -m venv .venv
.venv/bin/pip install -r requirements-dev.txt
.venv/bin/python -m pytest tests/
```

Tests run in well under a second: they exercise pure functions directly
(`compress_around_two`, `lineage_walk`, `hex_to_rgb`, the PNG/SVG encoders,
`compute_full_period`, ...) using small hand-checked or `_walk_stage`-derived
fixtures, plus the small committed sample CSV -- never the full (gitignored,
multi-hundred-MB) dataset.

## Known Limitations

- Even at `PREFIX_LEN=100000`, most stages' data never reaches far enough to
  observe a single merge -- see the "chaos-to-order" boundary discussion in
  the properties file. This is disclosed on the charts themselves (the
  boundary curves), not hidden.
- `out/`'s charts additionally cap their *displayed* width well below what
  the data supports (`MAX_DISPLAY_WIDTH`); `giant/` has the uncapped
  versions for the same underlying data.
- The tight/practical boundary estimate (Property 3) is not proven; only
  empirically verified against available ground truth (`p` up to the low
  hundreds, growing as `PREFIX_LEN` grows -- see `verify.py`'s output for the
  current exact range).
