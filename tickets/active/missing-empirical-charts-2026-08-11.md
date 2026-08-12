# Missing Empirical Charts

**Created:** 2026-08-11
**Updated:** 2026-08-11
**Status:** Open

## Related Tickets

- `sieve-sequence-visual-presentation.md` — presentation-concept proposals
  (`01`-`06` under `presentations/sieve-sequence-visualization/`); this ticket
  is scoped to article/candidate charts specifically, not presentation
  concepts. `06-article-diagram-ideas.md` is the shared boundary: static
  figures for articles live there in spirit, animation/interactive concepts
  (e.g. `03-merge-theater.md`) do not belong in this ticket's scope.

## Goal

This session identified that most figures `gap_heatmap.py` generates are
orphaned (10 of 13 never embedded anywhere), while some of the project's most
important empirical claims have no chart at all, anywhere, despite having
ready or near-ready data. Track the three highest-value gaps found so they
aren't lost.

## Background

No article in `articles/` is primarily empirical (see discussion this
session); the closest thing,
`articles/draft/draft-empirical-g-local-analysis.md`, is explicitly
superseded and uses the old, incompatible `[p,p^2)` convention. A dedicated
empirical article was proposed as the destination for the charts below,
alongside extending individual `candidates/*.md`'s existing
"Empirical status" pattern to `properties/sieve-sequence/*.md`, which
currently has none at all (`properties/sieve-sequence/README.md` never
mentions "empirical").

## The Three Gaps

### 1. `local-surplus.md` (#2): `G_local` vs `A_worst`, head to head

**Priority:** highest — most ready, most important.

Candidate #2 is called "the strongest signal in the entire run" and the
"terminal sufficient target" in `candidates/analysis/FINDINGS.md`, with a
reported `surplus ~ p^1.6` growth trend (186/186 transitions, zero
failures) — yet has no chart anywhere. A two-line chart (`G_local` vs
`A_worst`, or just `surplus` on a log-log axis) would directly and visually
settle the "do shots ever outnumber gaps" question for the current canonical
convention, correcting the impression left by the superseded historical
`[p,p^2)` draft (which *did* show shots winning, but only pre-crossover at
`p<37`, in an incompatible convention).

**Data:** fully ready, no new generation needed —
`data/candidates/window-measurements.csv` (dense, p to ~1000) and
`data/candidates/window-measurements-sparse.csv` (p to ~19000), both already
have `G_local` and `A_worst` columns.

### 2. Deferred-filter-3 candidate — no chart from this session's new data

**Priority:** high — directly ties to this session's work, data already
generated and verified.

`candidates/deferred-filter-three-cluster-survival.md` (new this session) is
backed by `data/candidates/deferred3-measurements.csv`
(`candidates/analysis/run_deferred3.py`, 165 heads, q=7..997): the flat
cluster cap at exactly 3 (`max_run_length == predicted_cap` in all 165 rows),
the growing `n_two_gaps_deferred`/`n_two_gaps_post` counts, and the
`d_head_post` distribution (median 16, max 148) are all sitting unused.

**Data:** fully ready, no new generation needed.

### 3. Lineage dataset — a structurally different, never-charted question

**Priority:** important but data-constrained.

Every existing/planned chart (including #1 and #2 above) asks "one layer,
many different heads." The lineage experiment
(`candidates/analysis/run_lineage.py` /
`empirical/sieve-sequence/.../lineage_cli.py`) asks the opposite: fix one
target head `Q`, walk it through every intermediate filter layer on the way
there. That is the literal shape of "does the local count survive as we
approach one specific target," which recurred throughout this session's
discussion, and it has never been visualized.

**Data:** thin. Only two pilot runs exist —
`data/candidates/lineage-Q17.csv` (6 rows) and
`data/candidates/lineage-Q101.csv` (25 rows). A chart from these now would be
a proof-of-concept, not a strong result. A larger lineage sweep (more heads)
should probably precede building this chart, unlike #1 and #2.

## What This Session Already Did With Existing Charts (not part of this ticket)

For context, so this isn't duplicated: `hit-miss-matrices.svg` and
`gap-heatmap-2focused.svg` were identified as already-generated, good-fit
figures for `sieve-sequence.md`/`gap-dynamics-v3.md` and handled directly in
this session rather than deferred here. `stage-transition-repeat-filter-rotate.svg`
was identified as belonging to the `03-merge-theater.md` presentation
proposal instead of any article. The diff-heatmap
(`gap-heatmap-diff-simple-shift.svg`) was concluded not to belong in any
current article and dropped from `sieve-sequence-v2.md`.

## Next Action

Pick #1 (`local-surplus` chart) first — highest value, zero new data
collection. #2 next. #3 only after a larger lineage sweep exists.
