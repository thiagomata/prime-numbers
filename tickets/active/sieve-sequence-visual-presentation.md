# Sieve Sequence Visual Presentation

**Created:** 2026-07-20
**Status:** Active
**Owner:** presentation design

## Goal

Create a small set of competing presentation concepts for showing how sieve
sequence gap cycles evolve from exact small stages into large-scale structure.
The concepts should cover both video and interactive options, with special
attention to:

- gap copy versus merge events;
- values accepted by the current sieve that later turn out to be composite;
- the end of the safe zone, where current local primality certification no
  longer applies;
- 2-gap neighborhoods and their changing spacing patterns;
- Spark-derived data, including gap lineage and 2-gap focused compression.

## Current State

The Spark generator writes stage data under `spark/data/sieve-df/`, including
partitioned gap cycles, first values, gap origins, and 2-gap compressed views.
The repository also contains article and property-planning material around
copy-or-merge gap dynamics, full-period 2-gap survival, and the safe-zone
boundary.

## Expected State

A presentation folder should exist with several distinct markdown proposals.
Each proposal should be opinionated enough to compete with the others instead
of blending into one generic dashboard plan.

## Similar Tickets And Inputs

- `tickets/active/spark-sieve-data-generator.md`
- `tickets/future/sieve-property-landscape.md`
- `tickets/future/math-only-sieve-gap-survival-article.md`
- `articles/draft/draft-sieve-gap-survival-math.md`
- `spark/README.md`

## Assumptions And Hypotheses

- A semantic zoom from exact gaps to aggregate texture is a better core
  metaphor than a static chart collection.
- Copy/merge events should be visual primitives, not secondary annotations.
- Composite revelation must be separated from primality certification so the
  viewer sees what the current sieve knows and what only becomes known later.
- The safe zone should be shown as a moving boundary at `head^2`, not as a
  vague confidence region.
- Stage 8 and beyond should rely on aggregated or tiled data rather than
  drawing every gap in the browser.

## Validation Plan

- Run `git diff --check` because this is markdown-only.
- Check that every proposal says what it highlights, what data it needs, and
  where it is strongest or weakest.
- Check that no proposal claims proof strength beyond the current mathematical
  boundary.

## Learning Log

| Date | Observation | Implication |
|------|-------------|-------------|
| 2026-07-20 | Created the ticket before adding presentation concept files. | Keep the concepts grounded in existing Spark outputs and known proof/article boundaries. |
| 2026-07-20 | Added five competing proposal files under `presentations/sieve-sequence-visualization/` plus a folder README. | The strongest first prototype is the merge theater: it proves the visual grammar before investing in a full film or atlas. |
| 2026-07-20 | `git diff --check` passed for the markdown-only change. | No Stainless verification was needed for this documentation-only update. |
| 2026-07-20 | Added `06-article-diagram-ideas.md` with static figure concepts for the articles. | Article diagrams should be self-contained, one-claim figures that separate full-period structure from local safe-zone questions. |
