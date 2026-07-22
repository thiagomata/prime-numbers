# Local Safe-Window Capacity Exercise

**Created:** 2026-07-20
**Status:** Active
**Owner:** math exercise / reader-facing draft

## Goal

Create one detailed standalone exercise for a math student. The student should
only need the exercise text plus links to the existing sieve-sequence articles.
The exercise should ask them to verify the local strike-capacity bound for
2-gap survival in the next safe window.

## Current State

- `articles/chapter6/sieve-sequence.md` defines the sieve sequence, global
  period, expansion, filtering, and next-stage count.
- `articles/draft/draft-sieve-gap-survival-math.md` describes full-period
  2-gap survival, safe-window locality, and local capacity.
- `tickets/future/sieve-sequence-v2-gap-filter-properties.md` records a
  future article subsection about copy/merge behavior under filtering.

## Expected State

- Add a draft exercise under `articles/draft/`.
- The exercise must:
  - define the current head `p`, next head `q`, previous modulus `M`, and next
    safe window `[q, q^2)`;
  - explain that the same filter rule applies locally and globally;
  - prove the maximum number of values removed by the `p`-filter in the local
    window:
    `floor((q^2 - 1) / p) - floor((q - 1) / p)`;
  - prove the corresponding worst-case 2-gap destruction bound:
    at most twice that many local 2-gaps;
  - state a clear survival condition:
    if local 2-gaps before filtering exceed that worst-case capacity, at least
    one local 2-gap survives;
  - include a stronger optional isolated-gap variant;
  - avoid claiming a proven lower bound for local 2-gap abundance.

## Similar Tickets

- `tickets/future/sieve-sequence-v2-gap-filter-properties.md`
  - Related copy/merge behavior and filtering explanation.
- `tickets/future/math-only-sieve-gap-survival-article.md`
  - Related future article direction around the math-only gap survival draft.
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md`
  - Related exact full-period density/counting theorem; useful contrast with
    the local safe-window bound.

## Validation

- Markdown-only change, so no Stainless verification is required.
- Run `git diff --check` after creating the exercise.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-20 | Created ticket. | The exercise should emphasize that local and global use the same filtering rule; the difference is only whether the counted interval is a complete lifted orbit or a partial safe window. |
| 2026-07-20 | Added draft exercise and validated markdown. | `git diff --check` passed. The exercise proves the local capacity theorem and explicitly leaves local 2-gap abundance as a separate question. |
