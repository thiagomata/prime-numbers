# Sieve-Sequence Mathematical Property Catalog

**Created:** 2026-07-20
**Status:** Active
**Owner:** mathematical reference documentation

## START HERE

Create a top-level `properties/sieve-sequence/` reference catalog. Add one
self-contained Markdown file per strong mathematical property discussed in the
gap-survival analysis, beginning with exact batched 2-gap survival.

## Goal

Preserve the strongest useful sieve-sequence properties in a form that can be
read independently. Every property file must state its notation, hypotheses,
claim, proof or derivation, consequence, and exact limitation.

## Current State

- The properties are distributed across chapter articles, a math-only draft,
  internal learnings, and the local-capacity exercise.
- The newly derived batch property is not yet recorded in the repository.
- Global identities, local conditional bounds, numerical observations, and
  open positional claims need visibly different status labels.

## Expected State

- Add `properties/sieve-sequence/README.md` as an index.
- Add separate files for:
  - exact full-period 2-gap count;
  - exact batched 2-gap survival;
  - post-3 isolation of 2-gaps;
  - exact accepted local filter strikes;
  - local survival threshold;
  - global-count-to-local forcing threshold;
  - safe-window prime certification;
  - rotation invariance and its local boundary limitation.
- Mark these notes as mathematical references, not Stainless-verified claims,
  unless an exact verified source is cited.

## Similar Tickets And Inputs

- `tickets/active/local-safe-window-capacity-exercise.md`
  - Establishes the current local strike-capacity exercise and its boundary.
- `tickets/future/sieve-sequence-v2-gap-filter-properties.md`
  - Tracks copy/merge behavior and stable absence of 2-gaps.
- `tickets/future/math-only-sieve-gap-survival-article.md`
  - Tracks the broader math-only gap-survival article.
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md`
  - Tracks exact complete-period density results.
- `articles/learnings/learnings-capacity-argument.md`
  - Catalogs sound invariants, failed global-to-local arguments, and the open
    positional boundary.

## Alternatives Considered

- Add the batch property directly to a chapter article.
  - Rejected for this task because the user requested independent property
    files, and publication articles have stronger representation requirements.
- Put all properties in one document.
  - Rejected because it makes individual claims harder to review and reuse.
- Record only the new batch theorem.
  - Rejected because its meaning depends on nearby global, local, isolation,
    certification, and rotation properties.

## Risks, Assumptions, And Hypotheses

- Risk: a conditional local statement could be presented as an unconditional
  twin-prime result.
  - Validation: every local file must include an explicit limitation section.
- Risk: cyclic rotation could be described as changing the global gap count.
  - Validation: distinguish cyclic invariance from linear-window boundaries.
- Assumption: after filtering by 2 and 3, every 2-gap start is `5 mod 6`.
  - Validation: include the elementary residue proof in the relevant files.
- Hypothesis: batching improves exact bookkeeping but does not itself prove a
  positive count in a safe window shorter than the combined modulus.
  - Validation: state the complete-period CRT proof and separately identify the
  unproved short-window discrepancy bound.

## Validation

- Review every formula for half-open interval endpoints.
- Cross-check notation across all property files.
- Confirm all files clearly separate theorem, conditional theorem, empirical
  observation, and open problem.
- Run `git diff --check`; no Stainless run is required for Markdown-only work.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-20 | Created ticket after reviewing related tickets, articles, and learnings. | The catalog will use one file per property and keep global identities separate from local positional requirements. |
| 2026-07-20 | Added the indexed property catalog under `properties/sieve-sequence/`. | Added independent notes for the exact global count, batch survival, 2-gap isolation, accepted local strikes, local survival, safe-window certification, global forcing threshold, rotation invariance, stable absence, and the short-window discrepancy boundary. |
| 2026-07-20 | Corrected the local framing to retain distribution across repeated copies. | For an old 2-gap `(a,a+2)`, a new prime forbids exactly two copy-index classes modulo that prime. The whole batch is therefore a deterministic residue-class covering problem, not arbitrary local deletion. Added `copy-index-filter-frequency.md` and revised the discrepancy boundary accordingly. |
| 2026-07-20 | Validated the documentation and finite-copy formula. | Direct enumeration confirmed the bound `destroyed <= 2*ceil(N/r)` and exactly two destructions in every complete `r`-copy block. New files have no trailing whitespace and all README links resolve. Repository-wide `git diff --check` remains blocked by a pre-existing trailing-space line in `LEARNINGS.md`; that unrelated file was not changed. |
| 2026-07-20 | Reverse-engineered the complete initial certificate for an eventual head 2-gap. | Added `reverse-engineered-eventual-head-scenario.md`. A seed residue gap, a safe-window copy-index interval, avoidance of two forbidden classes for each prime in one finite batch, and an unbounded family of successful coordinates are sufficient. Once the copy reaches a square-safe stage, primality is certified and later arrival at head is automatic. The remaining theorem is nonempty intersection of the geometric and batch-allowed index sets for infinitely many scenarios, not for every head. |
| 2026-07-20 | Added the independent expert-verification property `infinite-perfect-scenario-property.md`. | The standalone note assumes only the linked sieve articles and defines the initial stage, seed gap, cumulative prime-gap chain, common `p^2` horizon, eligible copy-index interval, exact forbidden classes, six perfect-scenario conditions, finite certificate proof, open infinite-occurrence property, covering form, worked example, dependency diagram, and twelve review questions. It explicitly requires `p>=3` and `k>=1`, permits arbitrarily rare variable scenarios, and does not claim infinitude or twin-prime proof. README index updated; links, fences, and scoped whitespace checks passed. |
