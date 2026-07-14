# Math-Only Sieve Gap Survival Article

**Created:** 2026-07-14
**Status:** Active
**Owner:** article drafting

## Goal

Create a follow-up article after `articles/chapter6/sieve-sequence-v2.md`
that studies mathematical consequences of sieve-sequence gap dynamics without
claiming Stainless verification.

The article should focus on properties such as:

- gap copy and merge behavior under the next-head filter;
- global-window survival of twin-prime candidates / 2-gaps;
- conditions under which a gap value can never reappear in later stages;
- how finite sieve-sequence objects can support future-prime analysis.

## Current State

- `articles/chapter6/sieve-sequence-v2.md` is the verified-properties article.
- `articles/chapter6/gap-dynamics.md` contains active but historically
  overconfident gap-dynamics material.
- `articles/learnings/learnings-capacity-argument.md`,
  `articles/draft/draft-empirical-g-local-analysis.md`, and deprecated gap
  persistence/twin-prime drafts contain useful mathematical ideas.
- Several tickets document gap copy/merge, survivor windows, empirical
  2-gap counts, and open proof boundaries.

## Expected State

- A new draft article under `articles/draft/` or `articles/chapter6/` with a
  clear title and an explicit math-only status.
- The article must not cite tickets or internal learnings documents directly.
- It may use ideas from tickets/deprecated drafts, but it must present them as
  self-contained mathematics.
- It must not claim formal verification unless a referenced property is already
  verified and cited accurately.

## Similar Tickets And Inputs

- `tickets/active/sieve-sequence-v2-gap-filter-properties.md`
- `tickets/active/sieve-property-landscape.md`
- `tickets/sieve-sequence-epic.md`
- `tickets/archived/empirical-g-local-crossover.md`
- `tickets/done/v0-gap-list-cycle-formalization.md`
- `tickets/done/filter-merge-foundation-gaps.md`

## Plan

1. Read the current V2 sieve-sequence article and the gap-related active,
   draft, deprecated, and ticket materials.
2. Extract only the mathematically useful claims, separating proven,
   plausible, empirical, and speculative statements.
3. Draft a new math-only article with explicit status labels.
4. Run markdown/diff checks only; do not run Stainless for markdown-only work.

## Learning Log

| Date | Observation | Implication |
|------|-------------|-------------|
| 2026-07-14 | Ticket created before drafting the math-only follow-up article. | Keep this article separate from `sieve-sequence-v2.md`; it may present mathematical conjectural structure, but must not pretend to be fully verified. |
| 2026-07-14 | Created `articles/draft/draft-sieve-gap-survival-math.md`. It is a math-only follow-up covering copy/merge gap dynamics, stable absence of 2-gaps, full-period 2-gap survival, safe-window/local-capacity boundaries, cluster survival, safe-window stability, and later-forbidden gap values. | The draft intentionally avoids ticket/internal-learning references and does not claim Stainless verification for its new mathematical claims. |
| 2026-07-14 | Reviewed the full draft for over-strong and imprecise claims. Corrected the merged-gap lower bound wording, required both endpoints for safe-window 2-gaps, made the local-capacity implication explicitly conditional on the isolation hypothesis, and replaced overbroad permanence language with induction phrasing over later stages. | The draft now separates proven copy/merge consequences from conditional local survival arguments more clearly. |
