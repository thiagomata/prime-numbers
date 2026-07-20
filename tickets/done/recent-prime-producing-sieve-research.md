# Recent Prime-Producing Sieve Research

**Created:** 2026-07-20
**Status:** Complete
**Owner:** external research audit

## START HERE

Deeply assess recent established work on prime-producing sieves, Type I/Type II
estimates, structured prime sets, parity-breaking techniques, and short-interval
prime distribution against the exact perfect-scenario obstruction documented
under `properties/sieve-sequence/`.

## Goal

Produce a self-contained research note that answers:

1. Which recent results are genuinely relevant to the perfect-scenario count?
2. Which hypotheses can already be supplied by sieve-sequence repetition and
   CRT uniformity?
3. Which missing estimate remains responsible for positivity?
4. What concrete theoretical and computational work should happen next?

## Current State

- Exact complete-period 2-gap counts and batch survival are known.
- Each new filter forbids exactly two copy-index classes.
- A finite perfect scenario is an explicit intersection between a safe-window
  copy-index interval and a batch-allowed residue set.
- Infinite occurrence remains open because no positive short-window lower
  bound or maximum-covered-run bound has been proved.
- Existing internal review identifies the classical sieve parity problem as a
  likely obstruction to any argument using only local divisibility density.

## Expected State

- Add a research note under `properties/sieve-sequence/research/`.
- Use primary sources for technical claims.
- Explain Ford--Maynard Type I/Type II requirements in project notation.
- Assess Green--Sawhney, structured-set sieves, recent distribution-level
  improvements, and short-interval results without claiming direct transfer.
- Reject unreviewed purported twin-prime resolutions as established evidence.
- Give explicit proof obligations, falsification tests, and staged milestones.

## Similar Tickets And Inputs

- `tickets/active/sieve-sequence-property-catalog.md`
  - Defines the perfect-scenario and copy-index properties being assessed.
- `tickets/active/scientific-review-articles-2026-07-17.md`
  - Records the prior parity-problem and scientific-merit review.
- `tickets/future/math-only-sieve-gap-survival-article.md`
  - Tracks the broader math-only gap-survival presentation.
- `properties/sieve-sequence/infinite-perfect-scenario-property.md`
  - Main mathematical target for this research audit.
- `properties/sieve-sequence/batched-short-window-discrepancy-boundary.md`
  - Current statement of the missing short-window estimate.

## Alternatives Considered

- Summarize recent papers without mapping their hypotheses.
  - Rejected because it would not identify an actionable unblocker.
- Treat every recent arXiv claim of a twin-prime proof as progress.
  - Rejected unless independently validated or accepted by the field.
- Focus only on improved prime-gap constants.
  - Rejected because bounded gaps and twin-pair lower bounds have different
    parity requirements.

## Risks, Assumptions, And Validation

- Risk: confuse exact Type I residue counts with Type II cancellation.
  - Validate by writing both estimate families explicitly.
- Risk: claim a theorem transfers from a structured polynomial sequence to the
  affine pair `(x,x+2)` without its extra algebraic variables.
  - Validate every transfer hypothesis separately.
- Risk: mistake an improved upper bound for a positive lower bound.
  - Label the direction of every cited result.
- Assumption: the best immediate use of recent work is a diagnostic reformulation
  even if it does not close the conjecture.
  - Validate by producing concrete proof obligations and failure criteria.
- Final validation: source links resolve, all external claims are cited near
  their use, and scoped Markdown/fence/whitespace checks pass.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-20 | Created research ticket after locating the existing parity review and perfect-scenario catalog. | The audit will prioritize theorem-to-hypothesis mapping over general literature summary. |
| 2026-07-20 | Added `properties/sieve-sequence/research/recent-prime-producing-sieves-deep-dive.md` and indexed it in the property README. | Ford--Maynard gives the actionable diagnostic: prove genuine short-window Type I uniformity and a sufficiently long arbitrary-coefficient Type II range. Current CRT identities prove neither complete norm. The audit also found that `q<p^2` implies the fixed-seed primorial eventually exceeds `q^2`, so local multiplicity must come from averaging over seeds, heads, or another structural variable. |
