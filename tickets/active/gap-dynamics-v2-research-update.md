# Gap Dynamics V2 Research Update

**Created:** 2026-07-20
**Status:** Complete
**Owner:** article review preparation

## START HERE

Create `articles/chapter6/gap-dynamics-v2.md` as a new review candidate. Leave
the current `gap-dynamics.md` unchanged.

## Goal

Produce a self-contained v2 article that preserves the sound copy-or-merge and
full-period results while incorporating the newer property catalog:

- exact global and batched 2-gap survival;
- exact two-class copy-index filtering;
- post-3 isolation of 2-gaps;
- exact accepted strikes in the next safe window;
- the sharp one-transition threshold;
- finite perfect-scenario certificates and the weaker infinitude target;
- the fixed-seed primorial scale conflict;
- short-window discrepancy, covered-run, and Type I/Type II boundaries;
- the finite perfect-scenario generator as an experimental next step.

## Current State

- `articles/chapter6/gap-dynamics.md` uses a coarse raw `p-1` strike count and
  emphasizes an every-stage local-density condition.
- `articles/draft/draft-sieve-gap-survival-math.md` distinguishes global from
  local survival but predates the exact batch and accepted-strike properties.
- The independent property notes now give a sharper theorem/boundary map.
- Recent prime-producing sieve research identifies arbitrary-coefficient Type
  II cancellation as the missing analytic input beyond divisibility density.

## Expected State

- Add only `gap-dynamics-v2.md`; do not rewrite or remove the current article.
- Make every theorem's mathematical and Stainless status explicit.
- Use all three representations for article properties. For mathematically
  proved but unverified properties, include clearly marked draft Scala
  signatures and state that Stainless verification is pending.
- Keep failed approaches out of the main narrative except where they establish
  a reusable negative boundary.
- Keep framing honest: no proof of infinitely many twin primes is claimed.

## Similar Tickets And Inputs

- `tickets/future/math-only-sieve-gap-survival-article.md`
- `tickets/active/sieve-sequence-property-catalog.md`
- `tickets/active/local-safe-window-capacity-exercise.md`
- `tickets/active/recent-prime-producing-sieve-research.md`
- `tickets/active/finite-perfect-scenario-generator-next-step.md`
- `tickets/active/scientific-review-articles-2026-07-17.md`

## Alternatives Considered

- Update `gap-dynamics.md` directly.
  - Rejected because the user requested a separate v2 for team review.
- Add every historical failed attempt.
  - Rejected because chronological failure logs obscure the theorem boundary.
- Keep only the original local-density formulation.
  - Rejected because exact accepted strikes and rare perfect scenarios are
    strictly sharper formulations.

## Risks, Assumptions, And Validation

- Risk: confuse complete-period CRT density with short-window positivity.
  - Validation: state the discrepancy term and covered-run problem explicitly.
- Risk: present the `q<p^2` scale conflict as disproving finite scenarios.
  - Validation: state only that it removes local multiplicity for one fixed
    seed and motivates averaging over seeds or heads.
- Risk: imply Ford--Maynard or Green--Sawhney transfers directly to twin pairs.
  - Validation: list the missing Type II estimate and extra-structure boundary.
- Risk: overstate Stainless coverage.
  - Validation: label every new property as verified, mathematically proved
    with verification pending, conditional, or open.
- Final validation: whole-document precision pass, local links, code fences,
  article framing, and scoped whitespace checks.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-20 | Created the v2 article ticket after searching existing articles, property notes, tickets, `.holds` lemmas, `OBJECTS.md`, and `PROOF_GUIDE.md`. | The article will distinguish verified construction foundations from mathematically proved but unverified gap theorems and open analytic boundaries. |
| 2026-07-20 | Completed `articles/chapter6/gap-dynamics-v2.md` without modifying `gap-dynamics.md`. | The v2 article covers verified copy/merge branches, stable absence, exact global and batched counts, copy-index classes, rotation, square-safe certification, exact accepted strikes, the sharp local threshold, finite perfect scenarios, the fixed-seed scale conflict, discrepancy and extremal count boundaries, Type I/Type II research, and the finite generator. Every unverified Scala block is marked as a draft specification sketch. |
| 2026-07-20 | Completed the whole-document precision pass. | Abstract, body, claim boundary, and conclusion agree; local links resolve; code fences are balanced; headings are unique; no trailing whitespace, ticket references, stale `sieve-sequence-v2.md` links, or old `G_local>p` capacity formulation remain. Markdown-only work required no Stainless run. |
