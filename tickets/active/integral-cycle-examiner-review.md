# Integral Cycle Examiner Review

**Created:** 2026-07-14
**Status:** Active
**Scope:** Review `articles/integral-cycle.md` from an examiner/publication perspective.

## Goal

Evaluate whether `articles/integral-cycle.md` is publication-ready under the
project's article standards: accurate theorem framing, current source-backed
verification claims, no overclaiming beyond proved artifacts, and clear
distinction between verified code and mathematical exposition.

## Current State

The user asked for a review similar to the recent examiner review of
`articles/chapter6/sieve-sequence-v2.md`.

## Expected State

Produce a concise examiner-style assessment with:

- verdict;
- major findings ordered by severity;
- source-backed notes for any verification or citation issues;
- suggested fixes where useful.

## Similar Tickets and Prior Work

- `tickets/trash/archived/article-reviews/integral-cycle.md` — prior
  article-review artifact for this exact article.
- `tickets/active/sieve-sequence-article-rewrite.md` — identifies
  `integral-cycle.md` as a strong layout model for layered articles.
- `tickets/done/cycle-integral-filter-merge.md` — proof work related to
  filtered cycle-integral properties.
- `tickets/done/sieve-foundation-cycle-integral-ones-and-filter-preserves-primes.md`
  — proof work and article cross-reference involving cycle-integral ones.

## Validation Plan

1. Read the current article structure and claims.
2. Compare cited function names against current source.
3. Check `OBJECTS.md` for documented cycle-integral properties.
4. Review prior article-review notes for already-known publication concerns.
5. Return an examiner-style review without editing the article unless the user
   explicitly asks for fixes.

## Learning Log

- Started current examiner review; no article edits planned in this pass.
- Current article path is `articles/chapter4/integral-cycle.md`; the archived
  review still references the older root-level path.
- Major publication issue: source links in the article use `../src/...` from
  `articles/chapter4/`, which resolves to `articles/src/...`; they should point
  two levels up.
- The current Chapter 4 verification log is green in
  `logs/verify-ch-4-v1-chapter4-_.log` with `2854 valid`, `0 invalid`,
  `0 unknown`; the article's Appendix B points to `../logs/verify.log`, which is
  not the best current evidence path.
- Several Appendix A sections say "full Scala verification code" while snippets
  intentionally omit proof bodies; wording should say "representative excerpt"
  or include the full code.
- Future Work still lists x-fold expansion among unverified extended properties
  even though Section 5.2 marks it verified.
- Applied article cleanup:
  - changed source links from `../src/...` to `../../src/...`;
  - changed "full Scala verification code" wording to "key Scala verification
    excerpt" plus complete proof source links;
  - removed x-fold expansion from Future Work's unverified-property list.
- Per user direction, ignored Appendix B/log evidence for now because active
  code work will refresh final verification logs before submission.
- Second review pass findings:
  - Corrected equivalence concern after checking definitions: `ClassicCycleIntegral`
    and recursive `CycleIntegral` have the same `apply`, `period`, and `sum`
    definitions over `MemCycle`, so their equivalence is definitional. The
    cited `assertCycleIntegralMatchModCycleDef` then supplies the Recursive
    / Modulo extensional bridge.
  - The conclusion still summarizes only the three definitions and underplays
    verified Section 5 extensions; either summarize extensions or scope the
    conclusion to the core definitions.
  - Follow-up check: the period-boundary identity
    `ci(ci.period) - ci(0) == ci.sum` is proved by
    `CycleIntegralFilterProperties.assertCIShiftEqualsSum`; some wrapper lemmas
    keep it as a precondition to avoid re-proving it. Do not present this as an
    unresolved article boundary.
  - Remaining precondition precision concern is narrower: survivor filtering
    lemmas have real nonzero start/end and range preconditions that the prose
    should not silently generalize away.
  - Appendix B/log link remains intentionally ignored for now per user direction.
- Applied conclusion update to summarize the verified Section 5 properties and
  name the remaining draft extensions.
- Per user direction, added the duplicate classic cycle-integral cleanup to
  `TODO.md` instead of touching code while another developer is active. The
  article now presents only the canonical recursive `CycleIntegral` and the
  closed-form `ModCycleIntegral`, with Appendix A.1/A.2 quoting the recursive
  property source directly.
