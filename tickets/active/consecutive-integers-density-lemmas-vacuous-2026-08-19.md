# ConsecutiveIntegers density lemmas have vacuous/tautological specs

**Created:** 2026-08-19
**Updated:** 2026-08-19
**Status:** Open
**Depends on:** none

## Related Tickets

- Found during the PR #17 (articles publish prep) review, 2026-08-19;
  the review's fix work is complete and its ticket was deleted.

## Goal

Make the multi-factor density lemmas in
`src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala`
either actually prove what their Scaladoc/OBJECTS.md claims say, or have
those claims softened to match reality.

## Current State

Verified by reading bodies (2026-08-19):

- `nonzeroAfterZero`, `existsZero`, `atMostOneZero`, `exactlyOneZeroInConsecutive`,
  `findZeroOffset` (real `ensuring`), `zeroRepeatsEveryP` — REAL: they return
  the claimed expression, so `.holds` carries content. These back
  `articles/chapter2/modulo.md` §6.14 and are fine.
- `zerosInMultipleBlocks` — base case returns a real check and the else
  branch has one real assert (`Calc.mod(n + m*p + k, p) == 0`); per
  LEARNINGS.md §1.1/§1.4 that fragment can propagate. But no counting
  statement exists anywhere in the chain (no counting function, no list,
  no quantified claim), so "exactly m multiples in the interval" is not
  among the facts available to propagate.
- `countModZeroEqualsM` (line 173) — returns the value of a call with
  trivial postcondition; exports nothing. The "exactly m zeros in
  [a, a+m·p)" claim is comment-only.
- `twoFactorsDensity` (187), `densityForDivisor` (207), `densityForFactorList`
  (256) — return literal `true` or vacuous calls; Stainless verifies them
  trivially.
- `densityPreservedAfterFiltering` (229) — returns
  `(m·p1 − m)·p2 == m·p1·p2 − m·p2` where every term is a locally defined
  val, not a fact derived from modulo lemmas; it is an arithmetic
  tautology. Proves nothing about filtering.

OBJECTS.md §2.x (lines ~108-111) describes these as established lemmas.
OBJECTS.md line ~564 shows chapter 6 code referencing
`assertDensityForAllPrimesSoFarConditional` bridging to
`densityForFactorList` (at least "Conditional" in the name is honest) —
downstream reliance needs an audit.

Also: the survivor-product claim as literally stated in the PR-deleted
article paragraph ("proportion of survivors ... is the product of the
individual survival rates") is mathematically FALSE without coprimality
(counterexample: block of 30 filtered by 6 and 10 gives 23/30 survivors,
not 5/6 · 9/10 = 22.5/30). Any future real lemma needs pairwise-coprimality
(or equivalent) hypotheses.

## Expected State

Either:
(a) Real specs — e.g. an actual counting function (recursive count of
multiples in an interval) with `ensuring`, with the density lemmas
composed on top returning/ensuring the counting facts; or
(b) Comments and OBJECTS.md entries softened to "conjecture/sketch,
formal statement pending".

Plus an audit of chapter 6 call sites that lean on these lemmas.

## Approaches Considered

1. Strengthen specs (real counting function + ensuring). Risk: induction
   over intervals; `zerosInMultipleBlocks` already hints at the shape.
2. Soften claims in Scaladoc + OBJECTS.md. Low risk, loses the roadmap.
3. Audit-first: check what chapter 6 actually needs from these lemmas
   before deciding.

## Failed Paths

- None attempted yet.

## Open Concerns

- Does any chapter 6 verification currently depend on the vacuous
  postconditions (i.e., does anything call them expecting facts)? If so,
  those call sites are proving less than they appear to.

## Next Action

- Grep call sites of the four density lemmas + `countModZeroEqualsM`
  across `src/`, `companions/`, `properties/`; then decide (a) vs (b).

## Learning Log

- 2026-08-19 — Finding recorded during PR #17 review. `{}.holds` returning
  literal `true` (or a call to such) is a vacuous lemma; only returned
  expressions / `ensuring` clauses export facts to callers.
- 2026-08-19 — Refinement after discussion: `.holds` lemma calls DO export
  facts to callers (LEARNINGS.md §1.1 return expressions, §1.4 cached
  asserts) — the general mechanism is real. The density lemmas' problem is
  narrower: their bodies express no counting statement anywhere, so the
  documented claims are not among the propagatable facts. Fix shape:
  add a recursive counting function (`countMultiples(a, p, n)`), make
  `countModZeroEqualsM` return `countMultiples(a, p, m*p) == m`, and
  rebuild the density lemmas on top per LEARNINGS.md §1.2/§1.3
  (body-is-the-equality or `.ensuring`).
