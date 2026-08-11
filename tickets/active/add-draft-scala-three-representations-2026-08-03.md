# Add Draft Scala For The Pending Three-Representations Form

**Created:** 2026-08-03
**Updated:** 2026-08-03
**Status:** Open — draft Scala captured here; articles deliberately left deferring
**Depends on:** `investigate-final-programs-signed-energy-almost-prime-2026-08-03.md`
(the Filter-Seven Excess Bound property, #83, #84, #85, #86 originate there)

## START HERE

The two new review-draft articles
(`articles/chapter6/gap-dynamics-v2.md`,
`articles/draft/draft-relaxed-almost-prime-sieve-sequence.md`)
present every property with inline English + LaTeX math, but their Scala
(form 3 of the three-representations rule) is **deferred**: each property
section ends with a "Stainless And Source Evidence" subsection stating that
no `.holds` theorem exists yet.

This ticket captures the draft Scala for those properties so it is not lost,
and tracks the work of promoting each draft to a verified `.holds` theorem in
`src/main/scala/`. **The articles are intentionally left unchanged for now** —
per the decision recorded below, the articles remain self-contained for
reading the *mathematics*, and the Scala is tracked here.

The drafts below are written to be illustrative and to match the project's
existing `.holds` idiom. They are NOT compiled and NOT verified. Each is
annotated `// DRAFT — not yet verified through Stainless`.

## Related Tickets

- `investigate-final-programs-signed-energy-almost-prime-2026-08-03.md` —
  originated the Filter-Seven Excess Bound property, #83, #84, #85, #86.
- `prove-apply1-is-prime.md` — prior example of a property whose
  Stainless verification is tracked separately while the math is proved.

## Goal

One paragraph: produce, for each of the mathematically-proved-but-unformalized
properties referenced by the two new articles, either (a) a verified `.holds`
theorem in an appropriate `properties/` object under
`src/main/scala/v1/chapter6/.../properties/`, or (b) a documented obstacle
explaining why that property resists Stainless formalization (e.g. it requires
quantifying over an external analytic theorem). The finite-algebra properties
(#84/#85/#86 and the simpler 2-gap counts) are the realistic near-term
targets; the analytic-bound properties (#82's chain consequence, #83's
relative-energy input) are expected to remain documented obstacles.

## Strategy

Formalize bottom-up by difficulty, not by article order:

1. **Finite CRT counting first** — the 2-gap / cluster / batched-survival
   products (#1, #2, #3, #4) are finite products over installed primes and
   match the existing `SpecSieveSeqPeriodProperties` / `GapCycle` machinery.
   These are the closest analogues to already-verified lemmas and should
   verify first.
2. **Relaxed-weight finite algebra next** — #84's five-case local table, #85's
   Möbius/character decomposition, and the χ₃ refutation are all finite
   algebra over a squarefree wheel. They do not require any analytic input.
3. **Square-safe certification (#8) and post-filter-3 isolation (#5)** —
   elementary divisibility; `SpecSieveSeqHeadIsPrime` already proves the
   head-is-prime direction, so #8 is a two-endpoint generalization.
4. **Defer the analytic bounds** — #6 (accepted strikes, needs Bertrand +
   prime-counting), #7 (abundance antecedent is open), #25 conservation +
   #66 Cauchy chain, #82 chain consequence, #83 relative-energy input. These
   either need external theorems or are open hypotheses; record them as
   obstacles rather than forcing a verification.

The through-line: verify the finite/exact identities first because they are
both tractable and because they unblock the *citation* form (form 3 with a
real source link) for the articles. Leave the analytic bounds as documented
pending, which is what they honestly are.

## Current State

- No new `.scala` has been written. The articles continue to defer via the
  §9 weaker option (omit code, state pending).
- The drafts in the **Draft Scala** section below are captured here as a
  reference for what verification work remains. They have not been compiled.
- The mathematical content of every listed property is already proved in the
  canonical `properties/sieve-sequence/*.md` notes and in the article math
  blocks; this ticket concerns only the Scala representation.

## What is Learned

- The finished articles (`integral-cycle.md`, `list.md`, `cycle.md`,
  `modulo.md`) inline 3–29 real `.holds` blocks each and link to `.scala`
  source 9–59 times. That is the project's established bar for "self-contained
  article." The new articles meet it for math (47–85 inline math blocks) but
  not for Scala (0–1 inline blocks).
- AGENTS.md `property-completeness` §9 defines two compliant options for a
  mathematically-proved-but-unformalized property: (stronger) inline draft
  Scala annotated `// DRAFT`; (weaker) omit code, state pending. The new
  articles chose the weaker option throughout, which is permitted but below
  the finished-article bar.
- The `.holds` idiom is `object Spec... { def assertX(...): Boolean = {
  require(...); assert(...); <claim> }.holds }` with `Calc.mod`/`Calc.div`
  for all modular arithmetic (never `%`).
- `SpecSieveSeqHeadIsPrime.assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq`
  already proves the head-is-prime direction; the Safe-Window Certification property is its two-endpoint
  generalization and should compose from it.
- Finite CRT products (#1–#4) have close analogues in `GapCycle` and
  `SpecSieveSeqPeriodProperties`; deep-search those before writing new code.

## Failed Paths

(none yet — no Scala has been attempted under this ticket.)

## Open Concerns

- Stainless may struggle with quantification over "all squarefree wheels" for
  #84/#85. A bounded/finite-wheelscope formulation may be necessary; that
  would weaken the theorem statement and must be reconciled with the
  article's universal quantifier.
- #85's character-orthogonality step may need a verified character-sum lemma
  that does not currently exist in the project. Check `FourierProperties` or
  any chapter7 analytic helper before assuming it must be built.
- The analytic-bound properties (#6 Bertrand dependency, #66 weighted
  Cauchy chain, #82 chain consequence) are expected to resist Stainless and
  should be triaged as documented obstacles, not forced.

## Next Action

1. Deep-search `GapCycle`, `SpecSieveSeqPeriodProperties`,
   `SpecSieveSeqSurvivorCountProperties`, `SieveUtils` for any lemma already
   covering the #1–#4 finite CRT products. Do not write a new lemma that
   duplicates an existing one.
2. If none exists, promote the the Global 2-Gap Count property draft below into a new
   `SpecTwoGapCountProperties` object and run `just verify` on that one
   function (green-to-green, one lemma per cycle).

## Validation

- Each promoted lemma must pass `just verify <FunctionName>` and the
  chapter-by-chapter regression (`just verify-ch 6`) starting from the
  current 30 valid / 0 invalid / 0 unknown baseline.
- One lemma or assertion per verify cycle (`small-changes` rule).
- Markdown-only edits to the articles (if any are later made to inline the
  now-verified code) require no verify cycle, but a mixed code+markdown
  change does.
- Use `Calc.mod` / `Calc.div` exclusively; never `%`.

## Draft Scala (illustrative, NOT compiled)

The blocks below record the intended shape of the eventual `.holds`
theorems. They are written in the project idiom but have not been type
checked or verified. Annotate any inlined copy `// DRAFT — not yet verified
through Stainless`.

### Exact Global 2-Gap Count (finite CRT product)

```scala
// DRAFT — not yet verified through Stainless
// Target file: src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecTwoGapCountProperties.scala
package v1.chapter6.sieve.seq.spec.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc

object SpecTwoGapCountProperties {

  /**
   * For an odd installed prime q, the two forbidden 2-gap-start classes
   * x = 0 and x = -2 mod q are distinct, leaving q - 2 allowed classes.
   */
  def allowedClassesPerOddPrime(q: BigInt): Boolean = {
    require(q >= 3)
    // 0 and -2 mod q are distinct iff q does not divide 2, i.e. q is odd.
    Calc.mod(BigInt(2), q) != 0
  }.holds

  /**
   * The complete-period 2-gap count is the product of (q - 2) over every
   * installed odd prime q < p. DRAFT: this states the product form;
   * a verified proof needs a CRT bijection lemma over the installed list,
   * which should be searched for in GapCycle / SpecSieveSeqPeriodProperties
   * before being written here.
   */
  def assertGlobalTwoGapCountProduct(installed: List[BigInt]): Boolean = {
    require(!installed.isEmpty)
    // placeholder: the real proof composes allowedClassesPerOddPrime over
    // the list via a verified CRT product. TODO: locate or build that lemma.
    true
  }.holds
}
```

### Safe-Window 2-Gaps Certify Twin Primes

```scala
// DRAFT — not yet verified through Stainless
// Composes from SpecSieveSeqHeadIsPrime.assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq.
def assertSquareSafeEndpointPrime(n: BigInt, Q: BigInt, primorialQ: BigInt): Boolean = {
  require(Q <= n && n < Q * Q)
  require(Calc.gcd(n, primorialQ) == 1)  // TODO: gcd helper location
  // If n composite, least prime divisor d <= sqrt(n) < Q, so d | primorialQ,
  // contradicting gcd(n, primorialQ) = 1. DRAFT: needs the least-divisor
  // lemma already used by SpecSieveSeqHeadIsPrime; search before re-proving.
  true
}.holds
```

### Exact Divisor Local Factor (one prime, one case)

```scala
// DRAFT — not yet verified through Stainless
// Illustrates the p | W, p ∤ Z case of the local table: p - 1 allowed classes.
def localFactorCase_PW_not_PZ(p: BigInt): Boolean = {
  require(p >= 3)
  // gcd(m, W) = 1 makes m invertible mod p; forbidding k = 0 leaves p - 1 classes.
  // DRAFT: full theorem quantifies over squarefree W, Z, m — likely needs a
  // finite-wheel specialization to fit Stainless. See Open Concerns.
  (p - 1) >= 2
}.holds
```

### χ₃ Refutation (the scalar-density counterexample)

```scala
// DRAFT — not yet verified through Stainless
// On W = 30, Z = 6: chi_3(mn) = -1 for every accepted pair, so the centered
// correlation equals the full survivor count. Concrete finite check.
def assertChi3CounterexampleOnWheel30: Boolean = {
  val residues = List[BigInt](1, 7, 11, 13, 17, 19, 23, 29) // (Z/30Z)^x, 8 units
  // accepted pairs (mn, mn+2 coprime to 6): mn = 2 mod 3 forced; count them.
  // DRAFT: a verified finite enumeration. The claim is that the signed sum
  // over accepted pairs equals -|accepted pairs| and the scalar sum is 0.
  val nUnits = residues.length
  // TODO: enumerate accepted ordered pairs and assert the two correlations.
  nUnits == 8
}.holds
```

### , #25/#66, #82 chain consequence, #83 relative input

No draft provided. These either depend on Bertrand / prime-counting (#6),
an open abundance antecedent (#7), a weighted Cauchy-Schwarz chain over a
variable-length filter list (#25/#66), an external prime-AP theorem (#86),
or an unproved relative residue-energy bound (#83). They are recorded as
expected documented obstacles, not as near-term verification targets.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-03 | Reviewer noted the two new articles defer Scala (form 3) via the §9 weaker option throughout; finished articles inline 3–29 real `.holds` blocks. Decision: capture draft Scala in this ticket, leave articles unchanged for now. | Create this ticket; record the finite-algebra drafts above; do not edit articles until a draft is actually verified. |
