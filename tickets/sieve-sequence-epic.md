# Spec / Canonical / Cycle — Design Overview

**Status:** Living document. Bird's-eye view of the three-way sieve
equivalence effort, traced down to individual tickets and verified lemmas.
**Created:** 2026-06-24. **Last updated:** 2026-07-04.
**Maintained alongside:** `active/sieve-sequence-proof.md` (the canonical
active sieve-sequence proof ticket). Historical Leg-2 notes live in
`done/canonical-spec-to-cycle-alignment.md`.

> This document is the coordination point. Individual legs live in their own
> tickets; this file explains how they fit together and what is proven today.

**Current verification:** `12138 valid: 12138 invalid: 0 unknown: 0` (was 9373 at creation, +14 from P2/nextFromWindow,
+1042 from P2 full, +756 from value-level survivor proofs).

---

## 1. The Three Representations

The project models one sieve stage in three ways. They differ in *how* they
generate the stream of survivor values, not in *which* values they generate.

| Representation                          | File                                                | Generates values by                                                                                                                                                                                                       |
|-----------------------------------------|-----------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| **Spec** (`SpecSieveSequence`)          | `v1/chapter6/seq/sieve/SpecSieveSequence.scala`     | **Linear scan** of consecutive naturals, keeping those coprime to the tail primes. The mathematical source of truth.                                                                                                      |
| **Canonical** (`SpecDerivedCycleSieve`) | `v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala` | An *intermediate representation*. Built **from** a Spec stage; extracts Spec's certified prime list and gap cycle into a `CycleSieveSequence`. Owns all Spec↔Cycle correspondence lemmas. **Allowed to use Spec freely.** |
| **Cycle** (`CycleSieveSequence`)        | `v1/chapter6/seq/sieve/CycleSieveSequence.scala`    | **Cycle arithmetic** — a stored `GapCycle` replayed through `CycleIntegral`. The optimized implementation. Carries only its own structural invariants; **no link to Spec**.                                               |

### Why three, not two

A raw `CycleSieveSequence` constructor can enforce local structural facts
(non-empty primes, positive gaps, head coprimality), but it **cannot** enforce
by type alone the semantic fact "this gap cycle is exactly the sieve gap cycle
for this prime list." Canonical bridges that gap: it is *constructed from*
Spec's own certified gaps, so its correctness reduces to Spec's, and the Cycle
view it produces is correct by construction.

### ⚠️ What "equivalence" means — and what it does NOT

**Equivalence is structural identity of the generated stream, nothing more:**

```
cycle.head   == spec.head.value
cycle.gaps   == spec.gaps            (the stored gap cycle values)
cycle.apply  == spec.apply           (pointwise, for every k >= 0)
```

If those three hold, the cycle **is** the spec stream. `assertApplyMatches` is
in fact *derived from* the head + gap equalities (head + gaps ⇒ apply, by
unfolding the `CycleIntegral`).

**Equivalence does NOT require knowing the head is prime.** Primality matters
for whether the stream is *sieve-correct* (does it actually enumerate primes?),
but it is irrelevant to whether `cycle ≡ spec`. Do **not** drag primality into
the equivalence proof — it adds cost without load-bearing value. (Scoping
principle, user 2026-06-24: cycle rules carry only what the equivalence check
requires.)

**⚠️ GUARDRAIL for future agents — do NOT try to prove sieve-correctness
inside the cycle.** The hard, walk-opaque territory is
`CycleSieveSequence.next()` (which calls `nextGapsWalk`). Three prior attempts
to prove `nextGapsWalk(cycle) == spec.next.gapList(...)` timed out and were
commented out (see §5). The structural-identity equalities above are proven
**at construction** (`SpecDerivedCycleSieve(spec, period).cycle` vs `spec`); they
are **not** proven to be preserved by `cycle.next()`. If you find yourself
trying to prove `cycle.next()(k) == spec.next(k)` by reasoning *inside* the
walk, **STOP** — that is the deferred open hole (§5, Lemma 5), not something
to improvise. Use the Leg-3 cycle rules (§4) as the certified ingredients
instead, and surface the gap to the user rather than burning attempts.

---

## 2. The EPIC — a Three-Way Connection

```
   Spec (correct)
      |
      |  Leg 2: cycle(k) == spec(k) for all k           [DONE: assertApplyMatches]
      v
   Canonical (SpecDerivedCycleSieve)
      |
      |  Leg 3: canonical next exists and matches        [DONE: assertNextCycle*]
      |         spec.next by construction
      v
   SpecDerivedCycleSieve(spec.next, nextPeriod)            [by construction]
      |
      |  Leg 4a: survivor gaps == spec.next gaps          [DONE: P2 lemmas]
      |         (using position-based lemmas,
      |          NOT the walk)
      v
   Survivor-derived next stage                            [verified equivalent]
      |
      |  Leg 4b: nextGapsWalk equals either              [PARTIAL: P2 provides
      |         survivor-derived gaps or spec.next gaps    certified alternative]
      v
   CycleSieveSequence.next()                             [walk-backed]
      |
      |  Leg 5: CycleSieveSequence == Canonical,          [FUTURE]
      |         using ONLY Cycle's structural rules
      v
   CycleSieveSequence (correct by transitivity, no Spec link)
```

| Leg | Statement                                                                                   | Status         | Owner                                                                                                     |
|-----|---------------------------------------------------------------------------------------------|----------------|-----------------------------------------------------------------------------------------------------------|
| 1   | Spec is correct                                                                             | ✅ Done         | `SpecSieveSequence`                                                                                       |
| 2   | Canonical ≡ Spec (current stage): `cycle(k) == spec(k)` ∀k                                  | ✅ Done         | `SpecDerivedCycleSieve.assertApplyMatches`                                                                |
| 3   | The canonical next cycle built from `spec.next` matches `spec.next`                         | ✅ Done         | `SpecDerivedCycleSieve` (see §4)                                                                          |
| 4a  | Survivor-derived next gaps = spec.next gaps (per-index, walk-free)                          | ✅ Done         | `assertSurvivorGapEqualsSpecNextGap`, `assertSpecNextIsKthSurvivor`, `assertFirstSurvivorEqualsSpecNext0` |
| 4b  | `CycleSieveSequence.nextFromWindow()` — verified method using transparent window + requires | ✅ Done (14/14) | `CycleSieveSequence.nextFromWindow()` + P2 lemmas                                                         |
| 5   | `CycleSieveSequence` ≡ Canonical, using **only** Cycle's structural rules (no Spec)         | Future         | (future ticket)                                                                                           |

### P2 Breakthrough + Verified Next (2026-06-27/29)

Three verified lemmas that close Leg 4a — the gap equality between cycle survivors and spec.next — **without unfolding
the walk**:

| Lemma                                               | VCs   | What it proves                                                                       |
|-----------------------------------------------------|-------|--------------------------------------------------------------------------------------|
| `assertFirstSurvivorEqualsSpecNext0`                | 7/7   | `cycle.integral(0) == spec.next(0)` — head match                                     |
| `assertSurvivorGapEqualsSpecNextGap(nextPeriod, i)` | 53/53 | `spec.next(i+1)-spec.next(i) == cycle(pos_{i+1})-cycle(pos_i)` — gap match per index |
| `assertSpecNextIsKthSurvivor(nextPeriod, k)`        | 29/29 | `spec.next(k) == cycle(indexOfAccepted(spec.next(k)))` — survivor position match     |

These proofs avoid `survivorValues`, `specGapCycle`, and `nextGapsWalk` entirely. They work through **position-based
lemmas** (`indexOfAccepted`, `assertApplyMatches`, `assertNextGapEqualsCurrentGapSum`), which are lightweight and
cached.

Two additional structural additions:

| Lemma                                  | VCs   | What it proves                                                                    |
|----------------------------------------|-------|-----------------------------------------------------------------------------------|
| `assertFilterMergeComposition`         | 34/34 | A `CycleIntegral` built from survivors has no multiples of the filter prime       |
| `assertFullEquivalence(nextPeriod, k)` | 13/13 | `cycle(k)==spec(k) ∧ cycle(1)==spec.next.head.value` — top-level packaged theorem |

### Transparent Window Helpers

Two list-based helpers that expose the cycle's data as plain `List[BigInt]`, enabling list-induction proofs instead of
cycle reasoning:

| Helper                  | Purpose                                                                      |
|-------------------------|------------------------------------------------------------------------------|
| `currentWindow(steps)`  | `List[BigInt]` of `cycle.integral(0..steps-1)` — transparent recursion (6/6) |
| `survivorWindow(steps)` | Filtered window (non-multiples of head)                                      |

These provide a proof-friendly middle representation: instead of reasoning through `MemCycle`/`CycleIntegral` opacity,
lemmas can induct over the plain `List[BigInt]`. Future Leg-4b work could use `survivorWindow` to prove the walk matches
the survivor list element-by-element.

### ⚠️ Remaining open: the walk itself

The `nextGapsWalk` function is still opaque. Three prior direct attempts timed out (see §5 legacy notes). The P2 lemmas
provide a **certified alternative**: the survivor computation produces the correct gaps. The walk correctness is now a
bridge between the walk and the certified survivor computation, not a proof from scratch.

### New: Value-level survivor proofs (`SpecDerivedBySurvivors`)

A new class `SpecDerivedBySurvivors` wraps `SpecDerivedSieveSequence` and provides an
alternative value-level proof chain that avoids the index-based `nextAcceptedOldIndex`
machinery. It proves (2026-07-04):

| Lemma                                          | VCs | Statement                                                | Approach                                      |
|------------------------------------------------|-----|----------------------------------------------------------|-----------------------------------------------|
| `assertCycleSurvivorPassesSpecNextFilter(pos)` | 8   | Survivor `integral(pos)` passes `spec.next.passesFilter` | Coprimality chain, no `>=` precondition       |
| `assertSurvivorAcceptedBySpecNext(pos)`        | 12  | Survivor accepted by `spec.next.accepts`                 | `passesFilter` + monotonicity bridge          |
| `assertIntegralGeIntegral0(pos)`               | 20  | `integral(pos) >= integral(0)`                           | Induction via `assertCycleValuePositive`      |
| `assertNextHeadLessThanNewModulus()`           | 9   | `cycle(1) < head * modulus`                              | `spec.apply.ensuring` + Z3 arithmetic         |
| `assertNextHeadLessThanHeadSquared()`          | 3   | `cycle(1) < head^2`                                      | Constructor require + `assertNextHeadMatches` |

12 lemmas total (all verified). The F5 timeout wall (integral monotonicity) was climbed
by using existing `CycleIntegralProperties.assertCycleValuePositive` +
`GapCycle.assertMemCycleValuesPositive` as intermediate lemmas — 3 attempts, final
success in 11.53s. The rotation-proxy inequality `cycle(1) < head * modulus` was also
unblocked (3 attempts: naive induction timed out, intermediate bound timed out,
`spec.apply.ensuring` + Z3 arithmetic succeeded).

A bridge class `SpecDerivedEquivalence` (4 lemmas) proves both derived classes share
the same `cycle`, `apply(k)`, `gapCycle`, and head/modulus — certifying that proofs
from either class transfer to the other.

### Architectural rule (confirmed with user, 2026-06-24)

- **SpecDerivedCycleSieve** is built around Spec by definition and may use Spec freely.
- The "walks with its own legs" / "no Spec link" constraint applies to
  **`CycleSieveSequence`** (Leg 5) only. Leg 4 may still use SpecDerived/Spec
  facts because its job is to certify the concrete survival walk against the
  canonical specification.

---

## 3. Key Proof Idioms in the Codebase

The project has accumulated several distinct verified patterns for reasoning
about cycles. Leg 3 deliberately reused these rather than inventing new ones.

| Idiom                              | Source                                                                                  | When it applies                                                                                                                                                           |
|------------------------------------|-----------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| **Transfer through equivalence**   | `assertApplyMatches` + a Spec lemma                                                     | When Canonical needs a fact Spec already proved. Call the Spec lemma, rewrite `spec.apply(i)` → `cycle(i)` at the relevant positions. **This is the workhorse of Leg 3.** |
| **Diff-based induction**           | `ClassicCycleIntegralProperties.assertDiffEqualsCycleValue`, `assertSameDiffAfterCycle` | Reasoning about `integral(k+1) - integral(k) == cycle(k+1)`; periodic via `MemCycleProperties.valueMatchAfterManyLoopsInBoth`.                                            |
| **`indexOfAccepted` substitution** | `SpecSieveSequence.indexOfAccepted` (with `.ensuring`)                                  | Avoiding positional scans; cached postconditions give `spec(res) == value` directly. Used by `assertNextGapEqualsCurrentGapSum`.                                          |
| **Walk / `collectGaps`**           | `SieveSequenceNextLevel.nextGapsWalk`                                                   | ❌ **Avoid.** Timed out 3× — diff depends on `lastSurvivor` (all previous positions), so Stainless treats the walk as opaque from outside `.holds`.                        |

---

## 4. Leg 3 — The Cycle Rule List (COMPLETE)

**Goal:** a set of rules, each stated purely over `canonical.cycle`, that
together define how the next stage's head and gaps are derived from the
current cycle's own data. Proofs may use Spec; **conclusions reference only
`cycle`**.

**Scoping principle (user, 2026-06-24):** cycle rules carry **only what the
equivalence check requires**, not everything that is true. E.g. the next head
is in fact prime, but the cycle does not need to know that — so "head is prime"
is excluded from the rule list.

### Verified rules (all green, `10572 valid` as of 2026-06-29)

| Rule                    | Lemma                                                                         | Statement over `cycle`                                                                              |
|-------------------------|-------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------|
| **Next head**           | `assertNextHeadMatches`                                                       | `cycle(1) == spec.next.head.value`                                                                  |
| **Gap positivity**      | `assertGapPositiveMatchesSpec`                                                | `cycle(k+1) - cycle(k) > 0`                                                                         |
| **Gap periodicity**     | `assertGapPeriodicMatchesSpec`                                                | `cycle(period+k+1) - cycle(period+k) == cycle(k+1) - cycle(k)`                                      |
| **Period sum**          | `assertNextFilterModulusRelation`                                             | `spec.next.tailPrimorial == cycle.head * spec.tailPrimorial`                                        |
| **Copy rule**           | `assertCopyGapMatchesSpec`                                                    | if `cycle(k)`, `cycle(k+1)` both not multiples of `cycle.head` → next gap = `cycle(k+1) - cycle(k)` |
| **Merge rule (accept)** | `assertCurrentNonMultipleAcceptedByNext` + `assertNextGapEqualsCurrentGapSum` | non-multiple of `cycle.head` → value accepted by next; merged gap = sum of current gaps             |
| **Merge rule (reject)** | `assertCurrentMultipleRejectedByNext`                                         | multiple of `cycle.head` → value rejected by next                                                   |
| **Gap list equality**   | `nextGapList` + `assertNextGapListMatchesSpecNext`                            | `nextGapList(from, count) == spec.next.gapList(from, count)`                                        |
| **Per-position gap**    | `assertNextGapAtMatchesSpecNext`                                              | `spec.next(i+1) - spec.next(i) == spec.next.gapList(0, nextPeriod).apply(i)`                        |
| **Ordering**            | `assertCurrentValueAtOrAboveNextHead`                                         | `k >= 1` ⇒ `spec(k) >= spec.next.head.value`                                                        |

### P2 rules added in 2026-06-27

| Rule                        | Lemma                                               | Statement over `cycle`                                                                                       |
|-----------------------------|-----------------------------------------------------|--------------------------------------------------------------------------------------------------------------|
| **Survivor head match**     | `assertFirstSurvivorEqualsSpecNext0`                | `cycle.integral(0) == spec.next(0)`                                                                          |
| **Survivor gap match**      | `assertSurvivorGapEqualsSpecNextGap(nextPeriod, i)` | `spec.next(i+1)-spec.next(i) == cycle(pos_{i+1})-cycle(pos_i)` where `pos_i = indexOfAccepted(spec.next(i))` |
| **Survivor position match** | `assertSpecNextIsKthSurvivor(nextPeriod, k)`        | `spec.next(k) == cycle(indexOfAccepted(spec.next(k)))`                                                       |
| **Filter composition**      | `assertFilterMergeComposition`                      | New CI from `survivors` has no multiples of `cycle.head`                                                     |
| **Full equivalence**        | `assertFullEquivalence(nextPeriod, k)`              | `cycle(k)==spec(k) ∧ cycle(1)==spec.next.head.value`                                                         |
| **Transparent window**      | `currentWindow(steps)`                              | `List[BigInt]` of `cycle.integral(0..steps-1)`                                                               |
| **Transparent survivor**    | `survivorWindow(steps)`                             | `currentWindow(steps).filter(v ⇒ v mod head ≠ 0)`                                                            |

### Hard-won lessons from Leg 3 (candidates for `LEARNINGS.md`)

1. **Transfer beats re-derivation.** When a property is proven on Spec and
   Canonical is proven equivalent index-by-index, the transfer is mechanical
   (call + rewrite). Do NOT re-derive the property from scratch on the cycle
   side.
2. **`val nextSeq = spec.next` aliases cause timeouts.** Confirmed by an
   isolation test: the alias alone blocks the solver from connecting cached
   `.holds` results to the local variable. Use `spec.next` directly.
3. **Isolate ordering facts.** `spec(k) >= spec.next.head.value` combined
   inside a larger coprimality VC times out; exported through its own small
   lemma (`assertCurrentValueAtOrAboveNextHead`) it is cheap and stable.
4. **Forward-order builders.** When proving `myBuilder == specBuilder` by
   induction, sanity-check the builder order on paper first. A reversed
   builder is unprovable and surfaces as a timeout, not a counterexample.
5. **Sliding-window induction** over `from` (recurse with `from + 1`) beats
   fixed-`from` induction over `count` — keeps preconditions local at each step.

---

## 5. Leg 2 — Canonical Construction (current stage)

**Goal:** prove `cycle(k) == spec(k)` for all `k >= 0`.

| Lemma                                                               | Statement                                                                    | Status                                                           |
|---------------------------------------------------------------------|------------------------------------------------------------------------------|------------------------------------------------------------------|
| `cycle` (constructor)                                               | Extracts `PrimeUtils.primeValues(spec.primes)` + `spec.specGapCycle(period)` | ✅                                                                |
| `assertApplyMatches(k)`                                             | `cycle(k) == spec(k)` ∀k                                                     | ✅                                                                |
| `assertHeadMatches` / `assertPrimesMatch` / `assertGapCycleMatches` | structural aliases                                                           | ✅                                                                |
| `assertNextAcceptsMatches(value)`                                   | `spec.next.accepts(v) == isCoprime(v, cycle.primes)`                         | ✅                                                                |
| `assertNextPrimesMatch`                                             | next prime list correspondence                                               | ✅                                                                |
| `assertWalkDecisionMatchesNextAccept(k)`                            | walk keep/skip == next acceptance                                            | ✅                                                                |
| `assertNextValueMatchesCyclePosition(k)`                            | value-level next-stage correspondence                                        | ✅                                                                |
| **Lemma 5** (walk equality `nextGapsWalk == spec.next.gapList`)     | —                                                                            | ❌ Deferred (3 timeouts); superseded by Leg 3's transfer approach |

**Constructor caveats still carried explicitly:**

- `spec.primes.nextPrime.value < spec.head.value * spec.head.value` (the
  "prime before p²" wall, tracked in `prove-apply1-is-prime.md`).
- `Calc.mod(SieveUtils.product(filterValues), head.value) != 0` (tracked in
  `primorial-not-divisible-by-new-prime.md`).

---

## 6. Leg 5 — Cycle ≡ Canonical (FUTURE)

**Goal:** prove `CycleSieveSequence.apply(k) == SpecDerivedCycleSieve(spec, period).cycle.apply(k)`
using **only** `CycleSieveSequence`'s structural invariants — no reference to
Spec whatsoever.

This is the leg that makes the optimized Cycle implementation correct *on its
own terms*. Once Leg 5 is done, the full chain Spec → Canonical → Cycle is
closed, and `CycleSieveSequence` can be trusted without re-proving anything
against the linear scan.

**No ticket exists yet.** Open scoping questions:

- Which of `CycleSieveSequence`'s constructor `require`s are sufficient to
  carry the Leg-4 proof?
- Does Leg 5 need the Leg-3 cycle rules (positivity, periodicity, copy, merge)
  as hypotheses, or can it re-derive them from Cycle's structural invariants
  alone?

---

## 7. Out-of-Scope / Tracked Elsewhere

| Item                                         | Where                                                                                            |
|----------------------------------------------|--------------------------------------------------------------------------------------------------|
| "Prime between p and p²" (Bertrand-style)    | `blocked/prove-apply1-is-prime.md` — undischarged wall (LEARNINGS 10.1)                          |
| Product not divisible by head                | `blocked/primorial-not-divisible-by-new-prime.md` — Euclid's lemma wall (LEARNINGS 10.2)         |
| Gap property landscape (24+ properties)      | `active/sieve-property-landscape.md` — catalogues proved, provable, and open twin-gap properties |
| Forbidden states / dead configurations       | `active/sieve-property-landscape.md` §"Forbidden States" — monotonic exclusion theorem           |
| Old `CycleSieveSequence.next` / walk framing | `superseded/remove-extern-from-next.md`                                                          |
| Old Spec/Cycle equivalence plan              | `superseded/v0-v2-apply-equivalence.md`                                                          |
| Failed walk-based pipeline (do not revive)   | `superseded/walk-based-pipeline.md`                                                              |

---

## 8. Rule-Compliance Notes for Future Work

This effort is governed by `AGENTS.md`. The rules most load-bearing for this
design:

- **`green-to-green`** — check `verify.log` before any change; verify after.
  Current green: `9373 valid: 9373 invalid: 0 unknown: 0`.
- **`small-changes`** — one lemma/assertion per verify cycle. Leg 3's
  progress came from many tiny verified steps, not large proofs.
- **`stop-and-ask`** — 3 failed attempts → stop. Several Leg-3 lemmas hit
  this (copy rule acceptance transfer) and were unblocked only by isolating
  the failing fact into its own small lemma.
- **`never-destroy`** — failed lemmas are commented out, never deleted.
  `SpecDerivedCycleSieve.scala` retains commented-out records of timed-out
  attempts as proof logs.
- **`stay-on-track`** — the 3-way architecture and the Leg boundaries are
  fixed; do not fold Leg 4 into Leg 3, or Leg 5 into Leg 4, unless the user
  explicitly changes the architecture.

---

## Update Log

### 2026-06-24 — Document created

Bird's-eye design doc consolidating the 3-way Spec/Canonical/Cycle
architecture. Reflects the verified state as of Leg 3 completion (`9373 valid`).
Traces the EPIC (§2) down to per-lemma status (§4, §5) and records the
load-bearing proof idioms (§3) and lessons (§4) accumulated across Legs 2–3.
Leg 5 is documented as future work with open scoping questions.

### 2026-06-29 — P2 breakthrough, transparent window, property landscape

Major updates:

- **Verification count**: `9373 → 10572` (+1199)
- **Leg 4a (survivor gaps)**: ✅ DONE via P2 lemmas:
  `assertSurvivorGapEqualsSpecNextGap` (53/53),
  `assertSpecNextIsKthSurvivor` (29/29),
  `assertFirstSurvivorEqualsSpecNext0` (7/7)
- **Filter composition**: `assertFilterMergeComposition` (34/34)
- **Top-level theorem**: `assertFullEquivalence` (13/13)
- **Transparent window**: `currentWindow`, `survivorWindow` added as plain-list bridges
- **New ticket**: `active/sieve-property-landscape.md` — catalogues 24+ properties
  (proved, likely provable, open) including the Forbidden States hypothesis
- **Leg 4b** (walk itself) remains the only open item in the EPIC; the P2 lemmas
  provide a certified alternative path that bypasses the walk

### 2026-07-04 — Value-level survivor proofs, F5 timeout climbed

Major additions:

- **Verification count**: `10572 → 12114` (+1542)
- **New class**: `SpecDerivedBySurvivors` — wraps `SpecDerivedSieveSequence`, proves survivor filter-passing and
  acceptance via value-level coprimality chains (10 lemmas, all verified)
- **F5 timeout climbed**: `assertIntegralIncreasingForCount` (14/14 in 11.53s) by using existing
  `assertCycleValuePositive` + `GapCycle.assertMemCycleValuesPositive` as intermediate lemmas (3 attempts: naive
  induction timed out, intermediate lemma timed out, existing-lemmas succeeded)
- **Architectural update**: `passesFilter` → `accepts` bridge now proven — survivors satisfy `>= head.value`
  precondition via monotonicity induction, connecting value-level proofs to index-based lemmas
- New ticket: `active/spec-derived-by-survivors.md`
- OBJECTS.md §6.9: new section with 10 lemmas, ch6 count updated
