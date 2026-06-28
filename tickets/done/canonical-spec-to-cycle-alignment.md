# Canonical Spec-to-Cycle Alignment

**Status:** Active, migrating verified bridges into an intermediate representation
**Created:** 2026-06-23
**Umbrella design doc:** [`../spec-canonical-cycle-design.md`](../spec-canonical-cycle-design.md)
**Related:**
- `tickets/active/v0-v2-apply-equivalence.md`
- `tickets/done/v0-gap-list-cycle-formalization.md`
- `tickets/active/remove-extern-from-next.md`

## Goal

Create and verify a canonical path from `SpecSieveSequence` to
`CycleSieveSequence`:

```scala
spec.toCycle(period): CycleSieveSequence
```

where the returned cycle sequence is constructed from Spec's own certified gap
cycle and is therefore behaviorally identical to the Spec sequence for the same
stage.

Then prove the recursive alignment theorem:

```text
if cycle == spec.toCycle(period)
then cycle.next() aligns with spec.next.toCycle(nextPeriod)
```

In plain terms: if the Spec and Cycle views are aligned now, their `next` stages
walk together too.

## Motivation

The current `v0-v2-apply-equivalence.md` strategy tries to prove that an
arbitrary or independently produced `CycleSieveSequence` matches
`SpecSieveSequence`. That is a very strong theorem, but it forces every proof to
carry a large semantic invariant:

```text
this gap cycle is exactly the sieve gap cycle for this prime list
```

A raw `CycleSieveSequence` constructor can enforce local structural facts, such
as non-empty primes and positive gaps, but it cannot enforce that semantic
invariant by type alone. Incorrect cycles can be constructed by supplying gaps
with the wrong alignment or a head that skips a prime.

This ticket narrows the verified API to the canonical construction:

```text
Spec is the source of truth.
Spec builds the Cycle view from its own proved gaps.
The Cycle view is proved behavior-identical to Spec.
The next Cycle view is proved to stay aligned with Spec.next.
```

This is weaker than proving every possible `CycleSieveSequence` is correct, but
it is a sound restriction. The project only needs the canonical path to generate
stable verified stages.

## Key Distinction From Full Equivalence

Full implementation equivalence asks:

```text
for any valid CycleSieveSequence,
Cycle.next() == Spec.next
```

This ticket asks:

```text
for the CycleSieveSequence built by spec.toCycle(period),
cycle.next() == spec.next.toCycle(nextPeriod)
```

The second theorem is narrower and should be more Stainless-friendly because
the proof can unfold the construction:

```text
cycle.head == spec.head.value
cycle.primes == PrimeUtils.primeValues(spec.primes.list.list)
cycle.gapCycle == spec.specGapCycle(period)
cycle(k) == spec(k)
```

## Proposed API

## Architecture Decision: Intermediate Canonical Representation

The canonical conversion and alignment lemmas must not live on
`SpecSieveSequence`. That class is the mathematical source of truth and should
remain isolated from the optimized Cycle representation.

The accepted ownership split is:

```text
SpecSieveSequence
  owns the linear specification, accepted values, gaps, and Spec proofs.

CycleSieveSequence
  owns generic cycle mechanics and invariants intrinsic to every valid cycle.

CanonicalCycleSieve
  receives a SpecSieveSequence, extracts the canonical Cycle representation,
  and owns every Spec/Cycle correspondence lemma.
```

Proposed intermediate representation:

```scala
case class CanonicalCycleSieve(
  spec: SpecSieveSequence,
  period: BigInt
) {
  require(period > 0)
  require(spec(period) == spec.head.value + spec.filterModulus)
  require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
  require(
    Calc.mod(
      SieveUtils.product(spec.filterValues),
      spec.head.value
    ) != 0
  )

  val cycle: CycleSieveSequence = ...
}
```

The bridge may call public Spec lemmas, but Spec must not import, construct, or
mention `CycleSieveSequence`.

### Migration Order

1. Expose only the existing Spec proof utility needed to reconstruct its gap
   cycle behavior; do not move Cycle knowledge into that utility.
2. Add `CanonicalCycleSieve` with the canonical construction.
3. Move canonical head, prime-list, gap-cycle, apply, next-head,
   next-acceptance, and next-prime-list lemmas into the bridge.
4. Retire the corresponding methods from `SpecSieveSequence` without changing
   the underlying Spec lemmas.
5. Update `OBJECTS.md` and ticket references to the new owner.

### Validation

- Use `just verify functionName` while iterating on each moved proof.
- Run full `just verify` after each accepted code change, as required by
  `AGENTS.md`.
- The migration is complete only when `SpecSieveSequence.scala` has no
  `CycleSieveSequence` construction or canonical alignment methods.

### Option A: Method On `SpecSieveSequence`

```scala
def toCycle(period: BigInt): CycleSieveSequence = {
  require(period > 0)
  require(apply(period) == head.value + filterModulus)

  CycleSieveSequence(
    PrimeUtils.primeValues(primes.list.list),
    specGapCycle(period)
  )
}
```

### Option B: Wrapper Object

```scala
case class CanonicalCycleSieve(
  spec: SpecSieveSequence,
  period: BigInt
) {
  require(period > 0)
  require(spec(period) == spec.head.value + spec.filterModulus)

  val cycle: CycleSieveSequence = spec.toCycle(period)
}
```

**Superseded recommendation:** Option A was useful for proving feasibility, but
it mixed the mathematical specification with the optimized representation.
The current recommendation is the intermediate `CanonicalCycleSieve` described
above.

## Required Lemmas

### 1. Canonical Cycle Construction

```scala
def toCycle(period: BigInt): CycleSieveSequence
```

**Statement:** Given a valid Spec period anchor,
`toCycle(period)` constructs a `CycleSieveSequence` whose prime list and gap
cycle are exactly the Spec-derived values.

Expected postconditions or follow-up aliases:

```text
toCycle(period).head == spec.head.value
toCycle(period).primes == PrimeUtils.primeValues(spec.primes.list.list)
toCycle(period).gapCycle.memCycle == spec.specGapCycle(period).memCycle
```

**Known dependencies:**
- `SpecSieveSequence.specGapCycle(period)`
- `PrimeUtils.primeValues(...)`
- `CycleSieveSequence` constructor requirements

**Estimated complexity:** Low to medium.

**Progress 2026-06-23:** Verified as
`SpecSieveSequence.toCycle(period)`.

The implemented method builds:

```scala
CycleSieveSequence(
  PrimeUtils.primeValues(primes.list.list),
  specGapCycle(period)
)
```

and proves the constructor obligations from existing Spec facts where possible.
It intentionally carries two conditional requirements needed by the current
`CycleSieveSequence` constructor:

```text
primes.nextPrime.value < head.value * head.value
Calc.mod(SieveUtils.product(filterValues), head.value) != 0
```

The first is the same square-bound assumption used by `SpecSieveSequence.next`.
The second is still tracked by the product-not-divisible work and should not be
hidden; it is the remaining constructor-side caveat for canonical cycle
creation.

Validation: `just verify` passed with `8696 valid`, `0 invalid`, `0 unknown`.

### 2. Canonical Apply Equality

```scala
def assertToCycleApplyMatches(period: BigInt, k: BigInt): Boolean
```

**Statement:**

```text
k >= 0
period > 0
spec(period) == spec.head.value + spec.filterModulus
  ==> spec.toCycle(period)(k) == spec(k)
```

**Why needed:** This proves that the canonical cycle view is not merely
structurally similar to Spec; it generates the same infinite stream.

**Known dependencies:**
- `SpecSieveSequence.assertSpecGapCycleIntegralMatchesApply(period, k)`
- `SpecCycleSieveEquivalence.assertSpecCycleApplyMatchesFromSameHeadAndGaps`
  may be reusable, but a direct proof inside `SpecSieveSequence` may be simpler
  because `toCycle(period)` unfolds to the exact Spec-derived gap cycle.

**Estimated complexity:** Low to medium. This should mostly consume already
verified gap-cycle reconstruction lemmas.

**Progress 2026-06-23:** Verified as
`SpecSieveSequence.assertToCycleApplyMatches(period, k)`.

The proof splits on `k == 0`:

- for `k == 0`, both sequences return the same head;
- for `k > 0`, the canonical cycle apply unfolds through
  `CycleIntegral(head.value, specGapCycle(period).memCycle)(k - 1)`, then
  reuses `assertSpecGapCycleIntegralMatchesApply(period, k)`.

This gives the first behavior-level bridge for the canonical strategy:

```text
spec.toCycle(period)(k) == spec(k)
```

Validation: `just verify` passed with `8720 valid`, `0 invalid`, `0 unknown`.

### 3. Canonical Next Head Equality

```scala
def assertToCycleNextHeadMatchesSpecNext(period: BigInt): Boolean
```

**Statement:**

```text
spec.toCycle(period)(1) == spec.next.head.value
```

under the existing Spec next assumptions, likely including:

```text
spec.primes.nextPrime.value < spec.head.value * spec.head.value
```

**Why needed:** `CycleSieveSequence.next()` uses `cycle(1)` as its new head.
To prove the next stages walk together, we must align that value with
`spec.next.head.value`.

**Known dependencies:**
- `assertToCycleApplyMatches(period, 1)`
- Spec-side fact that `spec(1) == spec.next.head.value`, or an alias exposing
  the already verified next-prime bridge.

**Estimated complexity:** Medium. The hard part is not the cycle side; it is
exposing the Spec-side `spec(1) == spec.next.head.value` fact cleanly.

**Progress 2026-06-23:** Verified as
`SpecSieveSequence.assertToCycleNextHeadMatchesSpecNext(period)`.

The proof composes:

```text
spec.toCycle(period)(1) == spec(1)
spec(1) == spec.primes.nextPrime.value
spec.next.head.value == spec.primes.nextPrime.value
```

This confirms the canonical Cycle next stage starts from the same head as
`SpecSieveSequence.next`.

Validation: `just verify` passed with `8746 valid`, `0 invalid`, `0 unknown`.

### 4. Canonical Next Acceptance Equality

```scala
def assertToCycleNextAcceptsMatchesSpecNext(
  period: BigInt,
  value: BigInt
): Boolean
```

**Statement:**

```text
spec.next.accepts(value)
  == SieveUtils.isCoprime(value, spec.toCycle(period).primes)
```

with the usual lower-bound requirement on `value`.

**Why needed:** The next gap walk accepts/skips values based on the next Cycle
filters. Spec.next accepts/skips values based on its own filter list. This lemma
is the semantic bridge showing both walks make the same skip decisions.

Note: the full next Cycle prime list is
`spec.toCycle(period)(1) :: spec.toCycle(period).primes`, but the active filter
tail for that next stage is the old `spec.toCycle(period).primes`. The
acceptance predicate is therefore stated over the tail filters.

**Known dependencies:**
- `assertToCycleNextHeadMatchesSpecNext`
- `SpecCycleSieveEquivalence.assertSpecAcceptsMatchesCycleTailCoprime`
- raw-prime-list correspondence from `toCycle(period)`

**Estimated complexity:** Medium.

**Progress 2026-06-24:** Verified as
`SpecSieveSequence.assertToCycleNextAcceptsMatchesSpecNext(period, value)`.

The proof exposes that:

```text
spec.next.filterValues == PrimeUtils.primeValues(spec.primes.list.list)
spec.toCycle(period).primes == PrimeUtils.primeValues(spec.primes.list.list)
```

so both predicates inspect the same divisor list.

Validation: `just verify` passed with `8769 valid`, `0 invalid`, `0 unknown`.

### 5. Canonical Next Gap Walk Equals Spec Next Gap List

```scala
def assertToCycleNextGapsMatchSpecNext(
  period: BigInt,
  nextPeriod: BigInt
): Boolean
```

**Statement:**

```text
SieveSequenceNextLevel.nextGapsWalk(spec.toCycle(period))
  == spec.next.gapList(0, nextPeriod)
```

under:

```text
period > 0
spec(period) == spec.head.value + spec.filterModulus
nextPeriod > 0
spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus
spec.primes.nextPrime.value < spec.head.value * spec.head.value
```

**Why needed:** This is the central producer theorem. Once it is proven, the
annoying `CycleSieveSequence.next()` preconditions become derivable from
Spec-side gap-list validity instead of being carried as mysterious assumptions.

**Expected proof shape:**

1. Let `cycle = spec.toCycle(period)`.
2. Use `assertToCycleApplyMatches` so the Cycle walk sees the same current
   values as Spec.
3. Use next-head equality so both paths start the next stage at the same value.
4. Use next-acceptance equality so both paths skip and keep the same values.
5. Recurse over the gap collection and Spec gap list.

**Estimated complexity:** High. This is the main hard theorem, but it is more
focused than proving equivalence for arbitrary Cycle states.

### 6. Canonical Next Requirements

```scala
def assertToCycleNextRequirements(period: BigInt, nextPeriod: BigInt): Boolean
```

**Statement:** The concrete `newGaps` used by `spec.toCycle(period).next()`
satisfy the requirements currently exposed by `CycleSieveSequence.next()`:

```text
newGaps.nonEmpty
ListBoundUtils.allGreaterThan(newGaps, 0)
SieveUtils.isCoprime(newHead + newGapCycle.memCycle(0), oldPrimes)
Calc.mod(newHead + newGapCycle.memCycle(0), newHead) != 0
Calc.mod(SieveUtils.product(oldPrimes), newHead) != 0
```

**Why needed:** This lets the canonical path call `cycle.next()` without
manually carrying proof obligations forever.

**Known dependencies:**
- `assertToCycleNextGapsMatchSpecNext`
- Spec next gap-list positivity and non-emptiness
- Spec next acceptance/soundness facts
- new-head primality from Spec next

**Estimated complexity:** Medium after lemma 5; high if attempted before lemma 5.

### 7. Canonical Next Stays Aligned

```scala
def assertCanonicalNextStaysAligned(
  period: BigInt,
  nextPeriod: BigInt,
  k: BigInt
): Boolean
```

**Statement:**

```text
spec.toCycle(period).next()(k)
  == spec.next.toCycle(nextPeriod)(k)
```

or structurally:

```text
spec.toCycle(period).next().primes
  == spec.next.toCycle(nextPeriod).primes

spec.toCycle(period).next().gapCycle.memCycle
  == spec.next.toCycle(nextPeriod).gapCycle.memCycle
```

**Why needed:** This is the recursive alignment theorem. It proves that if the
Spec-built Cycle view is aligned now, then calling `next()` keeps it aligned
with the next Spec-built Cycle view.

**Known dependencies:**
- canonical next head equality
- canonical next gap equality
- canonical next requirements
- `assertToCycleApplyMatches` for `spec.next`

**Estimated complexity:** Medium after lemmas 1-6.

## What This Proves

If completed, this ticket proves:

```text
Every valid Spec stage has a behavior-identical Cycle representation.
The canonical Cycle representation can advance with next().
After advancing, it remains aligned with the canonical Cycle representation of
Spec.next.
```

This supports recursive use:

```text
spec0.toCycle(...)
  .next()
  .next()
  ...
```

while staying tied to the verified Spec path.

## What This Does Not Prove

This does **not** prove that every arbitrary `CycleSieveSequence` value is a
correct sieve stage.

For example, it does not certify:

```scala
CycleSieveSequence(List(5, 3, 2), someUnrelatedGapCycle)
```

unless that object is proven to be equal to `spec.toCycle(period)` for some
valid Spec stage.

This is an intentional and sound restriction. The raw Cycle constructor is an
implementation-level representation; the verified API should prefer canonical
construction from Spec.

## Recommended Next Work

### Strengthen The Cycle Representation First

The canonical construction makes it reasonable for `CycleSieveSequence` to
carry more structural requirements. `SpecSieveSequence.toCycle` can extract
these facts from the specification, while `CycleSieveSequence.next` has one
clear preservation obligation for each fact.

The first required strengthening is:

```text
primes.head + gapCycle.memCycle(0) > primes.head
```

This expression is exactly `apply(1)`, written without calling a method from a
case-class constructor requirement. It immediately gives:

```text
apply(1) > head
apply(1) > 0
apply(1) != 0
```

This is the direct fact missing from the timed-out
`nextWithGapCycle` bridge. It should let later proofs discharge the divisor
precondition of expressions whose divisor is `cycle(1)` without unfolding the
entire canonical Spec construction.

The constructor already carries the other current-stage facts needed by this
ticket:

```text
isCoprime(head, primes.tail)
isCoprime(apply(1), primes.tail)
mod(apply(1), head) != 0
mod(product(primes.tail), head) != 0
```

Possible later requirements, to add only when a concrete proof needs them:

```text
the prime values are strictly descending
every stored prime value is actually prime
the stored prime list is a complete prime prefix through head
the gap cycle has the expected period sum
```

Those facts are stronger and more semantic. They are easy for the canonical
Spec conversion to establish, but preserving them in `CycleSieveSequence.next`
depends on the central next-gap theorem. Adding them before that theorem would
move the same hard proof into every constructor call without yet unblocking the
current bridge.

After the first structural strengthening:

1. [Done] Add a public Cycle-side alias exposing `apply(1) > head`.
2. [Done, superseded shape] Prove canonical next-prime-list correspondence on
   `CanonicalCycleSieve` without calling `nextWithGapCycle`.
3. Add one-step correspondence helpers for the next-gap walk.
4. Prove one-step gap equality, then generalize to the full next-gap walk.

### Immediate Next Lemma: Walk Decision Equality

`SieveSequenceNextLevel.collectGaps` keeps a current canonical value exactly
when:

```text
Calc.mod(current, cycle.head) != 0
```

The current Cycle already guarantees that every generated value is coprime to
`cycle.primes.tail`. Therefore the additional head test is equivalent to
coprimality against the complete old prime list:

```text
SieveUtils.isCoprime(current, cycle.primes)
```

`CanonicalCycleSieve.assertNextAcceptsMatches(current)` then rewrites that
predicate to:

```text
spec.next.accepts(current)
```

The next bridge should state, for every canonical index `k >= 1`:

```text
Calc.mod(cycle(k), cycle.head) != 0
  == spec.next.accepts(cycle(k))
```

Required supporting step: expose the existing pure-Spec monotonicity lemma so
the bridge can prove `cycle(k) >= spec.next.head.value` from `k >= 1`. This
visibility change remains entirely within Spec semantics.

Completed:

- representation aliases exposing:
   - `toCycle(period).head == spec.head.value`
   - `toCycle(period).primes == PrimeUtils.primeValues(spec.primes.list.list)`
   - `toCycle(period).gapCycle.memCycle == spec.specGapCycle(period).memCycle`
- `SpecSieveSequence.toCycle(period)`.
- `SpecSieveSequence.assertToCycleApplyMatches(period, k)`.
- `SpecSieveSequence.assertToCycleNextHeadMatchesSpecNext(period)`.
- `SpecSieveSequence.assertToCycleNextAcceptsMatchesSpecNext(period, value)`.
- `SpecSieveSequence.assertToCycleNextPrimesMatchSpecNext(period)`.

## Work To Avoid For This Ticket

- Do not prove broad residue-pipeline equivalence unless the canonical walk
  proof explicitly needs it.
- Do not prove arbitrary `CycleSieveSequence` correctness.
- Do not attempt counting/permutation proofs over residue lists.
- Do not modify `MemCycle`, `ModCycle`, or `CycleIntegral`.
- Do not add several lemmas at once. Follow the project rule: one lemma/change,
  then verify.

## Validation Plan

- Before code changes, check the latest `verify.log` result.
- For each non-markdown change, run full `just verify` after the change.
- Use focused verification only for iteration, not as final validation.
- Add unit tests for small stages before attempting the hard next-gap theorem:
  - `spec.toCycle(period)(k) == spec(k)` for early stages and small `k`;
  - `spec.toCycle(period).next().head == spec.next.head.value`;
  - concrete next gap list equality for small stages.

## Open Questions

1. Should the raw `CycleSieveSequence` constructor eventually become private,
   with canonical construction as the public path?
2. [Resolved] `CanonicalCycleSieve` owns canonical construction and all direct
   Spec/Cycle correspondence.
3. Which existing Spec lemma best exposes `spec(1) == spec.next.head.value`?
4. Can `CycleSieveSequence.next()` requirements be discharged from
   `nextGapsWalk == spec.next.gapList(...)`, or do we need one additional
   first-next-value lemma?
5. Should the old `v0-v2-apply-equivalence.md` ticket be narrowed to arbitrary
   Cycle refinement after this canonical path is proven?

## Update Log

### 2026-06-23

- Checked existing verification before documentation updates:
  `8720 valid`, `0 invalid`, `0 unknown`.
- Added and verified `SpecSieveSequence.toCycle(period)`.
- Added and verified `SpecSieveSequence.assertToCycleApplyMatches(period, k)`.
- Added and verified
  `SpecSieveSequence.assertToCycleNextHeadMatchesSpecNext(period)`.
- Added and verified
  `SpecSieveSequence.assertToCycleNextAcceptsMatchesSpecNext(period, value)`.
- Added and verified public representation aliases:
  `assertToCycleHeadMatches(period)`,
  `assertToCyclePrimesMatch(period)`, and
  `assertToCycleGapCycleMatches(period)`.
- Added and verified
  `SpecSieveSequence.assertToCycleNextPrimesMatchSpecNext(period)`, proving
  that the raw prime list produced by a canonical Cycle next stage matches the
  raw prime values of `SpecSieveSequence.next`.
- Checked the existing private merge-prefix helpers. They remain useful as
  proof inspiration, but their current precondition `nextSeq.head.value ==
  head.value` means they do not directly apply to the actual canonical
  `spec.next` stage, whose head is `spec.apply(1)`.
- Updated `OBJECTS.md` so the canonical construction and apply equality are
  visible in the `SpecSieveSequence` object catalog.
- Kept the product-not-divisible caveat explicit instead of hiding it inside
  the canonical strategy.

Validation after the representation aliases: focused verification passed for
each alias, then full `just verify` passed with `8795 valid`, `0 invalid`,
`0 unknown`.

Validation after the next-prime-list bridge: focused verification passed for
`assertToCycleNextPrimesMatchSpecNext`, then full `just verify` passed with
`8820 valid`, `0 invalid`, `0 unknown`.

- Tried the next natural bridge,
  `assertToCycleNextWithGapCyclePrimesMatchSpecNext(period, newGapCycle)`, but
  removed it after focused verification timed out. The timeout was not on the
  final prime-list equality; it was on the precondition for evaluating
  `Calc.mod(cycle(1) + newGapCycle.memCycle(0), cycle(1))`, where Stainless
  needed the divisor fact for `cycle(1)` while also unfolding the canonical
  cycle. This suggests the next attempt should first expose a tiny, reusable
  lemma that canonical `cycle(1)` is positive/non-zero, rather than calling
  `CycleSieveSequence.nextWithGapCycle` directly inside a larger bridge.
- Restored the code to the last verified surface and ran full verification:
  `8820 valid`, `0 invalid`, `0 unknown`.

### 2026-06-24

- Confirmed both Spec and Cycle stages use the same filter convention: the
  current head is the stream start, while only `primes.tail` is the active
  filter list.
- Chose to strengthen `CycleSieveSequence` with invariants available directly
  from the canonical Spec representation and preservable by `next`.
- Identified the first missing structural requirement as
  `primes.head + gapCycle.memCycle(0) > primes.head`, the constructor-level
  form of `apply(1) > head`. This also exposes that `apply(1)` is positive and
  nonzero, which addresses the exact divisor-side obligation seen in the last
  timeout.
- Deferred semantic requirements such as complete-prime-prefix correctness and
  exact period-sum equality until the next-gap theorem can preserve them.
- Added the constructor requirement
  `primes.head + gapCycle.memCycle(0) > primes.head` to
  `CycleSieveSequence`. Every current construction site proves it from the
  positive-gap representation; full verification passed with `8823 valid`,
  `0 invalid`, and `0 unknown`.
- Added and verified the public alias
  `CycleSieveSequence.assertNextHeadGreaterThanHead()`, exposing
  `apply(1) > head` without unfolding `CycleIntegral`. The first compile attempt
  identified the missing `BooleanDecorations` import; after adding that import,
  full verification passed with `8825 valid`, `0 invalid`, and `0 unknown`.
- Validation workflow reminder: use `just verify functionName` for fast
  proof iteration, then run full `just verify` once as the final project-wide
  check after the code change.
- Architecture review rejected keeping canonical construction and
  correspondence lemmas on `SpecSieveSequence`. The ticket now adopts
  `CanonicalCycleSieve(spec, period)` as the sole owner of Spec-to-Cycle
  extraction and alignment. Intrinsic Cycle invariants remain on
  `CycleSieveSequence`; pure Spec lemmas remain on `SpecSieveSequence`.
- Exposed `SpecSieveSequence.assertMemCycleGapMatch(i, period)` publicly. Its
  statement remains purely about the Spec-derived gap cycle; the visibility
  change lets the intermediate representation consume it.
- Added and fully verified `CanonicalCycleSieve(spec, period)`. Its `cycle`
  field extracts the raw prime values and exact `specGapCycle(period)` from the
  supplied Spec stage.
- Moved the verified canonical proof surface to the intermediate
  representation:
  `assertApplyMatches`,
  `assertHeadMatches`,
  `assertPrimesMatch`,
  `assertGapCycleMatches`,
  `assertNextHeadMatches`,
  `assertNextAcceptsMatches`, and
  `assertNextPrimesMatch`.
- Retired the old `SpecSieveSequence.toCycle` and `assertToCycle...` API as one
  commented historical block. It was not deleted, following the repository's
  non-destructive editing rule. Active Spec code no longer constructs or
  returns `CycleSieveSequence`.
- Updated `OBJECTS.md` and the coordination ticket to make
  `CanonicalCycleSieve` the canonical owner.
- Final full verification after the ownership migration:
  `8764 valid`, `0 invalid`, `0 unknown`.
- Selected the first post-migration proof target: canonical walk decision
  equality. It connects the exact branch condition in `collectGaps` with
  `spec.next.accepts` for a canonical generated value. This is the smallest
  useful dependency for a later recursive gap-walk equality proof.

### 2026-06-24 — Walk Decision Equality Verified

Added `CanonicalCycleSieve.assertWalkDecisionMatchesNextAccept(k)`.

**Statement:** For every `k >= 1`,
`Calc.mod(cycle(k), cycle.head) != 0 == spec.next.accepts(cycle(k))`.

**Proof structure:**
1. `assertApplyMatches(k)` to equate `cycle(k) == spec(k)`.
2. `spec.assertApplyMonotonic(1, k)` + `assertNextHeadMatches()` to prove
   `cycle(k) >= spec.next.head.value`.
3. `spec(k)` passes tail filter (from `apply(k).ensuring`), giving
   `isCoprime(v, spec.filterValues)`.
4. Structural `primeValues` lemma connects `spec.filterValues == cycle.primes.tail`,
   giving `isCoprime(v, cycle.primes.tail)`.
5. `assertNextAcceptsMatches(v)` gives `spec.next.accepts(v) == isCoprime(v, cycle.primes)`.
6. `isCoprime(v, cycle.primes)` checks head first (returns `false` if
   `v % head == 0`) then recurses to tail (returns `isCoprime(v, tail) = true`
   from step 4). Therefore `isCoprime(v, cycle.primes) == (v % head != 0)`.
7. Completing the equivalence.

**Validation:** Focused verification passed with 55 VCs in 9.69s. Full
`just verify` passed with `8819 valid`, `0 invalid`, `0 unknown`.

**Next target (lemma 5):** `assertToCycleNextGapsMatchSpecNext(period, nextPeriod)` —
the central gap-walk equality theorem. The walk decision equality now provides
the branch-condition bridge needed for a recursive structural comparison between
the walk's collected gaps and `spec.next.gapList`.

### 2026-06-24 — Single-Gap Merge Property Verified (indexOfAccepted approach)

Added `CanonicalCycleSieve.assertNextGapEqualsCurrentGapSum(nextPeriod, i)`.

**Statement:** For any `i < nextPeriod - 1`,
`spec.next(i+1) - spec.next(i) == spec(k_{i+1}) - spec(k_i)`
where `k_i = spec.indexOfAccepted(spec.next(i))`.

**Proof strategy:** Instead of scanning positions (which times out in the
walk/pipeline approaches), the lemma uses `spec.indexOfAccepted()` — a public
verified method with `.ensuring(res => apply(res) == value)`. The cached
postcondition gives `spec(k_i) == spec.next(i)` and `spec(k_{i+1}) == spec.next(i+1)`.
Substituting yields `nextGap == currentGapSum`.

The preconditions (`value >= head.value` and `accepts(value)`) are discharged
via `assertNextHeadMatches`, `assertNextAcceptsMatches`, and the fact that
`spec.next.accepts(spec.next(k))` follows from `apply(k).ensuring`.

**Why this avoids the timeout:** No per-position scanning, no walk execution,
no pipeline unfolding. Just two calls to `indexOfAccepted` per gap, each using
its cached postcondition. The SMT solver only needs arithmetic substitution.

**Validation:** Focused verification passed with 76 VCs in 13.05s. Full
`just verify` passed with `8918 valid`, `0 invalid`, `0 unknown`.

**What this proves:** Adding the current head as a new filter merges consecutive
current gaps whose intermediate values are multiples of head. Each next gap is
the sum of current gaps between two consecutive non-multiples-of-head in the
current stage's value stream. This is the merge property at the per-gap level.

### 2026-06-24 — Gap Equality Attempts and Blocking Analysis

Three approaches to Lemma 5 (proving `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)`)
were attempted. All three timed out. A deep analysis of the three complex verified
files (`ModCycleIntegralProperties`, `MemCycleProperties`, `RecursiveCycleMatchesModCycle`)
was conducted to identify working strategies.

**Attempt 1 — Direct list comparison:** `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)`
as a single `.holds` lemma. Timed out at 121s. The walk's `collectGaps` recursively
scans `head * period` positions, and the SMT solver cannot symbolically execute
this many iterations.

**Attempt 2 — Position-by-position aux lemma:** Followed the
`ModCycleIntegralProperties.assertModCycleEqualsCycleIntegral` pattern of proving
equality through induction on position. Wrote `assertWalkGapsEqualSpecNextGapsAux`
that scans one walk position per recursive call, tracking `lastSurvivor`,
`specIdx`, and `remaining`. At each non-multiple position, asserts
`v == spec.next(specIdx + 1)` and `walkGap == specGap`. Timed out at 300s.

**Root cause:** The critical step `v == spec.next(specIdx + 1)` requires proving
there is no accepted value between `lastSurvivor` and `v`. This requires a FORALL
over all intermediate walk positions (those skipped between the last non-multiple
and the current one). The aux lemma's recursion structure implicitly encodes
this invariant (it only skips multiples), but Stainless cannot derive a FORALL
from a sequential assertion chain. A `∀t ∈ (lastPos, walkPos). !accepted(cycle(t+1))`
quantifier is needed, which Stainless cannot express as a recursive function
parameter.

**Attempt 3 — Even `walkedGaps.nonEmpty`** timed out at 121s, confirming that
`nextGapsWalk` is fundamentally opaque from outside `.holds` contexts. The
`.ensuring` on `collectGaps` (added previously) exports positivity but not
length or element values, so external lemmas get no structural information
about the walk's output.

**Strategy analysis from reference files:**

| Strategy | Source | Why it works | Why it doesn't transfer |
|----------|--------|--------------|------------------------|
| Induction via diff lemma | `ModCycleIntegralProperties` | Diff `f(n)-f(n-1)` depends only on `mod(n, size)`, a single position | Walk diff `v - lastSurvivor` depends on ALL previous positions — no closed-form single-position diff exists |
| Structural alignment | `RecursiveCycleMatchesModCycle` | Both computations handle modulo identically (via `mod` vs `-size`) | Walk and spec.next have NO structural alignment — one scans/gathers, the other generates iteratively |
| Small single-purpose lemmas | `MemCycleProperties` | Each lemma is 3-15 lines, one concept | Works for simple oracle properties; doesn't help with `nextGapsWalk` which is structurally opaque |
| `equality` chaining | `ModCycleIntegralProperties` | Breaks complex algebra into small steps | The gap equality is not algebraic — it requires establishing an inter-process correspondence |

**Revised plan:**

The gap equality `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)` is
deferred to work on easier parts first. Three approaches were attempted (direct
comparison, position-by-position aux lemma, `walkedGaps.nonEmpty`) and all
timed out. The root cause is that `collectGaps` recurses over `head * period`
iterations and the walk's diff depends on `lastSurvivor` (all previous
positions), unlike the modulo-cycle-integral case where the diff depends only
on `mod(position, size)`. This prevents using the
`ModCycleIntegralProperties` "induction via diff lemma" pattern.

**Current focus:** Build the verified canonical path as far as possible without
the gap equality. The canonical construction `CanonicalCycleSieve(spec, period)`
already bridges all known properties for the current stage. The next canonical
stage `CanonicalCycleSieve(spec.next, nextPeriod).cycle` is the correct
continuation by construction. The raw `CycleSieveSequence.next()` method (which
uses `nextGapsWalk`) is a separate optimization whose correctness can be
addressed once the easier canonical path is complete.

**Future work:** Revisit the gap equality after the canonical path is fully
verified. Potential approaches include:
(a) Proving a FORALL over intermediate positions via a recursive accumulator parameter;
(b) Computing `nextGapsWalk` in a non-opaque way by strengthening `collectGaps` postconditions;
(c) A different structural alignment strategy not yet considered.

### 2026-06-24 — Restoration of Verified Lemmas

Restored both non-timed-out lemmas from the commented-out block:

1. **`assertNextGapEqualsCurrentGapSum`** — previously verified at 8918 valid.
   Focused verification: 76 VCs in 2.79s. Full `just verify`: 8918 valid.
   Proves each next-stage gap equals the corresponding current-stage gap sum
   using `indexOfAccepted`'s cached postcondition.

2. **`assertNextValueMatchesCyclePosition`** — not marked as timed out.
   Focused verification: 53 VCs in 2.41s. Full `just verify`: 8971 valid.
   Proves every `spec.next(k)` value appears at some current cycle position,
   establishing value-level correspondence between stages.

**Current verified lemma count on CanonicalCycleSieve:** 12 lemmas.

**Canonical path status:** The canonical bridge is functionally complete for
single-stage representation and cross-stage value correspondence. The
remaining ticket goals (Lemmas 5-7) depend on the deferred gap walk equality.

The canonical path allows constructing `CanonicalCycleSieve(spec.next, nextPeriod)`
directly (with caller-provided preconditions) instead of calling `cycle.next()`.
All 12 verified lemmas establish equivalence between each canonical Cycle and
its originating Spec stage.

**Remaining commented-out code (not restored):**
- `mergeGaps`, `noNonMultipleInRange`, `noNonMultipleExcludesValue`,
  `findNextNonMultiple`, `nonMultiplePosition` — helper functions for timed-out lemmas
- `assertNonMultipleMatchesSpecNext`, `assertMergeGapsMatchesSpecNext`,
  `assertMergeGapsIntegralMatchesSpecNext` — timed out (3 attempts each);
  left commented per stop-and-ask rule
