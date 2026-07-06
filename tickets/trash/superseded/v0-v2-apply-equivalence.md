# V0-V2 Apply Equivalence

**Status:** Active coordination ticket
**Created:** 2026-06-22
**Depends on:** `v0-gap-list-cycle-formalization.md` (items 1-11 fully verified)
**Alternative active strategy:** `canonical-spec-to-cycle-alignment.md`

The alternative ticket narrows the proof to the canonical Cycle sequence built
by the intermediate correspondence representation:

```text
canonical = SpecDerivedCycleSieve(spec, period)
cycle = canonical.cycle
```

and then tries to prove the recursive alignment theorem:

```text
canonical.cycle.next() aligns with
SpecDerivedCycleSieve(spec.next, nextPeriod).cycle
```

This may be a more tractable route than proving arbitrary
`CycleSieveSequence` equivalence.

## Goal

Prove that `SpecSieveSequence` and `CycleSieveSequence` generate the same values when
constructed from corresponding prime lists:

```
SpecSieveSequence(AllPrimesSoFarList(SortedPrimeList(primes.map(Prime(_))))).apply(k)
  ==
CycleSieveSequence(primes, gapCycle).apply(k)

for all k >= 0 and for every valid sieve stage.
```

## Current State

- **V0 properties (prerequisite):** Most gap properties are verified in
  `SpecSieveSequence` (see `v0-gap-list-cycle-formalization.md`). Items 7
  (`assertApplyEqualsHeadPlusGapSum`) and 8 (`gapList(from, count)`) are the
  two V0 lemmas that were identified as missing — they are the bridge entry
  points this ticket consumes.
- **Cycle next construction:** `CycleSieveSequence.next()` is no longer
  `@extern`. It is a conditional verified builder: it computes
  `SieveSequenceNextLevel.nextGapsWalk(this)`, requires the walked gaps to be a
  valid positive `GapCycle`, requires the first next-cycle value to satisfy the
  new filters, and delegates to `nextWithGapCycle`.
- **No cross-verification exists:** V0 and V2 are completely independent
  implementations. No code asserts equality between them.

## Strategy Reset — Recommended Proof Path

The proof should now be organized around the transition from a known-equivalent
current stage to an equivalent next stage.

**Recommended primary theorem:**

```
current head equal
and current gap cycle equal
  ==> current apply streams equal
  ==> next heads equal
  ==> next acceptance predicates equal
  ==> next walked gaps equal Spec next gaps
  ==> next gap cycles equal
  ==> next apply streams equal
```

The current verified lemmas already cover the first and last implication:

- same current head + same current gap cycle implies current apply equivalence;
- same next head + same next gap cycle implies next apply equivalence.

The missing producer theorem is:

```
same current head + same current gap cycle
  ==> SieveSequenceNextLevel.nextGapsWalk(cycle)
      == spec.next.gapList(0, nextPeriod)
```

This is the central proof obligation for this ticket.

### Work On These Next

1. **Next head equality from current equivalence.**
   Prove a small bridge using the existing all-index apply equivalence at
   `k = 1`:

   ```
   same current head + same current gaps
     ==> cycle(1) == spec(1)
     ==> cycle(1) == spec.next.head.value
   ```

   The second step may require the existing Spec-side next-prime/square-bound
   precondition, but the new head is prime on the Spec side by construction.

2. **Next-stage acceptance predicate equality.**
   Prove that once `cycle(1) == spec.next.head.value`, both sides use the same
   next filter:

   ```
   spec.next.accepts(value)
     == SieveUtils.isCoprime(value, cycle(1) :: cycle.primes)
   ```

   This is more directly useful than proving residue-pipeline facts in
   isolation.

3. **Walk gap equality against Spec next gaps.**
   Prove the recursive producer theorem:

   ```
   SieveSequenceNextLevel.nextGapsWalk(cycle)
     == spec.next.gapList(0, nextPeriod)
   ```

   This proof should consume current apply equivalence, next head equality, and
   next acceptance equality.

4. **Derive `next()` requirements from gap equality.**
   Once walked gaps equal Spec next gaps, use Spec gap-list validity to discharge:

   ```
   newGaps.nonEmpty
   ListBoundUtils.allGreaterThan(newGaps, 0)
   ```

   Then handle the remaining first-next-value filter requirements using the same
   next acceptance equivalence.

### Do Not Work On These Unless They Directly Feed The Path Above

- Do **not** continue proving general residue-pipeline soundness/completeness as
  an end in itself.
- Do **not** add more `nextSorted`/`nextFiltered` aliases unless a later theorem
  explicitly consumes them.
- Do **not** attempt counting/permutation/list-extensionality proofs for the
  residue pipeline unless the direct walk-vs-Spec gap proof fails and the ticket
  is explicitly re-scoped.
- Do **not** try to prove `nextGapsWalk == nextGaps` as the immediate next step.
  That compares two Cycle-side constructions and does not by itself establish
  Spec/Cycle equivalence.

Residue lemmas already proved are not considered wasted: they remain useful
supporting facts and may become important if the direct walk proof fails.
However, the default next work should target the Spec/Cycle transition above.

## The Equivalence Chain

```
V0.apply(k)                              [by definition of gaps]
  = V0.head + sum_{i=0}^{k-1} V0.gap(i)  [V0 lemma: assertApplyEqualsHeadPlusGapSum]
  = V0.head + CycleIntegral(V0.gapList).apply(k-1)  [by construction of GapCycle from V0 gaps]
  = V2.head + CycleIntegral(V2.gapCycle).apply(k-1)  [if V0's gap cycle == V2's gap cycle]
  = V2.apply(k)                           [by definition of V2]
```

The central unproven link is: **V0's gap cycle values equal V2's gap cycle values**
for the same prime list.

## Required Lemma Map

This section lists the lemmas currently believed necessary for the full
`SpecSieveSequence.apply(k) == CycleSieveSequence.apply(k)` proof. The names are
proposed local names unless marked as already implemented.

### A. Representation Bridges

These lemmas do not prove new sieve mathematics. They translate between the
Spec representation (`Prime` values stored in `AllPrimesSoFarList`) and the
Cycle representation (`BigInt` values stored directly in `CycleSieveSequence`).

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertHeadsMatchFromPrimeValues(spec, cycle)` | If `cycle.primes = primeValues(spec.primes)`, then `spec.head.value = cycle.head`. | Base case and all integral equations need both streams to start at the same number. | Verified. |
| `assertFilterValuesMatchTailPrimes(spec, cycle)` | If `cycle.primes = primeValues(spec.primes)`, then `cycle.primes.tail = spec.filterValues`. | Lets every filter predicate move between Spec and Cycle. | Verified. |
| `assertSpecAcceptsMatchesCycleTailCoprime(spec, cycle, value)` | If `value >= spec.head.value`, then `spec.accepts(value) <=> isCoprime(value, cycle.primes.tail)`. | This is the semantic bridge from the linear Spec filter to the Cycle residue/filter pipeline. | Verified. |
| `assertApplyZeroMatchesFromPrimeValues(spec, cycle)` | If `cycle.primes = primeValues(spec.primes)`, then `spec(0) = cycle(0)`. | Handles the `k = 0` case before the proof switches to gap/integral reconstruction for `k > 0`. | Verified. |

### B. Spec Apply As Gaps

These lemmas express the linear Spec stream as a head plus a sum of consecutive
gaps. This is the bridge from "search through accepted numbers" to "cycle over
gap values".

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertApplyEqualsHeadPlusGapSum(k)` | For all `k >= 0`, `spec(k) = spec.head.value + sum_{i=0}^{k-1} gap(i)`. Equivalently, `spec(k) = head + sumGap(0, k)`. | Turns `spec.apply` into an accumulated gap expression. | Verified in `SpecSieveSequence`. |
| `gapList(from, count)` plus size/positivity aliases | `gapList(from, count) = [gap(from), ..., gap(from + count - 1)]`, `size = count`, and every gap is `> 0`. | Needed to package Spec gaps as a valid `GapCycle`. | Verified in `SpecSieveSequence`. |
| `assertGapPeriodic(k, period)` | If `period = indexOfAccepted(head + filterModulus)`, then `gap(k + period) = gap(k)`. | Justifies using a finite Spec gap list as a repeating cycle. | Verified in `SpecSieveSequence`. |
| `assertSpecPeriodAnchor(period)` | If `period = indexOfAccepted(head + filterModulus)`, then `spec(period) = head + filterModulus`. | Identifies the first full filter period in the Spec stream. | Existing via `indexOfAccepted`; useful alias still wanted. |

### C. Spec GapCycle Reconstruction

These lemmas prove that the finite Spec gap list, once wrapped in `GapCycle` and
`CycleIntegral`, reconstructs the same values as `spec.apply`.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `specGapCycle(period)` | If `period > 0` and `spec(period) = head + filterModulus`, then `GapCycle(gapList(0, period))` is well formed and stores exactly those gaps. | Builds the same object shape used by `CycleSieveSequence`. | Verified. |
| `assertSpecGapCycleIntegralBase(period)` | `CycleIntegral(head, specGapCycle(period).memCycle)(0) = spec(1)`. | Base case for positive indices. | Verified. |
| `assertSpecGapCycleIntegralStep(period, k)` | If `k >= 0`, then advancing the integral one step adds the next periodic Spec gap: `I(k + 1) = I(k) + gap(k + 1)`, where `I = CycleIntegral(head, specGapCycle(period).memCycle)`. | Gives the induction step for integral reconstruction. | Subsumed by `assertSpecGapCycleIntegralMatchesApply`. |
| `assertSpecGapCycleIntegralMatchesApply(period, k)` | For all `k > 0`, `CycleIntegral(head, specGapCycle(period).memCycle)(k - 1) = spec(k)`. | Converts the Spec stream into the same `apply` shape as `CycleSieveSequence`. | Verified. |

### D. Cycle Apply As Integral

These lemmas expose simple facts already present in `CycleSieveSequence.apply`.
They are worth local aliases so the final proof does not unfold class internals
repeatedly.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|---|
| `assertCycleApplyZeroIsHead(cycle)` | `cycle(0) = cycle.head`. | Cycle side of the base case. | Trivial; currently used inside base bridge. |
| `assertCycleApplyPositiveIsIntegral(cycle, k)` | If `k > 0`, then `cycle(k) = cycle.integral(k - 1)`. | Final rewrite in the `k > 0` equivalence proof. | Verified. |
| `assertCycleIntegralUsesGapCycle(cycle)` | `cycle.integral = CycleIntegral(cycle.head, cycle.gapCycle.memCycle)`. | Makes the integral object explicit when comparing against the Spec-built `CycleIntegral`. | Verified. |

### E. Residue Pipeline Means Accepted Values

These lemmas connect the Cycle residue pipeline to the same accepted values
enumerated by the Spec linear search. This is the main semantic work.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertResiduesContainCoprimeBelowModulus(modulus, filters, r)` | For `0 <= r < modulus`, `isCoprime(r, filters) => r in residues(modulus, filters)`. | Completeness half of the residue characterization. Proves every filter survivor below the modulus is generated by the residue list. | Verified. |
| `assertResiduesAreCoprimeBelowModulus(modulus, filters, r)` | For `r in residues(modulus, filters)`, `isCoprime(r, filters)`. | Soundness half of the residue characterization. Proves the generated residue list contains only filter survivors. | Verified. |
| `assertResiduesAreExactlyCoprimeBelowModulus(modulus, filters, r)` | For `0 <= r < modulus`, `r in residues(modulus, filters) <=> isCoprime(r, filters)`. | Combines the completeness and soundness halves into the bidirectional residue characterization used by later pipeline lemmas. | Both halves verified separately; bidirectional wrapper deferred (not needed by downstream lemmas). |
| `assertExpandedResiduesRepresentPeriod(seq, value)` | Values in `nextExpanded(seq)` are exactly `seq.head + r + m * seq.modulus` for residue survivors `r` across the next head window. | Connects residue classes to actual natural numbers near the current head. | Verified. |
| `assertNextFilteredContainsCoprime(seq, value)` | `0 ≤ value < head*modulus` ∧ `isCoprime(value, head :: primes.tail)` ⇒ `value ∈ nextFiltered(seq)`. | Reverse direction: every coprime bounded value survives the residue + filter pipeline. | Verified. |
| `assertNextFilteredIsCoprime(seq, value)` | `value ∈ nextFiltered(seq)` ⇒ `isCoprime(value, head :: primes.tail)`. | Forward direction: every filtered survivor is coprime. | In progress — one generated-offset block now has verified membership-to-coprime soundness via `assertGeneratedOffsetContainsOnlyCoprime`; remaining work is lifting that fact through `expandSingleResidue` and `expandResidues`, then combining it with the head filter. |
| `assertNextSortedContainsCoprime(seq, value)` | `0 ≤ value < head*modulus` ∧ `isCoprime(value, head :: primes.tail)` ⇒ `value ∈ nextSorted(seq).list`. | Reverse direction for the sorted pipeline. Forward direction is guaranteed by construction (sorted from nextFiltered). | Verified. |
| `assertNextSortedOnlyContainsFiltered(seq, value)` | `value ∈ nextSorted(seq).list` ⇒ `value ∈ nextFiltered(seq)`. | Forward direction for the sorted stage only: sorting can reorder survivors but cannot create a new survivor value. | Verified. |

### F. Gap List Equality

These lemmas turn equality of survivor values into equality of consecutive gap
lists.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertCalculateGapsMatchesSpecGapList(spec, cycle, period)` | If `nextSorted(cycle).list = [spec(0), spec(1), ..., spec(period)]`, then `calculateGaps(nextSorted(cycle), cycle.modulus) = spec.gapList(0, period)`. | Converts survivor-value equality into gap equality. | Required. |
| `assertNextGapsMatchSpecGapList(spec, cycle, period)` | `SieveSequenceNextLevel.nextGaps(cycle) = spec.gapList(0, period)`. | Bridges the named Cycle pipeline output to Spec gaps. | Required. |
| `assertNextRotatedGapsMatchSpecGapList(spec, cycle, period)` | After rotating at the next-head residue index, the Cycle gap list equals the Spec gap list for the same head alignment. | Needed if the pipeline rotation changes the starting point relative to `spec.head`. | Required; exact statement depends on chosen head alignment. |
| `assertCycleGapCycleMatchesSpecGapCycle(spec, cycle, period)` | `cycle.gapCycle.memCycle.values = specGapCycle(period).memCycle.values`. | The central object equality used by the top-level apply proof. | Required. |

### G. Top-Level Apply Equivalence

These lemmas combine the previous groups into the final theorem.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps(spec, cycle, period, k)` | If `k > 0`, `spec.head.value == cycle.head`, and `spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle`, then `spec(k) = cycle(k)`. | Main positive-index theorem under the clean same-head/same-gaps precondition. | Verified. |
| `assertSpecCycleApplyMatchesFromSameHeadAndGaps(spec, cycle, period, k)` | If `k >= 0`, `spec.head.value == cycle.head`, and `spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle`, then `spec(k) = cycle(k)`. | Final conditional local equivalence theorem for one stage. It proves same head plus same gap memory is enough for all indices. | Verified. |
| `assertSpecCycleNextResiduePipelineMatches(spec, cycle)` | If the Cycle gap cycle is constructed by the residue pipeline for the same stage, then the gap-cycle-match precondition of `assertSpecCycleApplyMatches` holds. | Connects the final theorem to the actual construction path we want to trust. | Required after residue work. |

### I. Conditional Next Bridge

These lemmas expose the constructor shape needed to compare `SpecSieveSequence.next`
with a conditionally verified Cycle next. The goal is to make hard obligations
explicit as preconditions instead of forcing Stainless to rediscover the full
next-stage proof inside one method body.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertSpecNextPrimeValuesExtendCurrent(spec)` | If `spec.primes.nextPrime.value < spec.head.value * spec.head.value`, then `PrimeUtils.primeValues(spec.next.primes.list.list) = spec.next.head.value :: PrimeUtils.primeValues(spec.primes.list.list)`. | Shows that Spec `next` prepends its new head to the previous raw prime values, matching the raw list shape expected from Cycle next. | Verified. |
| `assertConditionalNextPrimeValuesMatch(spec, cycle, newGapCycle)` | If current raw prime lists correspond, `cycle(1) = spec.next.head.value`, and `newGapCycle` satisfies `nextWithGapCycle` preconditions, then `cycle.nextWithGapCycle(newGapCycle).primes = PrimeUtils.primeValues(spec.next.primes.list.list)`. | Gives the next-stage raw-prime correspondence under the isolated next-head and gap-cycle constructor assumptions. | Verified. |
| `assertConditionalNextApplyMatchesFromSameHeadAndGaps(spec, cycle, newGapCycle, nextPeriod, k)` | If current raw prime lists correspond, `cycle(1) = spec.next.head.value`, `newGapCycle` satisfies `nextWithGapCycle` preconditions, `spec.next(nextPeriod) = spec.next.head.value + spec.next.filterModulus`, and `spec.next.specGapCycle(nextPeriod).memCycle = cycle.nextWithGapCycle(newGapCycle).gapCycle.memCycle`, then `spec.next(k) = cycle.nextWithGapCycle(newGapCycle)(k)`. | Combines the conditional next raw-prime bridge with the all-index same-head/same-gaps theorem, advancing apply equivalence by one stage while keeping the hard `next()` requirements explicit. | Verified. |

### H. Optional/Deferred Walk Pipeline Bridge

This section is intentionally deferred. These lemmas compare Cycle-side
pipelines to each other; they are not the preferred immediate route to
Spec/Cycle equivalence.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertWalkGapsMatchResidueGaps(cycle)` | `nextGapsWalk(cycle) = nextGaps(cycle)`. | Optional fallback if the direct `nextGapsWalk(cycle) == spec.next.gapList(...)` proof is blocked. It does not by itself prove Spec/Cycle equivalence. | Deferred. |
| `assertNextGapCycleMatchesResidueGapCycle(cycle)` | `SieveSequenceNextLevel.nextGapCycle(cycle).memCycle.values = nextRotatedGaps(cycle)`. | Optional residue-pipeline bridge. Not the next recommended target because `CycleSieveSequence.next()` currently uses `nextGapsWalk`. | Deferred. |

## Approach

### Phase 1: V0 gap cycle construction (depends on `v0-gap-list-cycle-formalization.md`)

1. Use `V0.gapList(0, p)` with `p = indexOfAccepted(head + filterModulus)` to
   extract the concrete gap list for the current stage.
2. Construct a `GapCycle(gapList)` and prove `CycleIntegral(head, gapCycle).apply(k-1)`
   equals `V0.apply(k)` using `assertApplyEqualsHeadPlusGapSum` and gap periodicity.

**Verification scope:** All V0-internal. No V2 references.

### Phase 1.5: Conditional same-head/same-gaps equivalence (preferred next step)

Before proving where the Cycle-side gaps come from, prove the simple conditional
bridge:

```
if spec.head.value == cycle.head
and spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle
then spec.apply(k) == cycle.apply(k)
```

This is not a different proof strategy. It is the same equivalence chain split
at the cleanest boundary: two streams with the same starting value and the same
repeating gaps are the same stream. Proving this first is preferable because it
isolates the easy final rewrite from the harder gap-construction proof.

Expected proof shape:

1. For `k == 0`, use the head equality and both `apply(0)` definitions.
2. For `k > 0`, use
   `SpecSieveSequence.assertSpecGapCycleIntegralMatchesApply(period, k)` to
   rewrite Spec apply into `CycleIntegral(spec.head.value, specGapCycle(period).memCycle)(k - 1)`.
3. Use `SpecCycleSieveEquivalence.assertCycleApplyPositiveIsIntegral(cycle, k)`
   and `assertCycleIntegralUsesGapCycle(cycle)` to rewrite Cycle apply into
   `CycleIntegral(cycle.head, cycle.gapCycle.memCycle)(k - 1)`.
4. The assumed head equality and MemCycle equality make the two integral objects
   identical.

This gives a useful theorem even before the residue or walk pipeline is proven:
all remaining work can focus on proving the gap equality precondition.

### Phase 2: Next-stage producer theorem

The previous version of this ticket recommended proving the residue pipeline
first. That recommendation is now superseded.

The preferred path is to prove that current Spec/Cycle equivalence produces the
same next state:

```
same current head + same current gap cycle
  ==> same current apply stream
  ==> same next head
  ==> same next accepted values
  ==> nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)
```

This targets the production path used by `CycleSieveSequence.next()` and avoids
building a large residue-pipeline proof that may not be consumed by the final
equivalence theorem.

**Residue pipeline status:** The residue pipeline remains a valid fallback or
supporting route. It should be used only when a concrete downstream proof needs
one of its facts, for example to simplify a specific acceptance predicate or to
replace a failed direct walk argument. It should not be the default next track.

### Phase 3: Equivalence proof

1. Prove that `V0.gapList(0, p)` (the first-period V0 gaps) equals the gap list
   produced by the residue pipeline for the same primes.
   - This requires mapping V0's filter primes to V2's prime list representation.
   - The core identity: V0.accepts(v) == isCoprime(v, V0.filterValues) ==
     SieveUtils.isCoprime(v, V2.primes.tail).
2. Construct a `GapCycle` from the residue pipeline result.
3. Prove `V0.apply(k) == V2.apply(k)` by induction on k, using the gap cycle
   equality and the CycleIntegral representation.

### Phase 4: Inductive stage-to-stage (optional, long-term)

Prove that if V0 and V2 agree at stage n, they also agree at stage n+1:
- V0's gap transformation lemmas (copy/merge, `mergedGapPrefix`) describe
  stage n+1 gaps in terms of stage n gaps.
- V2's residue pipeline describes stage n+1 gaps in terms of stage n primes.
- Prove these two descriptions produce equal gap cycles.

## Concrete Work Items

### Work item 1: Phase 1 — V0 GapCycle construction

**Requires:** `V0.gapList(from, count)` and `V0.assertApplyEqualsHeadPlusGapSum(k)`.

Build a lemma (in `SpecSieveSequence` or a companion) that:
1. Computes `p = indexOfAccepted(head.value + filterModulus)`.
2. Computes `gaps = gapList(0, p)`.
3. Builds `GapCycle(gaps)`.
4. Proves `CycleIntegral(head, GapCycle(gaps).memCycle).apply(k) == apply(k+1)`.

**Estimated complexity:** Medium. The GapCycle construction and integral equality
follow directly from V0's gap properties, but constructing the concrete objects
inside Stainless may require handling constructor preconditions
(`allGreaterThan(_, 0)`, non-empty).

**Progress:** Sub-step 3 is verified as `SpecSieveSequence.specGapCycle(period)`.
Given `period > 0` and `apply(period) == head.value + filterModulus`, it builds
`GapCycle(gapList(0, period))` and exports
`result.memCycle.values == gapList(0, period)`. This discharges the Spec-side
`GapCycle` constructor preconditions using `assertGapListPositive` and
`assertGapListSize`. Verified with 7771 valid after tests passed (173/173).
The base case of sub-step 4 is verified as
`SpecSieveSequence.assertSpecGapCycleIntegralBase(period)`: the integral built
from `specGapCycle(period)` satisfies
`CycleIntegral(head.value, specGapCycle(period).memCycle)(0) == apply(1)`.
Focus-verified with `just verify assertSpecGapCycleIntegralBase` (17 valid),
then full-verified with `just verify` (7788 valid).
The remaining Phase 1 proof is the general integral reconstruction theorem for
all positions.

### Work item 2: Group E — Residue pipeline semantics

Prove that the residue pipeline (`nextResidues` → `nextExpanded` → `nextFiltered` → `nextSorted`)
produces the same set of accepted values that Spec's next-stage survivor window would.

**Already proved (in `SieveUtils`):**
- `assertResiduesAllCoprime` — every residue in [0, modulus) is coprime to primes.tail (soundness)
- `assertResiduesComplete` — every value in [0, modulus) coprime to primes.tail appears (completeness)
- `assertAllRExpandedCoprime` — for every residue r and 0 ≤ i < head, r + i*modulus is coprime to primes.tail
- `assertExpandResiduesRange` — expanded set is non-negative and bounded by head * modulus
- `assertFilterListNonNegative`, `assertFilterListAllLessThan` — filterList preserves range properties

**Group E lemmas (4 required):**

**E1: `assertResiduesAreExactlyCoprimeBelowModulus(modulus, filters, r)`**
Statement: `r ∈ residues(modulus, primes.tail) ⇔ 0 ≤ r < modulus ∧ isCoprime(r, primes.tail)`
Proof: Split into one-value aliases. The completeness direction is now verified
as `assertResiduesContainCoprimeBelowModulus`, which wraps
`SieveUtils.assertGenerateResiduesContainsCoprime`. The soundness direction
should be proved separately by induction over `generateResidues`, then E1 can
combine both halves into the bidirectional `.holds` lemma.

**E2: `assertExpandedResiduesRepresentPeriod(seq, value)`**
Statement: `value ∈ expandResidues(residues(seq.modulus, seq.primes.tail), seq.modulus, seq.head) ⇔ 0 ≤ value < seq.head * seq.modulus ∧ isCoprime(value, seq.primes.tail)`
Proof:
- Forward: Every value in the expanded set is coprime to primes.tail (already in `assertAllRExpandedCoprime`) and bounded by head * modulus (already in `assertExpandResiduesRange`).
- Reverse: Given `0 ≤ v < head*modulus` and `isCoprime(v, primes.tail)`, decompose `r = v % modulus`, `i = Calc.div(v, modulus)`. Need to show `0 ≤ r < modulus`, `isCoprime(r, primes.tail)`, and `0 ≤ i < head`. The bounds follow from `Calc.mod` postcondition and `v < head*modulus`. Coprimality preservation of `v % modulus` with respect to `primes.tail` requires a small helper lemma: if `isCoprime(v, primes)` and `v = q*modulus + r`, then `isCoprime(r, primes)` — which follows from the fact that any divisor of `r` also divides `v` since `modulus` is a product of those primes.

**E3: `assertNextFilteredMatchesSpecAccepted(spec, cycle, value)`**
Statement: `value ∈ nextFiltered(seq) ⇔ 0 ≤ value < head * modulus ∧ isCoprime(value, head :: primes.tail)`
Proof: Composes E2 with `filterList` semantics. `filterList(list, head)` removes values where `Calc.mod(v, head) == 0`. So the filtered set = `{v in expanded set | v % head ≠ 0}` = `{v in [0, head*modulus) | isCoprime(v, primes.tail) ∧ v % head ≠ 0}`. Since head is prime, `v % head ≠ 0` iff `isCoprime(v, List(head))`. The conjunction is exactly `isCoprime(v, head :: primes.tail)`.

**E4: `assertNextSortedContainsCoprime(seq, value)`**
Statement: For `0 ≤ value < head*modulus` and `isCoprime(value, head :: primes.tail)`, `value ∈ nextSorted(seq).list`.
Proof: `assertNextFilteredContainsCoprime` gives `value ∈ nextFiltered(seq)`. Then `assertInsertSortedContainsSelf`, `assertInsertSortedPreservesMembership`, and `assertSortFilteredContains` lift membership through `sortFiltered` to `SortedList.fromUnsorted`. Sorting preserves the set: every element of the input appears in the sorted output.

**Key technical challenges:**
1. E2 reverse direction needs a lemma that `mod` preserves coprimality: `isCoprime(v, primes) ∧ v = q*modulus + r ⇒ isCoprime(r, primes)`. This is true because any divisor of `r` divides `v` (since `modulus` is the product of primes in `primes`).
2. E2 also needs the identity `Calc.div(v, modulus) < head` when `v < head*modulus` — this follows from `Calc.div` being the floor of the division.

**Estimated complexity:** Low-Medium. Mostly gluing existing `SieveUtils` lemmas together. The only new proof content is E2's reverse direction (coprimality preservation under `mod`).

### Work item 3: Phase 3 — Top-level equivalence

```scala
def assertV0EqualsV2(v0: SpecSieveSequence, v2: CycleSieveSequence, k: BigInt): Boolean = {
  require(k >= 0)
  // prime list correspondence
  // gap cycle equality
  v0.apply(k) == v2.apply(k)
}.holds
```

**Estimated complexity:** Very high. Depends on items 1-2.

### Work item 4: Phase 4 — Inductive stage bridge (future)

Prove that `V0.next().apply(k) == CycleSieveSequence(v2.primes.next, ...).apply(k)`
under the inductive hypothesis that V0 and V2 agree at the current stage.

**Not yet scoped.** Requires all V0 gap transformation lemmas (items 1-6, 9-11
of `v0-gap-list-cycle-formalization.md`).

## Risks and Assumptions

1. **Prime list representation mismatch:** V0 uses `AllPrimesSoFarList` (which
   wraps `SortedPrimeList[Prime]`). V2 uses `List[BigInt]`. Proving they
   correspond may require a translation layer and lemmas about `primeValues`.
2. **Residue pipeline vs. walk pipeline:** The residue pipeline is defined, but
   `CycleSieveSequence.next()` currently uses `nextGapsWalk`. The walk path is
   no longer `@extern`, but it is conditional: it requires non-empty positive
   gaps and first-next-value filter facts. The recommended proof should derive
   those facts from equality with `spec.next.gapList(...)`, not from an
   unrelated residue-pipeline proof.
3. **Gap cycle construction preconditions:** `GapCycle` requires
   `allGreaterThan(values.list, 0)` (proven in V0) and non-empty. The
   non-emptiness proof (`p > 0`) is trivial but must be explicit.
4. **Period length equivalence:** V0's period `p = indexOfAccepted(head + M)`
   and the residue list size should be equal. This is the "P4" property
   explicitly SKIPPED in SpecSieveSequence (see OBJECTS.md line 976: counting
   residues timed out). For Phase 2, we may need to avoid relying on this
   equality — use the actual residue list size as the cycle length.

## Validation

- Before starting each work item, verify that all dependencies in
  `v0-gap-list-cycle-formalization.md` are complete.
- Write concrete unit tests for small stages (S_0, S_1, S_2) comparing V0 and
  V2 outputs before attempting general proofs.
- Use `seq.integral.cycle.values == seq.gapCycle.memCycle.values` as a sanity
  check (guaranteed by V2's object graph).
- Follow AGENTS.md green-to-green: verify before and after each change, one
  lemma per cycle.
- Search `tickets/` for existing work on the residue pipeline correctness
  before duplicating effort.

## Update Log

### 2026-06-23 — Strategy reset: prioritize next-state producer theorem

The proof plan was updated to prevent drift toward residue-pipeline lemmas that
do not directly advance the final Spec/Cycle equivalence theorem.

**Decision:** The primary route is now:

```
same current head + same current gap cycle
  ==> same current apply stream
  ==> same next head
  ==> same next acceptance predicate
  ==> nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)
  ==> same next gap cycle
  ==> same next apply stream
```

**Why:** The project already has the consumer theorem:

```
same head + same gap cycle ==> same apply(k)
```

What is missing is the producer theorem:

```
same current state ==> same next head and same next gaps
```

Residue-pipeline facts can be useful, but proving them in isolation risks
creating verified lemmas that do not discharge the requirements of
`CycleSieveSequence.next()` or the next-stage equivalence bridge.

**Recommended immediate work:**

1. Prove next head equality from current same-head/same-gaps equivalence.
2. Prove next-stage acceptance predicate equality.
3. Prove `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)`.
4. Derive `CycleSieveSequence.next()` requirements from that gap equality.

**Explicit non-goals for now:**

- More general `nextFiltered`/`nextSorted` aliases unless directly consumed.
- Counting/permutation proofs for residue lists.
- `nextGapsWalk == nextGaps` as the next immediate step.
- Full residue-pipeline equivalence unless the direct walk proof is blocked and
  this ticket is deliberately re-scoped.

### 2026-06-22 — Naming decision and rename execution

**Decision:** Rename classes to better reflect architectural roles:

| Old | New | Rationale |
|---|---|---|
| `SieveSequenceV0` | `SpecSieveSequence` | The specification model — linear scan, obviously correct by construction |
| `SieveSequenceV2` | `CycleSieveSequence` | The cycle-based implementation — uses precomputed GapCycle and CycleIntegral |

**Also renamed:**
- Companion methods `S_0V2()`/`S_1V2()` → `S_0()`/`S_1()`
- All `V2` suffixes on `SieveSequenceNextLevel` methods dropped (e.g., `nextResiduesV2` → `nextResidues`)
- Files renamed accordingly (e.g., `SieveSequenceV0.scala` → `SpecSieveSequence.scala`)

**Status:** Rename execution complete. All source files, test files, and markdown docs updated.
- **Verify:** 7755 valid, 0 invalid, 0 unknown (cache rebuilt).
- **Tests:** 173 passed, 0 failed.
- **Docs updated:** OBJECTS.md, LEARNINGS.md, AGENTS.md (0 refs), and 15+ tickets/articles.

**Assumptions unchanged:** All 4 risks (prime list representation, residue vs. walk pipeline, gap cycle preconditions, period length equivalence) unaffected by the rename.

**Assumptions unchanged:** Prime list representation mismatch (risk 1), residue vs. walk pipeline (risk 2), gap cycle construction preconditions (risk 3), period length equivalence (risk 4) — none affected by the rename.

### 2026-06-22 — Spec GapCycle constructor bridge

Added `SpecSieveSequence.specGapCycle(period)` as the first Phase 1 bridge.

- **What it proves:** For a positive period satisfying
  `apply(period) == head.value + filterModulus`, `gapList(0, period)` can be
  wrapped as a first-class `GapCycle`, and the resulting cycle values are
  exactly the Spec gap list.
- **Why it matters:** The Spec-vs-Cycle equivalence now has a verified way to
  construct the same object shape used by `CycleSieveSequence`, without touching
  the residue pipeline or the walk pipeline.
- **Validation:** `just test` passed with 173 tests. `just verify` passed with
  7771 valid, 0 invalid, 0 unknown.
- **Next step:** Prove the integral reconstruction theorem:
  `CycleIntegral(head.value, specGapCycle(period).memCycle)(k - 1) == apply(k)`
  for `k > 0`, likely by induction and/or by connecting repeated cycle access
  back to `gapList` plus `assertGapPeriodic`.

### 2026-06-22 — Focused Stainless verification command

Added an optional focus argument to `just verify` and `just verify-no-cache`.

- **Command shape:** `just verify someFunctionName` compiles the full Scala
  source tree, then passes `--functions=someFunctionName` to Stainless.
- **Why not file-only:** Directly giving Stainless only one `.scala` file fails
  for this project because imported dependencies are not present in the compile
  set. The focused-function approach preserves full-source compilation while
  shrinking the VC set for fast proof iteration.
- **Boundary:** This is an interaction aid only. It does not replace the final
  full `just verify` required before treating the branch as green.
- **Validation:** `just verify assertSpecGapCycleIntegralBase` passed with
  17 valid, 0 invalid, 0 unknown. Full `just verify` later passed with
  7788 valid, 0 invalid, 0 unknown.

### 2026-06-22 — Spec gap-cycle integral base case

Added `SpecSieveSequence.assertSpecGapCycleIntegralBase(period)`.

- **What it proves:** Given `period > 0` and
  `apply(period) == head.value + filterModulus`, the `CycleIntegral` built from
  `specGapCycle(period).memCycle` reconstructs the next Spec value at integral
  index 0:
  `CycleIntegral(head.value, specGapCycle(period).memCycle)(0) == apply(1)`.
- **Why it matters:** This confirms that the packaged Spec gaps are not merely
  constructible as a `GapCycle`; they also begin reconstructing the Spec stream
  through the same integral object used by the cycle implementation.
- **Validation:** Focus-verified with `just verify assertSpecGapCycleIntegralBase`
  (17 valid, 0 invalid, 0 unknown), then full-verified with `just verify`
  (7788 valid, 0 invalid, 0 unknown).
- **Next step:** Generalize from the base case to arbitrary `k`, probably by
  proving a small recursive/inductive lemma that aligns `CycleIntegral` over
  `gapList(0, period)` with `sumGap(0, k + 1)`.

### 2026-06-22 — Local representation bridge aliases

Added `SpecCycleSieveEquivalence` as the local home for Spec-vs-Cycle bridge
lemmas.

- **`assertHeadsMatchFromPrimeValues(spec, cycle)`**
  proves that if the cycle-side prime list is exactly
  `PrimeUtils.primeValues(spec.primes.list.list)`, then
  `spec.head.value == cycle.head`.
- **`assertFilterValuesMatchTailPrimes(spec, cycle)`**
  proves that the same prime-list correspondence gives
  `cycle.primes.tail == spec.filterValues`.
- **Dependency shape:** Head equality and filter equality both depend only on
  the full prime-list correspondence. The next planned local alias should use
  `assertFilterValuesMatchTailPrimes` to expose the predicate identity
  `spec.accepts(value) == SieveUtils.isCoprime(value, cycle.primes.tail)`.
- **Validation:** `just test` passed with 173 tests, but took 129 seconds and is
  too slow for the normal proof-edit loop. Focused verification passed for both
  aliases (`assertHeadsMatchFromPrimeValues`: 6 valid;
  `assertFilterValuesMatchTailPrimes`: 12 valid). Full `just verify` passed with
  7806 valid, 0 invalid, 0 unknown.

### 2026-06-22 — Acceptance predicate bridge alias

Added `SpecCycleSieveEquivalence.assertSpecAcceptsMatchesCycleTailCoprime`.

- **What it proves:** Given the same prime-list correspondence and a value at
  or above the Spec head, Spec acceptance is exactly the cycle-side tail
  coprime predicate:
  `spec.accepts(value) == SieveUtils.isCoprime(value, cycle.primes.tail)`.
- **Why it matters:** This is the first semantic bridge after the representation
  aliases. It gives the future apply-equivalence proof a local, verified way to
  translate "accepted by the Spec linear filter" into the predicate used by the
  cycle-side residue/filter pipeline.
- **Dependency shape:** The lemma depends on
  `assertFilterValuesMatchTailPrimes(spec, cycle)` plus the definition of
  `SpecSieveSequence.accepts`.
- **Validation:** Focus-verified with
  `just verify assertSpecAcceptsMatchesCycleTailCoprime` (11 valid, 0 invalid,
  0 unknown), then full-verified with `just verify` (7817 valid, 0 invalid,
  0 unknown).
- **Next step:** Add the base-case apply bridge, likely proving that under the
  prime-list correspondence `spec(0) == cycle(0)`.

### 2026-06-22 — Required lemma map and base apply bridge

Added the Required Lemma Map near the top of this ticket.

- **What it documents:** The expected dependency chain for the full
  Spec-vs-Cycle apply proof, grouped into representation bridges, Spec
  gap/integral reconstruction, Cycle apply aliases, residue-pipeline semantics,
  gap-list equality, top-level apply equivalence, and the deferred walk-pipeline
  bridge.
- **Why it matters:** The proof now has an explicit map of the lemmas we believe
  are required, including mathematical statements and status for each one. This
  should keep future proof work focused and prevent rediscovering the same
  dependency shape.
- **Code progress:** Added
  `SpecCycleSieveEquivalence.assertApplyZeroMatchesFromPrimeValues`, proving
  that under prime-list correspondence `spec(0) == cycle(0)`.
- **Validation:** Focus-verified with
  `just verify assertApplyZeroMatchesFromPrimeValues` (9 valid, 0 invalid,
  0 unknown), then full-verified with `just verify` (7826 valid, 0 invalid,
  0 unknown).

### 2026-06-22 — Cycle integral uses gap cycle alias

Added `SpecCycleSieveEquivalence.assertCycleIntegralUsesGapCycle`.

- **What it proves:**
  `cycle.integral == CycleIntegral(cycle.head, cycle.gapCycle.memCycle)`.
  The cycle implementation's stored integral is exactly the object shape that
  the Spec-side gap-cycle reconstruction theorem constructs from
  `specGapCycle(period)`.
- **Why it matters:** The final apply-equivalence proof for `k > 0` will need
  to compare the Cycle-side integral (used by `cycle(position)`) with the
  Spec-side integral (built from `specGapCycle(period).memCycle`). This lemma
  names the Cycle-side integral construction so the proof does not need to
  unfold `CycleSieveSequence` internals.
- **Validation:** Present in code already, verified as part of the 7829-valid
  full run. No dedicated focus-verify was run (trivial equality on field
  access).

### 2026-06-22 — Full Spec gap-cycle integral reconstruction theorem

Added five lemmas to `SpecSieveSequence` completing Phase 1 of the equivalence proof:

1. **`assertGapPeriodicMultiple(k, n, period)`** (private) — Extends
   `assertGapPeriodic` from one period to multiple periods by induction on `n`.
   Proves `gap(k + n*period) == gap(k)`.
2. **`assertGapListFirstEqualsGap(from, count)`** (private) — Proves
   `gapList(from, count).head == apply(from+1) - apply(from)` for `count > 0`.
3. **`assertGapListApplyEqualsGapAtPosition(from, count, r)`** (private) —
   Proves `gapList(from, count)(r) == apply(from+r+1) - apply(from+r)` for
   `r < count`, by induction on `r` shifting the `from` parameter.
4. **`assertMemCycleGapMatch(i, period)`** (private) — Proves
   `specGapCycle(period).memCycle(i) == apply(i+1) - apply(i)` for all `i >= 0`.
   Two-case induction: `i < period` uses `smallValueInCycle` +
   `assertGapListApplyEqualsGapAtPosition`; `i >= period` uses
   `valueMatchAfterManyLoops` + `assertGapPeriodic(i - period, period)`.
5. **`assertSpecGapCycleIntegralMatchesApply(period, k)`** (public) — The main
   Phase 1 theorem. Proves
   `CycleIntegral(head.value, specGapCycle(period).memCycle)(k-1) == apply(k)`
   for all `k > 0`. Induction on `k`: base `k=1` delegates to
   `assertSpecGapCycleIntegralBase`; step uses `CycleIntegralProperties.assertNextPosition`,
   the IH, and `assertMemCycleGapMatch(k-1, period)` to chain:
   `integral(k-1) == integral(k-2) + memCycle(k-1) == apply(k-1) + (apply(k) - apply(k-1)) == apply(k)`.

**Architectural notes:**
- `assertGapPeriodicMultiple` avoids needing the `Calc.div`/`Calc.mod` identity
  `a = b*div(a,b) + mod(a,b)` by using `valueMatchAfterManyLoops` with `m = 1`
  — reducing by exactly one period per recursion step instead of jumping directly
  to the remainder.
- `assertMemCycleGapMatch` bridges the gap between periodic MemCycle access
  (via ModCycle) and the infinite linear Spec gap sequence, which is the core
  connection needed by the integral reconstruction.

**Validation:** Focus-verified each lemma, then full `just verify` passed with
7943 valid (0 invalid, 0 unknown). `just test` passed with 144 tests.

**Update to lemma map:** `assertSpecGapCycleIntegralMatchesApply` moved from
`Required` to `Verified`. `assertSpecGapCycleIntegralStep` (the intermediate
step lemma) marked as `Subsumed` — the full theorem covers the same ground
more directly.

**Next steps:** Phase 1.5 — prove the conditional same-head/same-gaps
equivalence theorem before entering the residue pipeline lemmas.

### 2026-06-23 — Prefer conditional same-head/same-gaps theorem before Phase 2

After reviewing the proof strategy, the preferred next checkpoint is now the
conditional theorem:

```
spec.head.value == cycle.head
spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle
-----------------------------------------------------------
spec.apply(k) == cycle.apply(k)
```

This does not replace the residue-pipeline work. It isolates the easy final
rewrite and makes the remaining hard obligation explicit: prove the Cycle gap
cycle equals the Spec gap cycle. Once this theorem is verified, Phase 2 and
Phase 3 can focus only on discharging the gap equality precondition.

### 2026-06-23 — Positive same-head/same-gaps apply equivalence verified

Added
`SpecCycleSieveEquivalence.assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps`.

- **What it proves:** For `position > 0`, if
  `spec.head.value == cycle.head` and
  `spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle`, then
  `spec(position) == cycle(position)`.
- **Why it matters:** This verifies the positive-index half of the simplified
  strategy: once both implementations have the same head and same repeated
  gap memory, both positive apply values are reconstructed by the same
  `CycleIntegral`.
- **Validation:** Focus-verified with
  `just verify assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps`
  (16 valid, 0 invalid, 0 unknown), then full-verified with `just verify`
  (7959 valid, 0 invalid, 0 unknown).
- **Next step:** Add the all-index wrapper that combines this lemma with the
  existing `k == 0` base bridge.

### 2026-06-23 — All-index same-head/same-gaps apply equivalence verified

Added `SpecCycleSieveEquivalence.assertSpecCycleApplyMatchesFromSameHeadAndGaps`.

- **What it proves:** For `position >= 0`, if
  `spec.head.value == cycle.head` and
  `spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle`, then
  `spec(position) == cycle(position)`.
- **Why it matters:** This completes the conditional Phase 1.5 checkpoint. The
  current-stage apply equivalence is now reduced entirely to proving the gap
  equality precondition.
- **Validation:** Focus-verified with
  `just verify assertSpecCycleApplyMatchesFromSameHeadAndGaps`
  (19 valid, 0 invalid, 0 unknown), then full-verified with `just verify`
  (7978 valid, 0 invalid, 0 unknown).
- **Next step:** Prove or construct the gap equality bridge:
  `spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle`.

### 2026-06-23 — Spec next raw-prime extension bridge verified

Added `SpecCycleSieveEquivalence.assertSpecNextPrimeValuesExtendCurrent`.

- **What it proves:** If Spec's `next` precondition holds, then
  `PrimeUtils.primeValues(spec.next.primes.list.list) ==
  spec.next.head.value :: PrimeUtils.primeValues(spec.primes.list.list)`.
- **Why it matters:** This captures the representation shape needed for a
  verified next bridge: Spec next prepends the new head to the old raw prime
  values, while Cycle next should construct the same raw shape once its own
  head and gap-cycle obligations are made explicit.
- **Validation:** Focus-verified with
  `just verify assertSpecNextPrimeValuesExtendCurrent`
  (7 valid, 0 invalid, 0 unknown), then full-verified with `just verify`
  (7985 valid, 0 invalid, 0 unknown).
- **Learning:** Spec next and Cycle next pick their new head differently:
  Spec uses `AllPrimesSoFarList.nextPrime`; Cycle uses `cycle.apply(1)`. A
  conditional Cycle `next` should expose the needed equality and constructor
  obligations rather than trying to prove the whole walk-pipeline correctness
  immediately.

### 2026-06-23 — Conditional Cycle next builder verified

Added `CycleSieveSequence.nextWithGapCycle(newGapCycle)`.

- **What it proves:** If the caller supplies a `GapCycle` whose first generated
  value satisfies the remaining next-stage constructor facts, then
  `CycleSieveSequence(apply(1) :: primes, newGapCycle)` is a valid verified
  `CycleSieveSequence`.
- **Required assumptions:** The supplied gap cycle must make
  `apply(1) + newGapCycle.memCycle(0)` coprime to the old `primes`, not a
  multiple of the new head `apply(1)`, and must preserve
  `Calc.mod(SieveUtils.product(primes), apply(1)) != 0`.
- **Why it matters:** This mirrors the strategy used by `SpecSieveSequence.next`,
  where the hard fact that the next prime is before `head * head` is a method
  precondition. Here, the hard facts are the gap-cycle correctness obligations;
  the method assumes them explicitly and verifies the rest of the constructor
  path. This is analogous to `tail` requiring a non-empty list.
- **Validation:** Focus-verified with `just verify nextWithGapCycle`
  (12 valid, 0 invalid, 0 unknown), then full-verified with `just verify`
  (7997 valid, 0 invalid, 0 unknown).
- **Learning:** We can now separate two tasks cleanly: construct or assume a
  gap cycle that satisfies the next-stage facts, then use `nextWithGapCycle`
  as the verified constructor bridge. The follow-up implementation removed
  `@extern` from `next()` by exposing the walk-pipeline gap-list facts as
  explicit requirements inside the method.

### 2026-06-23 — Conditional next raw-prime bridge verified

Added `SpecCycleSieveEquivalence.assertConditionalNextPrimeValuesMatch`.

- **What it proves:** If the current Spec/Cycle raw prime lists correspond,
  Spec's `next` precondition holds, `cycle.apply(1) == spec.next.head.value`,
  and the supplied `newGapCycle` satisfies `CycleSieveSequence.nextWithGapCycle`
  requirements, then the conditional next Cycle stage has the same raw prime
  list as `spec.next`.
- **Why it matters:** This connects the verified conditional Cycle builder to
  the Spec next representation. It leaves the genuinely hard next-head equality
  and gap-cycle correctness facts explicit, but proves that once those facts are
  available the raw prime-list correspondence advances by one stage.
- **Validation:** Focus-verified with
  `just verify assertConditionalNextPrimeValuesMatch`
  (23 valid, 0 invalid, 0 unknown), then full-verified with `just verify`
  (8020 valid, 0 invalid, 0 unknown).
- **Next step:** Add the analogous conditional next apply-equivalence bridge:
  assuming next raw prime correspondence, next head equality, and next gap-cycle
  equality, reuse `assertSpecCycleApplyMatchesFromSameHeadAndGaps` to prove
  `spec.next(k) == cycle.nextWithGapCycle(newGapCycle)(k)`.

### 2026-06-23 — Conditional next apply bridge verified

Added `SpecCycleSieveEquivalence.assertConditionalNextApplyMatchesFromSameHeadAndGaps`.

- **What it proves:** For any `position >= 0`, under the explicit next-head,
  next-gap, period-anchor, and `nextWithGapCycle` constructor assumptions,
  `spec.next(position) == cycle.nextWithGapCycle(newGapCycle)(position)`.
- **Why it matters:** This is the conditional next-stage apply equivalence. It
  does not call `cycle.next()` directly, so the proof keeps the conditional
  next construction facts explicit. It proves that once the hard next facts are
  supplied, the verified conditional Cycle next path matches Spec next for every
  index.
- **Validation:** Focus-verified with
  `just verify assertConditionalNextApplyMatchesFromSameHeadAndGaps`
  (39 valid, 0 invalid, 0 unknown), then full-verified with `just verify`
  (8059 valid, 0 invalid, 0 unknown).
- **Remaining hard obligations:** Prove or assume
  `cycle.apply(1) == spec.next.head.value`; prove or assume
  `newGapCycle.memCycle == spec.next.specGapCycle(nextPeriod).memCycle`; prove
  or assume the three `nextWithGapCycle` constructor requirements for the
  concrete next gap cycle.

### 2026-06-23 — Cycle next removed from `@extern` with explicit requirements

Updated `CycleSieveSequence.next()` to remove `@extern`.

- **What changed:** `next()` now computes `nextGapsWalk(this)`, requires the
  walked gap list to be non-empty and all positive, constructs
  `GapCycle(newGaps)`, then requires the three `nextWithGapCycle` constructor
  facts before delegating to `nextWithGapCycle(newGapCycle)`.
- **Why it matters:** This exposes the concrete reason `next()` was extern. A
  direct call to `SieveSequenceNextLevel.nextGapCycle(this)` timed out because
  Stainless could not prove that `nextGapsWalk(this)` is non-empty and all
  positive at the call site. Making those facts explicit lets Stainless verify
  the rest of the method body.
- **Explicit requirements now carried by `next()`:**
  1. `newGaps.nonEmpty`
  2. `ListBoundUtils.allGreaterThan(newGaps, BigInt(0))`
  3. `SieveUtils.isCoprime(apply(1) + newGapCycle.memCycle(0), primes)`
  4. `Calc.mod(apply(1) + newGapCycle.memCycle(0), apply(1)) != BigInt(0)`
  5. `Calc.mod(SieveUtils.product(primes), apply(1)) != BigInt(0)`
- **Validation:** The first attempt, with only the three constructor facts,
  timed out on the two `nextGapCycle(this)` preconditions. After exposing all
  five requirements, full `just verify` passed with 8070 valid, 0 invalid, and
  0 unknown.
- **Remaining semantic work:** These requirements are assumed, not derived.
  The next proof work is to discharge them for the concrete walk-produced gap
  cycle, then connect `CycleSieveSequence.apply(1)` to `SpecSieveSequence.next.head`.

### 2026-06-23 — Residue completeness alias verified

Added `SpecCycleSieveEquivalence.assertResiduesContainCoprimeBelowModulus`.

- **What it proves:** For one residue value, if `0 <= residue < modulus`, the
  filters are positive, and `SieveUtils.isCoprime(residue, filters)` holds,
  then `SieveUtils.residues(modulus, filters).contains(residue)`.
- **Why it matters:** This is the completeness half of E1. It proves that every
  valid survivor below the modulus is generated by the residue list, using the
  existing `SieveUtils.assertGenerateResiduesContainsCoprime` proof in the
  exact local shape needed by the equivalence ticket.
- **Validation:** Full `just verify` passed with 8082 valid, 0 invalid, and
  0 unknown.
- **Learning:** The full E1 iff should stay split. Completeness is usable now;
  soundness should be the next small lemma, likely by induction over
  `generateResidues` membership rather than by trying to consume
  `assertResiduesAllCoprime` as if it were a one-value membership theorem.

### 2026-06-23 — Residue soundness wrapper and expanded-set period lemma (E1b, E2)

Added two public lemmas to `SpecCycleSieveEquivalence`:

1. **`assertResiduesAreCoprimeBelowModulus`** (E1b): Soundness half of E1.
   If `residues(modulus, filters)` contains `residue`, then
   `isCoprime(residue, filters)`. Wraps
   `assertGenerateResiduesContainOnlyCoprime`. Verified with 8137 valid.

2. **`assertExpandedResiduesRepresentPeriod`** (E2): Proves the expanded residue
   pipeline (`expandResidues(residues, seq.modulus, seq.head)`) contains exactly
   every coprime value in one period `[0, seq.head * seq.modulus)`.

   The reverse direction (coprime ⇒ appears in expansion) required new proofs:
   - **`assertModPreservesCoprimeForPrime`**: For one prime `p`, if `v % p ≠ 0`
     and `p | modulus`, then `Calc.mod(v, modulus) % p ≠ 0`. Uses `DivMod` for
     the decomposition `v = q*modulus + r` and `ModOperations.modAdd` + `modIdempotence`
     to prove `Calc.mod(v, p) == Calc.mod(r, p)`.
   - **`assertModPreservesCoprime`**: Lifts the per-prime lemma to a list of
     primes, using a prefix-product recursion (`modulus == prefixProd * product(remaining)`)
     to maintain the divisibility invariant.
   - **`assertAddOffsetContains`**: Proves `addOffset(list, offset)` preserves
     membership (`list.contains(x) ⇒ addOffset(list, offset).contains(x + offset)`).
   - **`assertExpandSingleResidueContains`**, **`assertExpandResiduesExtendsTo`**,
     **`assertExpandResiduesContainsShifted`**: Structural induction lemmas that
     propagate membership through the nested `++` calls in `expandSingleResidue`.

   **Validation:** Focus-verified each lemma, then full `just verify` passed with
   8319 valid (0 invalid, 0 unknown). `just test` passed with 144 tests.

   **Update to lemma map:** `assertResiduesAreCoprimeBelowModulus` (E1b) moved
   from `Required` to `Verified`. `assertExpandedResiduesRepresentPeriod` (E2)
   moved from `Required` to `Verified`. Bidirectional E1 wrapper deferred
   (both halves verified separately, no downstream lemma needs the combined form).

   **Next steps:** E3 (`assertNextFilteredMatchesSpecAccepted`) — connects the
   residue pipeline's filtered output to Spec's `accepts` predicate.

### 2026-06-23 — Filtered and sorted reverse-direction membership verified

Added two public lemmas to `SpecCycleSieveEquivalence`:

1. **`assertNextFilteredContainsCoprime`**: If `value` is in the bounded
   residue window and is coprime to `seq.head :: seq.primes.tail`, then
   `nextFiltered(seq)` contains `value`. This is the reverse direction of E3.

2. **`assertNextSortedContainsCoprime`**: Under the same bounded-coprime
   assumptions, `nextSorted(seq).list` contains `value`. This is the reverse
   direction of E4.

**Validation:** Full `just verify` passed with 8424 valid, 0 invalid, and
0 unknown.

**Remaining blocker:** The forward direction for `nextFiltered`/`nextSorted`
is still not locally exposed as a one-value theorem:
`value in nextFiltered(seq) => isCoprime(value, seq.head :: seq.primes.tail)`.
The source has `assertFilterListContainsOnlyIf`, and `SieveUtils` has
`assertAllRExpandedCoprime`, but the missing connector is a usable membership
lemma from `value in nextExpanded(seq)` to coprime-to-tail. A previous attempt
at the full list-level induction timed out, so the next attempt should isolate
that one-value connector rather than rebuild the whole pipeline.

### 2026-06-23 — Sorted forward-direction membership verified

Added `SpecCycleSieveEquivalence.assertNextSortedOnlyContainsFiltered`.

- **What it proves:** If `nextSorted(seq).list` contains `value`, then
  `nextFiltered(seq)` also contains `value`. This is the forward direction for
  the sorted stage only: sorting may reorder values, but it does not invent
  values.
- **How it was proved:** Added two private structural lemmas:
  `assertInsertSortedContainsOnlyExisting` proves `insertSorted` contributes
  only the inserted value or values already present in the input list; and
  `assertSortFilteredContainsOnlyExisting` lifts that fact across the recursive
  sort.
- **Validation:** Full `just verify` passed with 8456 valid, 0 invalid, and
  0 unknown.
- **Learning:** This successfully exposes the sorted-stage forward membership
  half, but it does not solve filtered-stage soundness. The hard frontier is
  now precise: prove `value in nextFiltered(seq) => isCoprime(value, seq.head ::
  seq.primes.tail)`, which likely requires a one-value expanded-stage soundness
  lemma before using `assertFilterListContainsOnlyIf`.

### 2026-06-23 — Expanded-stage soundness attempt rejected

Tried to prove the missing expanded-stage connector through a private
`assertAddOffsetContainsOnlyCoprime` helper.

- **Attempt 1:** Generalized over an arbitrary `residues` list. Stainless
  rejected the proof because arbitrary residues do not imply the generated
  value is nonnegative, bounded, or actually a member of
  `SieveUtils.residues(modulus, primes)`.
- **Attempt 2:** Strengthened the helper with
  `residues == SieveUtils.residues(modulus, primes)`. That fixed some shape
  issues but broke the recursive tail call because `residues.tail` is not equal
  to the full generated residue list. The attempt also timed out/returned
  unknown when trying to turn `SieveUtils.assertExpandedCoprime` into a usable
  `isCoprime(...)` fact.
- **Decision:** Removed the helper and restored green verification before
  proceeding. Do not continue with this exact proof shape. A better next
  attempt should either expose postconditions from the existing SieveUtils
  expanded-coprime lemmas or prove a smaller one-value lemma directly over the
  concrete recursive structure of `expandResidues`.

### 2026-06-23 — Expanded-value coprimality postcondition verified

Added two private arithmetic helpers to `SpecCycleSieveEquivalence`:

1. **`assertExpandedValueCoprimeViaPrefix`**: If `i >= 0`, `modulus` is
   `prefixProd * product(primes)`, and `r` is coprime to `primes`, then
   `r + i * modulus` is also coprime to `primes`.

2. **`assertExpandedValueCoprime`**: Natural wrapper for the common case
   `modulus == product(primes)`.

**Why it matters:** This takes the arithmetic fact already implicit in
`SieveUtils.assertExpandedCoprimeViaPrefix` and exposes it as a usable
postcondition. The previous failed expanded-stage attempt got stuck partly
because the existing helper returned only `true`, so callers could not use it
to derive `SieveUtils.isCoprime(value, primes)`.

**Validation:** Full `just verify` passed after the prefix helper with 8503
valid, 0 invalid, and 0 unknown. Full `just verify` passed again after the
natural wrapper with 8513 valid, 0 invalid, and 0 unknown.

**Next step:** Prove a structural list lemma over
`SieveUtils.addOffset(SieveUtils.generateResidues(from, modulus, primes), i *
modulus)`: membership in that offset list implies coprimality to `primes`.
That lemma should recurse over `generateResidues(from, ...)`, not over an
arbitrary residue tail, and should call `assertExpandedValueCoprime` only in
the kept-residue branch.

### 2026-06-23 — Generated-offset soundness verified

Added private lemma **`assertGeneratedOffsetContainsOnlyCoprime`** to
`SpecCycleSieveEquivalence`.

**Statement:** If a value belongs to
`SieveUtils.addOffset(SieveUtils.generateResidues(from, modulus, primes), i *
modulus)`, with `0 <= from <= modulus`, `i >= 0`, positive filters, and
`modulus == product(primes)`, then the value is coprime to `primes`.

**Why it matters:** This is the first list-level soundness bridge for the
expanded stage that avoids the previous timeout pattern. The proof follows the
shape of `generateResidues(from, ...)` directly:

- If `from` is kept by the residue generator, the head case calls
  `assertExpandedValueCoprime(from, i, modulus, primes)`.
- If the member value is not the current offset head, or if `from` was not
  kept, the proof recurses on `from + 1`.

This works because the lemma is specialized to the generated residue list
instead of trying to prove a false/general property for an arbitrary list of
residues.

**Validation:** Full `just verify` passed with 8556 valid, 0 invalid, and 0
unknown.

**Next step:** Prove the corresponding structural soundness for
`expandSingleResidue(residue, modulus, count)` by recursion over `count`, using
`assertGeneratedOffsetContainsOnlyCoprime` for the current generated-offset
block and the induction hypothesis for the remaining blocks. After that, lift
one more level to `expandResidues(residues(...), modulus, count)` and use it to
complete `assertNextFilteredIsCoprime`.

### 2026-06-23 — Item 1: Next head equality verified (from current equivalence)

Added two lemmas following the ordered "Work On These Next" plan:

1. **`SpecSieveSequence.assertApplyOneEqualsNextPrime`**
   (`src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala`):
   Proves `apply(1) == primes.nextPrime.value` given `nextPrime.value < head^2`.
   The proof uses:
   - `assertApplyOneGtHead`: `head + 1 <= apply(1)`
   - `assertApplyOneAtOrBeforeOwnNextPrime`: `apply(1) <= nextPrime`
   - `assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq`: `Prime.isPrime(apply(1))`
   - `AllPrimesSoFarList.nextPrime`'s postcondition:
     `noPrimesBetween(head+1, nextPrime)`
   Since `apply(1)` is prime and `> head`, no prime exists in `(head, nextPrime)`,
   so `apply(1)` must equal `nextPrime`.

2. **`SpecCycleSieveEquivalence.assertCurrentApplyOneEqualsSpecNextHead`**
   (`src/main/scala/v1/chapter6/seq/sieve/SpecCycleSieveEquivalence.scala`):
   Proves `cycle(1) == spec.next.head.value` under the current-stage equivalence
   assumptions (same head, same gaps) plus the Spec `next()` precondition.
   Combines the all-index apply equivalence at `k=1` with the new Spec-side
   lemma above.

**Validation:** Focus-verified each lemma, then full `just verify` passed with
8613 valid (0 invalid, 0 unknown).

**Next step:** Item 2 — Next-stage acceptance predicate equality.

### 2026-06-23 — Item 2: Next-stage acceptance predicate equality verified

Added `SpecCycleSieveEquivalence.assertNextAcceptsMatchesCyclePrimesCoprime`.

**Statement:** Under the prime-list correspondence and the Spec `next()`

## Strategy Update 2026-06-24 — Gap Equality Deferred, Canonical Path Forward

The original "Work On These Next" items 1-4 in this ticket were superseded by
the canonical strategy (see `canonical-spec-to-cycle-alignment.md`). The
canonical approach creates `SpecDerivedCycleSieve(spec, period)` as the sole
owner of Spec-to-Cycle extraction and alignment.

**Progress on canonical lemmas:**

| Lemma | Status | VCs |
|-------|--------|-----|
| Canonical cycle construction | Verified | 8820 verified |
| `assertApplyMatches(k)` | Verified | same |
| `assertNextHeadMatches()` | Verified | same |
| `assertNextAcceptsMatches(v)` | Verified | same |
| `assertNextPrimesMatch()` | Verified | same |
| `assertWalkDecisionMatchesNextAccept(k)` | Verified | +55, total 8819 |
| `assertNextGapEqualsCurrentGapSum(nextPeriod, i)` | Verified | +76, total 8918 — single-gap merge via `indexOfAccepted` |
| Gap equality (lemma 5) | **Deferred** | 3 approaches timed out — revisit after easier canonical path is complete |

**Gap equality root cause:** The walk's `collectGaps` is structurally opaque
from outside `.holds` contexts. Three separate approaches to proving
`nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)` all timed out:
(1) direct comparison, (2) position-by-position aux lemma following the
`ModCycleIntegralProperties` pattern, (3) even `walkedGaps.nonEmpty`. The
issue is that the walk's diff (`v - lastSurvivor`) depends on ALL
previous positions, unlike the modulo-cycle-integral case where the diff
depends only on `mod(position, size)`.

**Current focus:** Build the verified canonical path as far as possible without
the gap equality. The canonical construction `SpecDerivedCycleSieve(spec, period)`
already bridges all known properties for the current stage. The next canonical
stage `SpecDerivedCycleSieve(spec.next, nextPeriod).cycle` is the correct
continuation by construction. The raw `CycleSieveSequence.next()` optimization
(which uses `nextGapsWalk`) is deferred — we will return to it after completing
the canonical path.

**Future approaches for the gap equality:**
(a) Proving a FORALL over intermediate positions via a recursive accumulator
parameter inside `collectGaps`;
(b) Strengthening `collectGaps` postconditions to export element-level data;
(c) A different structural alignment strategy not yet considered.
