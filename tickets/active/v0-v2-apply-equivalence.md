# V0-V2 Apply Equivalence

**Status:** Active coordination ticket
**Created:** 2026-06-22
**Depends on:** `v0-gap-list-cycle-formalization.md` (items 1-11 fully verified)

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
- **V2 gap cycle construction:** `SieveSequenceNextLevel.nextGapCycleV2` computes
  the next stage's `GapCycle` via a walk pipeline (`collectGapsV2`). It is
  marked `@extern` (not Stainless-verified). Separately, a residue-based pipeline
  exists (`nextResiduesV2` through `nextRotatedGapsV2`) but is not used by `next()`.
- **No cross-verification exists:** V0 and V2 are completely independent
  implementations. No code asserts equality between them.

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
| `assertResiduesAreExactlyCoprimeBelowModulus(modulus, filters, r)` | For `0 <= r < modulus`, `r in residues(modulus, filters) <=> isCoprime(r, filters)`. | Proves the residue list is not merely a computed list; it is exactly the filter survivor set modulo one period. | Required; may need existing `SieveUtils.residues` helper aliases. |
| `assertExpandedResiduesRepresentPeriod(seq, value)` | Values in `nextExpanded(seq)` are exactly `seq.head + r + m * seq.modulus` for residue survivors `r` across the next head window. | Connects residue classes to actual natural numbers near the current head. | Required. |
| `assertNextFilteredMatchesSpecAccepted(spec, cycle, value)` | Under prime-list correspondence, `value in nextFiltered(cycle) <=> spec.accepts(value)` for values in the pipeline window. | This is where the verified acceptance bridge is consumed by the residue pipeline. | Required. |
| `assertNextSortedIsAcceptedWindow(spec, cycle)` | `nextSorted(cycle).list` is exactly the sorted list of Spec-accepted values in the relevant period window. | Needed before comparing calculated gaps with `spec.gapList`. | Required. |

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

### H. Optional/Deferred Walk Pipeline Bridge

After the conditional same-head/same-gaps theorem is complete, the current
recommendation remains to prove the residue pipeline before the walk pipeline.
The walk pipeline is closer to `next()` as written, but it is harder because it
walks through `CycleSieveSequence.apply`, which already depends on the gap cycle.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertWalkGapsMatchResidueGaps(cycle)` | `nextGapsWalk(cycle) = nextGaps(cycle)`. | Would connect the currently extern-backed walk implementation to the residue proof. | Deferred. |
| `assertNextGapCycleMatchesResidueGapCycle(cycle)` | `SieveSequenceNextLevel.nextGapCycle(cycle).memCycle.values = nextRotatedGaps(cycle)`. | Needed to remove `@extern` from the production `next()` path rather than only proving the residue path. | Deferred. |

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

### Phase 2: V2 gap cycle extraction

Two sub-approaches, either may be chosen:

**Option A — Walk pipeline (what `nextGapCycleV2` actually uses):**
- The walk pipeline (`collectGapsV2`) produces gaps by walking V2's own `apply`.
- Proving this matches V0's gaps is **circular** if V2.apply is defined in terms
  of the gap cycle. This suggests Option A is impractical for the base equivalence.

**Option B — Residue pipeline (defined but unused by `next()`):**
- `nextResiduesV2` through `nextRotatedGapsV2` compute the next gap cycle purely
  from the prime modulus and residues, without reference to V2.apply.
- Each pipeline step has a pre-verified `SieveUtils` helper.
- The gap cycle from residues should equal the gap cycle from the walk.
- Proving residue gaps == V0 gaps is more direct: V0's `accepts` predicate is
  exactly `isCoprime(value, filterValues)`, which is the same predicate the
  residue pipeline uses.

**Recommendation:** First prove Phase 1.5, the conditional same-head/same-gaps
equivalence theorem. After that, start with Option B. Defer the
residue-pipeline-to-walk equivalence to a separate subticket.

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
Proof: Trivial wrapper combining `assertResiduesAllCoprime` (soundness) and `assertResiduesComplete` (completeness) into one bidirectional `.holds` lemma.

**E2: `assertExpandedResiduesRepresentPeriod(seq, value)`**
Statement: `value ∈ expandResidues(residues(seq.modulus, seq.primes.tail), seq.modulus, seq.head) ⇔ 0 ≤ value < seq.head * seq.modulus ∧ isCoprime(value, seq.primes.tail)`
Proof:
- Forward: Every value in the expanded set is coprime to primes.tail (already in `assertAllRExpandedCoprime`) and bounded by head * modulus (already in `assertExpandResiduesRange`).
- Reverse: Given `0 ≤ v < head*modulus` and `isCoprime(v, primes.tail)`, decompose `r = v % modulus`, `i = Calc.div(v, modulus)`. Need to show `0 ≤ r < modulus`, `isCoprime(r, primes.tail)`, and `0 ≤ i < head`. The bounds follow from `Calc.mod` postcondition and `v < head*modulus`. Coprimality preservation of `v % modulus` with respect to `primes.tail` requires a small helper lemma: if `isCoprime(v, primes)` and `v = q*modulus + r`, then `isCoprime(r, primes)` — which follows from the fact that any divisor of `r` also divides `v` since `modulus` is a product of those primes.

**E3: `assertNextFilteredMatchesSpecAccepted(spec, cycle, value)`**
Statement: `value ∈ nextFiltered(seq) ⇔ 0 ≤ value < head * modulus ∧ isCoprime(value, head :: primes.tail)`
Proof: Composes E2 with `filterList` semantics. `filterList(list, head)` removes values where `Calc.mod(v, head) == 0`. So the filtered set = `{v in expanded set | v % head ≠ 0}` = `{v in [0, head*modulus) | isCoprime(v, primes.tail) ∧ v % head ≠ 0}`. Since head is prime, `v % head ≠ 0` iff `isCoprime(v, List(head))`. The conjunction is exactly `isCoprime(v, head :: primes.tail)`.

**E4: `assertNextSortedIsAcceptedWindow(spec, cycle)`**
Statement: The sorted pipeline output (after sorting) represents the same survivor set as Spec's accepted values in one period `[head, head + head*modulus)`.
Proof: Sorting does not change the set (only order). The Spec next stage's `accepts(v)` predicate is `v >= head ∧ isCoprime(v, head :: primes.tail)`. The sorted+filtered set contains all such values in `[0, head*modulus)`. The gap cycle `calculateGaps(sorted, head*modulus)` computes pairwise gaps with wrap-around by `head*modulus`, which matches the next stage's first period exactly. The shift from 0-based to head-based does not change the gap cycle (wrapping by `head*modulus` handles the offset).

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
2. **Residue pipeline vs. walk pipeline:** The residue pipeline is defined but
   unused by `nextGapCycleV2`. The walk pipeline is @extern. Proving the walk
   pipeline correct is a separate problem that may need the inductive stage
   bridge (Phase 4) or a separate `remove-extern-from-next.md` ticket.
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



## Related Tickets

- `v0-gap-list-cycle-formalization.md` — prerequisite: V0's internal gap cycle
  properties must be fully verified before this ticket can consume them.
- `remove-extern-from-next.md` — tracks removing @extern from V2.next(). May
  be partially unblocked by the gap periodicity facts proven in V0.
- `../superseded/conditional-nextprime-gap-cycle-bridge.md` — historical
  attempt at bridging V0 and V2 concepts (superseded).
