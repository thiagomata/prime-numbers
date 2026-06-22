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
| `assertSpecGapCycleIntegralStep(period, k)` | If `k >= 0`, then advancing the integral one step adds the next periodic Spec gap: `I(k + 1) = I(k) + gap(k + 1)`, where `I = CycleIntegral(head, specGapCycle(period).memCycle)`. | Gives the induction step for integral reconstruction. | Required. |
| `assertSpecGapCycleIntegralMatchesApply(period, k)` | For all `k > 0`, `CycleIntegral(head, specGapCycle(period).memCycle)(k - 1) = spec(k)`. | Converts the Spec stream into the same `apply` shape as `CycleSieveSequence`. | Required; next major Phase 1 lemma. |

### D. Cycle Apply As Integral

These lemmas expose simple facts already present in `CycleSieveSequence.apply`.
They are worth local aliases so the final proof does not unfold class internals
repeatedly.

| Lemma | Mathematical statement | Why needed | Status |
|---|---|---|---|
| `assertCycleApplyZeroIsHead(cycle)` | `cycle(0) = cycle.head`. | Cycle side of the base case. | Trivial; currently used inside base bridge. |
| `assertCycleApplyPositiveIsIntegral(cycle, k)` | If `k > 0`, then `cycle(k) = cycle.integral(k - 1)`. | Final rewrite in the `k > 0` equivalence proof. | Verified. |
| `assertCycleIntegralUsesGapCycle(cycle)` | `cycle.integral = CycleIntegral(cycle.head, cycle.gapCycle.memCycle)`. | Makes the integral object explicit when comparing against the Spec-built `CycleIntegral`. | Required alias if Stainless does not unfold the field directly. |

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
| `assertSpecCycleApplyPositiveMatches(spec, cycle, k)` | If `k > 0`, prime lists correspond, and gap cycles match, then `spec(k) = cycle(k)`. | Main positive-index theorem. | Required. |
| `assertSpecCycleApplyMatches(spec, cycle, k)` | For all `k >= 0`, if prime lists correspond and gap cycles match, then `spec(k) = cycle(k)`. | Final local equivalence theorem for one stage. | Required. |
| `assertSpecCycleNextResiduePipelineMatches(spec, cycle)` | If the Cycle gap cycle is constructed by the residue pipeline for the same stage, then the gap-cycle-match precondition of `assertSpecCycleApplyMatches` holds. | Connects the final theorem to the actual construction path we want to trust. | Required after residue work. |

### H. Optional/Deferred Walk Pipeline Bridge

The current recommendation remains to prove the residue pipeline first. The walk
pipeline is closer to `next()` as written, but it is harder because it walks
through `CycleSieveSequence.apply`, which already depends on the gap cycle.

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

**Recommendation:** Start with Option B. Defer the residue-pipeline-to-walk
equivalence to a separate subticket.

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

### Work item 2: Phase 3 — V0 residue gap construction

Prove that the residue pipeline (Path A in `SieveSequenceNextLevel`) produces the
same gap list for V2's primes as V0's `gapList(0, p)`.

**Key lemma needed:**
```
V0.gapList(0, p) == SieveSequenceNextLevel.nextRotatedGapsV2(v2Seq)
```
for corresponding prime lists.

**Estimated complexity:** High. Requires:
- Mapping V0's `filterValues` to V2's `primes.tail`.
- Proving the residue set is the set of values coprime to the filter primes in `[0, modulus)`.
- Proving the expanded + filtered set is the survivor set in `[head, head * modulus)`.
- Proving `calculateGaps` on the sorted survivor set produces the same gaps as
  `gapList(0, p)`.

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

### 2026-06-22 — Cycle positive apply alias

Added `SpecCycleSieveEquivalence.assertCycleApplyPositiveIsIntegral`.

- **What it proves:** For every positive `position`,
  `cycle(position) == cycle.integral(position - 1)`.
- **Why it matters:** This names the positive branch of
  `CycleSieveSequence.apply` so the eventual `k > 0` equivalence proof can
  rewrite the Cycle side into the same integral form as the Spec gap-cycle
  reconstruction theorem.
- **Validation:** Focus-verified with
  `just verify assertCycleApplyPositiveIsIntegral` (3 valid, 0 invalid,
  0 unknown), then full-verified with `just verify` (7829 valid, 0 invalid,
  0 unknown).

## Related Tickets

- `v0-gap-list-cycle-formalization.md` — prerequisite: V0's internal gap cycle
  properties must be fully verified before this ticket can consume them.
- `remove-extern-from-next.md` — tracks removing @extern from V2.next(). May
  be partially unblocked by the gap periodicity facts proven in V0.
- `../superseded/conditional-nextprime-gap-cycle-bridge.md` — historical
  attempt at bridging V0 and V2 concepts (superseded).
