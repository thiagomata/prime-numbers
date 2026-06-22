# V0-V2 Apply Equivalence

**Status:** Active coordination ticket
**Created:** 2026-06-22
**Depends on:** `v0-gap-list-cycle-formalization.md` (items 1-11 fully verified)

## Goal

Prove that `SieveSequenceV0` and `SieveSequenceV2` generate the same values when
constructed from corresponding prime lists:

```
SieveSequenceV0(AllPrimesSoFarList(SortedPrimeList(primes.map(Prime(_))))).apply(k)
  ==
SieveSequenceV2(primes, gapCycle).apply(k)

for all k >= 0 and for every valid sieve stage.
```

## Current State

- **V0 properties (prerequisite):** Most gap properties are verified in
  `SieveSequenceV0` (see `v0-gap-list-cycle-formalization.md`). Items 7
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

Build a lemma (in `SieveSequenceV0` or a companion) that:
1. Computes `p = indexOfAccepted(head.value + filterModulus)`.
2. Computes `gaps = gapList(0, p)`.
3. Builds `GapCycle(gaps)`.
4. Proves `CycleIntegral(head, GapCycle(gaps).memCycle).apply(k) == apply(k+1)`.

**Estimated complexity:** Medium. The GapCycle construction and integral equality
follow directly from V0's gap properties, but constructing the concrete objects
inside Stainless may require handling constructor preconditions
(`allGreaterThan(_, 0)`, non-empty).

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
def assertV0EqualsV2(v0: SieveSequenceV0, v2: SieveSequenceV2, k: BigInt): Boolean = {
  require(k >= 0)
  // prime list correspondence
  // gap cycle equality
  v0.apply(k) == v2.apply(k)
}.holds
```

**Estimated complexity:** Very high. Depends on items 1-2.

### Work item 4: Phase 4 — Inductive stage bridge (future)

Prove that `V0.next().apply(k) == SieveSequenceV2(v2.primes.next, ...).apply(k)`
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
   explicitly SKIPPED in SieveSequenceV0 (see OBJECTS.md line 976: counting
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

**Status:** Rename execution underway. Following AGENTS.md rules: one change per verify cycle, green-to-green throughout.

**Assumptions unchanged:** Prime list representation mismatch (risk 1), residue vs. walk pipeline (risk 2), gap cycle construction preconditions (risk 3), period length equivalence (risk 4) — none affected by the rename.

## Related Tickets

- `v0-gap-list-cycle-formalization.md` — prerequisite: V0's internal gap cycle
  properties must be fully verified before this ticket can consume them.
- `remove-extern-from-next.md` — tracks removing @extern from V2.next(). May
  be partially unblocked by the gap periodicity facts proven in V0.
- `../superseded/conditional-nextprime-gap-cycle-bridge.md` — historical
  attempt at bridging V0 and V2 concepts (superseded).
