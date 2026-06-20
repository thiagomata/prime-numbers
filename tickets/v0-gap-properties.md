# V0 Gap Properties (Positivity, Periodicity, Sum, and Count)

**Created:** 2026-06-19
**Status:** Plan phase — not yet started
**Depends on:** `v0-residue-cycle-proof.md` (P2+P3 completed, 6283 valid)

## Related Tickets

- `v0-residue-cycle-proof.md` — P2 (Residues Completeness) + P3 (Residue Periodicity) completed. Establishes `assertBlockShift` and `assertApplyResidueCycles` as foundations. Key lesson: split into smallest pieces, one lemma per verify cycle.
- `v0-apply-modulus-loop.md` — P1 `assertApplyModIsCoprime` completed. Lessons: `modZeroPlusC` over chained lemmas.
- `gap-dynamics.md` (article) — Describes neighbor-merge rule as draft. No `.holds` lemma exists.
- `gap-positivity-proof-detailed.md` — Detailed analysis of V2 gap positivity. BLOCKED on `@extern` + Euclid's lemma. V0 avoids both issues.
- `walk-based-pipeline.md` — V2 walk pipeline (COMPLETED, 4302 valid). Uses `collectGapsV2` but no equivalence proof with residue construction.

## Related Articles

- `articles/gap-dynamics.md` — Gap evolution (neighbor-merge). Draft only, no verified `.holds`.
- `articles/sieve-sequence.md` — V2 properties. Does not cover V0.

## Goal

Define `gap(k) = apply(k+1) - apply(k)` on `SieveSequenceV0` and prove a set of independent structural properties:

1. **Gap positivity**: `gap(k) > 0` for all `k >= 0`
2. **Gap periodicity**: `gap(k+p) == gap(k)` where `p = indexOfAccepted(head + M)`
3. **Gaps sum to modulus**: `sum_{i=0}^{p-1} gap(i) == M`
4. **Gap count equals residue count**: `p == residues(M, filterValues).size`
5. **Gap list matches calculateGaps** (stretch goal)

Each property is independent. If one gets stuck (3+ attempts), comment it out and move to the next.

## Current State

- 6283 valid, 0 invalid, 0 unknown
- `assertBlockShift(k, p)` — proves `apply(k+p) == apply(k) + M` in `.ensuring`
- `assertApplyResidueCycles(k, p)` — proves `Calc.mod(apply(k+p), M) == Calc.mod(apply(k), M)`
- `applyStrictlyIncreases(k)` — proves `apply(k+1) > apply(k)` (private `.holds`)
- `expandedCoprimePreservesFilter(r, i, M, values, prod)` — private, key for periodic preservation
- `assertReverseCoprimePreservation(v, M, values, prod)` — private, reverse direction
- `indexOfAccepted(value)` — public, returns `k` such that `apply(k) == value`
- `p = indexOfAccepted(head + M)` — the gap period (number of accepted values per block)
- `assertResiduesComplete(M, primes)` — every coprime value in `[0, M)` appears in residues list

## Expected State

- All reachable gap properties added as `.holds` lemmas in `SieveSequenceV0`
- 0 invalid, 0 unknown
- Properties that fail after 3 attempts are commented out with an error note

## Properties (in implementation order)

### P1: Gap positivity — `assertGapPositive(k)`

**Status:** RECOMMENDED (first, easiest)

```scala
def assertGapPositive(k: BigInt): Boolean = {
  require(k >= BigInt(0))
  apply(k + 1) - apply(k) > BigInt(0)
}.holds
```

**Strengths:** One-liner. `applyStrictlyIncreases(k)` already proves `apply(k+1) > apply(k)`. The `.holds` lemma simply repackages this as `gap > 0`.

**Risks:** Minimal. `applyStrictlyIncreases` is private but in the same class, so accessible.

**Fallback:** If timeout, inline the body of `applyStrictlyIncreases`.

### P2: Gap periodicity — `assertGapPeriodic(k, p)`

**Status:** RECOMMENDED (second)

```scala
def assertGapPeriodic(k: BigInt, p: BigInt): Boolean = {
  require(k >= BigInt(0))
  require(p >= BigInt(0))
  require(apply(p) == head.value + filterModulus)
  true
}.ensuring(res => {
  assert(assertBlockShift(k, p))
  assert(assertBlockShift(k + 1, p))
  assert(apply(k + p) == apply(k) + filterModulus)
  assert(apply(k + 1 + p) == apply(k + 1) + filterModulus)
  val g1 = apply(k + 1) - apply(k)
  val g2 = apply(k + 1 + p) - apply(k + p)
  res && g1 == g2
})
```

**Proof:**
```
gap(k+p) = apply(k+p+1) - apply(k+p)
         = (apply(k+1) + M) - (apply(k) + M)    [by assertBlockShift]
         = apply(k+1) - apply(k)
         = gap(k)
```

**Strengths:** Pure arithmetic. `assertBlockShift` handles the induction; this lemma only calls it at two offsets and compares.

**Risks:** The `.ensuring` block needs `assertBlockShift(k, p)` and `assertBlockShift(k+1, p)` to both be visible. Since `assertBlockShift` also uses `.ensuring`, the postconditions should propagate.

**Fallback:** If timeout, use `assert` calls with intermediate values (substitution chain pattern from LEARNINGS.md 6.1).

### P3: Gaps sum to modulus — `assertGapSum(p)`

**Status:** RECOMMENDED (third)

```scala
private def assertGapSum(i: BigInt, p: BigInt): Boolean = {
  require(p >= BigInt(0))
  require(i >= BigInt(0))
  require(i <= p)
  require(apply(p) == head.value + filterModulus)
  decreases(p - i)
  if (i == p) {
    sumGapFrom(0, i) == filterModulus
  } else {
    // gap(i) + sumGapFrom(i+1, p) == M  ???
  }
}.holds
```

Where `sumGapFrom(from, until)` is a helper that sums `gap(from) + ... + gap(until-1)`.

**Alternative:** Direct recursive proof with telescoping:
```
sum_{i=0}^{p-1} gap(i) = apply(p) - apply(0) = (head + M) - head = M
```

**Strengths:** Mathematical fact is simple telescoping. Build the sum recursively over the range, prove it equals `apply(until) - apply(from)`.

**Risks:** Recursive sum of BigInts may create VCs that grow with `p`. Mitigation: use structural recursion with `decreases(p - i)`.

**Fallback (no-counting approach):** Instead of summing all `p` gaps, prove the equivalent identity `apply(p) - apply(0) == M` using `assertBlockShift(0, p)`. Then prove that `sumGapFrom(0, p) == apply(p) - apply(0)` by induction on the range. This separates the telescoping into two independent lemmas.

### P4: Gap count equals residue count — `assertPeriodEqualsResidueCount(p)`

**Status:** MODERATE (fourth)

```scala
def assertPeriodEqualsResidueCount(): Boolean = {
  val p = indexOfAccepted(head.value + filterModulus)
  val R = SieveUtils.residues(filterModulus, filterValues).size
  p == R
}.holds
```

**Proof sketch:**
- `p` = number of accepted values in `[head, head + M)`
- `R` = number of coprime values in `[0, M)`
- `accepts(head + v)` iff `isCoprime(v, filterValues)` (by `expandedCoprimePreservesFilter` forward and `assertReverseCoprimePreservation` backward)
- `isCoprime(v, filterValues)` iff `contains(residues(M, filterValues), v)` (by `assertResiduesComplete` + `assertResiduesAllCoprime`)
- Therefore `p == R`

**Risks:** This requires proving a bijection between two sets, which involves `forall`-style reasoning or an explicit walk. A direct approach:
1. Prove `accepts(head + v)` → `isCoprime(v, filterValues)` (reverse preservation, already exists)
2. Prove `isCoprime(v, filterValues)` → `accepts(head + v)` (forward preservation, already exists via `expandedCoprimePreservesFilter` + `searchBoundPassesFilter`?)
3. Show `v in residues(M, filterValues)` ↔ `isCoprime(v, filterValues)` (completeness + soundness, already exist)
4. Conclude: the sets have equal size — this is the hard part in Stainless

**Fallback (easier):** Instead of proving `p == R` directly, prove a weaker statement: the gaps from one period do repeat with period `p`, and the count of gaps equals `p`. This is already covered by P2 + P3. Skip P4 if it gets stuck.

**Alternative approach:** Prove `SieveUtils.residues(M, vals).size == indexOfAccepted(head + M)` by induction on `generateResidues`. Walk `generateResidues` from 0 to M-1, counting both residues and accepted values. This is structural recursion aligned with `generateResidues`.

### P5: Gap list matches calculateGaps — `assertGapsMatchPipeline(p)`

**Status:** STRETCH GOAL (last)

Prove that the gaps produced by `calculateGaps` on the sorted expanded residues equal `[gap(0), ..., gap(p-1)]`.

**Strengths:** Would connect V0's implicit gap structure to the pipeline's explicit gap computation.

**Risks:** Requires proving the sorted expanded residues list equals `[apply(0), ..., apply(p-1)]`. This is a list-equivalence proof, which is heavy in Stainless (structural equality on lists of size p).

**Fallback:** Skip. This is not needed for any downstream property.

## Implementation Order

```
P1 → P2 → P3 → (P4?) → (P5?)
        ↑        ↑        ↑
    if stuck → skip → skip
```

Each property is a separate `.holds` lemma in `SieveSequenceV0`. After each:
1. Run `just verify`
2. If valid count increased → commit the change, move to next
3. If timeout/failure → try one alternative approach
4. If 3 total attempts fail → comment out the lemma, note the error in learning log, move to next

## Assumptions

- `applyStrictlyIncreases` remains accessible (private, same class)
- `assertBlockShift` remains accessible (private, same class)
- The `.ensuring` postcondition of `assertBlockShift` propagates to callers at different `k` offsets
- No interaction between independent gap lemmas (concurrent verification)
- `SieveSequenceV0` class structure stays unchanged (never-destroy rule)

## Risks

1. **P2 timeout**: `assertBlockShift` may not propagate through `.ensuring` at offset `k+1`. The solver may time out trying to instantiate `assertBlockShift(k+1, p)` from `assertBlockShift(k, p)`. Mitigation: use the direct approach with explicit `assert()` calls for both `k` and `k+1`.

2. **P3 induction timeout**: Recursive sum over `p` elements may create VCs proportional to `p`. For large `p` (e.g., `primorial(primes.tail)`), this may time out. Mitigation: the telescoping approach `sumGap(0, p) == apply(p) - apply(0)` avoids iterating over each element at the solver level.

3. **P4 counting timeout**: Proving set-size equality in Stainless is historically hard. The `generateResidues`-aligned recursion may time out. Fallback: comment out and move on.

4. **P5 list equivalence timeout**: List equality proofs over large lists may time out. This is a stretch goal — expected to be the hardest.

5. **Green-to-green violation**: Running `just verify` before any change is critical. Current state is 6283 valid. Any regression is unacceptable.

## Validation

- `just verify` before first change: confirms 6283 valid
- After each lemma: `just verify` — valid count >= previous, 0 invalid, 0 unknown
- `just test` after each verify cycle — all tests pass
- If lemma times out: check `verify.log` for "unknown" count increase
- After 3 failures: STOP, comment out, note error, move to next

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-19 | Ticket created. Five gap properties identified: P1 (positivity), P2 (periodicity), P3 (sum), P4 (count), P5 (pipeline match). Priorities: P1/P2/P3 are reachable; P4 moderate; P5 stretch. If stuck on any, skip and continue. | Start with P1 gap positivity. |
| 2026-06-19 | **P1: assertGapPositive** — 6285 valid (+2). One-liner lemma, body calls `applyStrictlyIncreases(k)` then returns `apply(k+1)-apply(k) > 0`. Verified instantly. | Move to P2. |
| 2026-06-19 | **P2: assertGapPeriodic** — 6306 valid (+21). Uses `.ensuring` pattern, calls `assertBlockShift` at `k` and `k+1` to prove `gap(k+p) == gap(k)`. Verified in 19.66s. | Move to P3. |
| 2026-06-19 | **P3: assertGapSum** — 6335 valid (+29). Added recursive `sumGap` helper and `assertSumGapTelescopes` lemma proving `sumGap(from, until) == apply(until) - apply(from)`. Then `assertGapSum(p)` proves `sumGap(0, p) == M`. Verified in 20.51s. | Move to P4. |
| 2026-06-19 | **P4: assertPeriodEqualsResidueCount** — FAILED (timeout). Two attempts: (1) direct `p == residues(M, F).size` timed out (2 unknowns on precondition + postcondition). (2) Added `countAcceptedBetween` + `assertCountAcceptedBetweenMatchesPeriod` — inductive postcondition timed out (120s). Root cause: connection between `countAcceptedBetween` recursion and `indexOfAccepted` requires interval-level bijection reasoning that solver can't handle. P4 is true by periodicity but proving it needs a dedicated interval-counting lemma. | Commented out P4. Skip to P5. |
| 2026-06-19 | **P5: Gap list matches calculateGaps** — SKIPPED (stretch goal, expected harder than P4). P5 would require list-equivalence proof between two independently-defined gap construction methods. | All done. Status: P1/P2/P3 verified (6335 valid), P4 failed, P5 skipped. |
