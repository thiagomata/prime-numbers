# SpecDerivedBySurvivors — Value-Level Survivor Proof

**Created:** 2026-07-04
**Updated:** 2026-07-04
**Status:** 6 lemmas verified (filter-passing chain + bulk induction).

---

## START HERE

### Goal

Create a new class `SpecDerivedBySurvivors` that wraps `SpecDerivedSieveSequence` and builds the survivor-to-next-stage equivalence proof using the **value-level approach** (coprimality chains, `passesFilter` instead of `accepts`, no index-based `nextAcceptedOldIndex` machinery). This is the "NEW APPROACH: SieveCycleAfterProof" path described in `independent-next-cycle.md` §C.1.1, restarted cleanly in its own class.

### Why a new class instead of the contract migration

- Does NOT modify any existing verified code
- Does NOT need the 9-function coupled require migration (which broke HEAD before)
- Builds incrementally, one lemma per verify cycle
- Reuses existing verified lemmas (`assertNextHeadMatches`, `assertCycleValueCoprimeToTail`, etc.)

### Architecture

```
SpecDerivedBySurvivors(derived: SpecDerivedSieveSequence)
  └── derived.spec, derived.cycle, derived.period  (delegated)
  └── Lemma chain:
        assertFirstSurvivorEqualsSpecNextHead()
        assertCycleSurvivorCoprimeToCyclePrimes(pos)
        assertSpecNextFilterEqCyclePrimes()
        assertCycleSurvivorCoprimeToSpecNextFilter(pos)
        assertCycleSurvivorPassesSpecNextFilter(pos)
        assertFirstSurvivorEqualsSpecNextHead()
        assertAllSurvivorsPassSpecNextFilter(count)
        ──→ (future: pipeline bridge, merge-sum, sortedness)
```

Each lemma reuses existing verified methods from `SpecDerivedSieveSequence`, adding value-level reasoning on top.

### Current state

Green: `12057 valid: 0 invalid: 0 unknown`

### Original micro-goal (done)

The 5 `SieveCycleAfterProof` lemmas + bulk induction — all 6 verified.

---

## Progress Log

### 2026-07-04 — Ticket created

- Green baseline: 12012 valid, 0 invalid, 0 unknown
- First micro-goal planned: `assertCycleSurvivorCoprimeToCyclePrimes(pos)` in new class `SpecDerivedBySurvivors`
- Reference: article `sieve-sequence.md` §C.1.1 documents the value-level approach
- Reference: `independent-next-cycle.md` §"NEW APPROACH: SieveCycleAfterProof" (5 commented-out lemmas)
- Reference: OBJECTS.md §6.6 for existing `SpecDerivedSieveSequence` lemmas

### 2026-07-04 — Lemma 1 verified

- Created `SpecDerivedBySurvivors.scala` (wraps `SpecDerivedSieveSequence`)
- Added `assertCycleSurvivorCoprimeToCyclePrimes(pos)` — verified 8/8
- Full chapter: 12020 valid, 0 invalid, 0 unknown (no regressions)
- Key discovery: no new groundwork needed — `primeValues` `.ensuring` already proves `result.head == primes.head.value`, and `checkAllPositive` delegates to `allGreaterThan`
- `assertFirstSurvivorEqualsSpecNextHead` would have duplicated existing `assertFirstSurvivorEqualsSpecNext0()` in SpecDerivedSieveSequence — skipped it
- OBJECTS.md updated with new §6.9 entry, ch6 count bumped from 214→215

### 2026-07-04 — Lemma 2 verified

- Added `assertSpecNextFilterEqCyclePrimes()` — verified 5/5, proves `spec.next.filterValues == cyclePrimes`
- Full chapter: 12025 valid, 0 invalid, 0 unknown
- Uses only `assertPrimesMatch()` + structural fact `spec.next.filterPrimes == spec.primes.list.list` (from `SpecSieveSequence` construction)
- OBJECTS.md §6.9 updated, ch6 count 215→216

### 2026-07-04 — Lemmas 3-5 verified (full chain complete)

- **Lemma 3** `assertCycleSurvivorCoprimeToSpecNextFilter(pos)` — 10/10: combines lemmas 1+2
- **Lemma 4** `assertCycleSurvivorPassesSpecNextFilter(pos)` — 8/8: uses `passesFilter` (no `>=` precondition)
- **Lemma 5** `assertFirstSurvivorEqualsSpecNextHead()` — 4/4: delegates to existing `assertFirstSurvivorEqualsSpecNext0()`
- Full chapter: 12047 valid, 0 invalid, 0 unknown
- OBJECTS.md §6.9 table complete with all 5 lemmas, ch6 count 216→219

### 2026-07-04 — Lemma 7: generalized bulk induction

- Added `assertAllSurvivorsPassSpecNextFilterFrom(from, count)` — 11/11
- Full chapter: 12068 valid, 0 invalid, 0 unknown
- OBJECTS.md §6.9 updated, ch6 count 220→221

### 2026-07-04 — F5 wall hit: `assertCycleIntegralIncreasing` timeout

- Attempted `assertCycleIntegralIncreasing(count)` — direct induction on `integral(pos) < integral(pos+1)`
- **Timed out** at 300s — naive induction without intermediate lemmas
- Reverted, back to green

### 2026-07-04 — F5 timeout during rotation lemma attempt

- Attempted `assertNextHeadLessThanNewModulus` — proves `cycle(1) < head * modulus` for rotation, needed `spec(1) < head + filterModulus` which requires chaining monotonicity across `period` steps — **timed out** at 300s
- This is the same monotonicity wall (F5) — chaining `applyStrictlyIncreases` across a symbolic period is too expensive
- Reverted — the class stays at 10 lemmas, all green

### Status Assessment — Path to M3

The class has proven its core mission: survivors pass the next filter (value-level, no `>=` precondition)
and are accepted by `spec.next.accepts`. The remaining path to M3 requires:

1. **Expansion bridge**: prove that the pipeline's `nextFiltered` contains exactly the cycle-integral
   survivors. This is partially solved by `assertExpandedResiduesRepresentPeriod` (for values in
   `[0, head*modulus)`), insufficient for later survivors beyond one period.

2. **Rotation anchor**: prove `nextHeadResidueIndex(cycle) == 0`. Requires `cycle(1) < head * modulus`
   which timed out due to monotonicity chaining.

3. **Composition**: combine pipeline gaps with `spec.next.gapList` equality. This builds on
   `assertSurvivorGapEqualsSpecNextGap` (already verified).

These three items require the expansion bridge + periodic reasoning, which is the remaining
hard problem for the independent-next-cycle ticket.

### Next direction

The class is at a natural stopping point. The next steps toward M3 (expansion bridge,
rotation proof) are outside this class's scope — they belong in the pipeline proofs
(`SieveSequenceNextLevel`, `SpecCycleSieveEquivalence`).

Consider reviewing `tickets/active/independent-next-cycle.md` for the coordinated plan,
especially S5 (sortedness preservation) or S6 (filter merge/sum) which are pipeline-related
and could leverage this class's results.

### Next steps

The class now has per-position AND bulk survivor filter-passing proofs. The next work toward the epic (M3: `nextRotatedGaps(cycle) == spec.next.gapList`):
- **Pipeline filter bridge**: connect cycle-integral survivors to `nextFiltered(cycle)` — both produce same survivors
- **Merge-sum bridge**: prove that gaps between consecutive survivors equal sums of original gaps (S6 from independent-next-cycle plan)
- **Sortedness**: prove `nextFiltered` preserves order (S5)

All of these are smaller sub-steps than "ordered survivor equality." Update this ticket once the next direction is clear.

### What the 5-lemma chain proves

For any `pos >= 0` where `mod(cycle.integral(pos), spec.head.value) != 0`:

1. `isCoprime(integral(pos), cyclePrimes)` — coprime to all primes
2. `spec.next.filterValues == cyclePrimes` — next-stage filter = full primes
3. `isCoprime(integral(pos), spec.next.filterValues)` — coprime to next filter
4. `spec.next.passesFilter(integral(pos))` — passes next filter (no `>=` precondition)
5. `integral(0) == spec.next.head.value` — first survivor = next stage head

### Next steps

The 5-lemma chain from `SieveCycleAfterProof` is now fully verified in `SpecDerivedBySurvivors`. The next work is:
- Ordered survivor equality (ladder step 6): prove that `spec.next(k)` values appear as cycle-integral survivors in order
- Gap equality (ladder step 9)
- Rotation equality (ladder steps 10-11 → M3)

---

## Lessons Learned

- **Don't plan duplicates first**: Check what's already proved in lower-chapter objects before planning new lemmas
- **`.ensuring` on `primeValues` covers the head equality need**: No new lemma in PrimeUtils was needed for `cyclePrimes.head == spec.head.value`
- **Value-level approach works**: the coprimality chain lemma verified (8/8 in 11.97s) — the basic approach is sound and fast
- **Next lemma**: `assertSpecNextFilterEqCyclePrimes()` to show `spec.next.filterValues == cyclePrimes`

---

## Related Tickets

- `tickets/active/independent-next-cycle.md` — parent ticket, M3 target (`nextRotatedGaps(cycle) == spec.next.gapList`)
- `tickets/sieve-sequence-epic.md` — epic overview
