# Remove @extern from CycleSieveSequence.next()

**Created:** 2026-06-13
**Status:** Phase 1 in progress
**Depends on:** `sieve-properties-step5-coprime-to-modulus.md` (✅ 5230 valid)

---

## Goal

Remove `@extern` from `CycleSieveSequence.next()` by proving all VCs that it currently bypasses.

---

## The Four Phases

### Phase 1: Gap Positivity (A2a + A2b) — IN PROGRESS

Prove `ListBoundUtils.allGreaterThan(gaps, BigInt(0))` for the result of `nextGapsWalkV2`.

**Key existing lemmas:**
- `assertCycleIntegralIncreasing(ci, a, b)` (CycleIntegralProperties.scala:16) — `b > a ⟹ ci(b) > ci(a)` ✅
- `assertDiffEqualsCycleValue(ci, a)` (CycleIntegralProperties:143) — `ci(a+1) - ci(a) == ci.cycle(a+1)` ✅
- `assertCycleValuePositive(ci, pos)` (CycleIntegralProperties:347) — `ci.cycle(pos) > 0` ✅

**Previous attempt** (SieveSequenceNextLevel.scala:69-94, commented-out) failed because:
- Used `%` operator instead of `Calc.mod` (project rule violation)
- Solver couldn't verify `current - lastSurvivor > 0`

**Fix:**
- Use `Calc.mod` for all modulo operations
- Add explicit `assert(current > lastSurvivor)` before computing gap
- Leverage already-verified `assertCycleIntegralIncreasing`

### Phase 2: New Head Coprimality (Blocker B) — NOT STARTED

Prove that the new head (`seq.apply(1)`) is coprime to `primes.tail`.

**Approach:** Add `assertNextHeadCoprimeToPrimes(seq)` in SieveSequenceNextLevel.
Uses `assertAllRExpandedCoprime` (already verified in Step 5).

### Phase 3: NonEmpty (A1) — NOT STARTED

Prove `gaps.nonEmpty` for the result of `nextGapsWalkV2`.

**Difficulty:** HIGH. This requires proving at least one survivor exists after filtering by `head`. Needs `head ∤ modulus` (Euclid's lemma).

**Approach options:**
- Option A: Prove Euclid's lemma (prime doesn't divide product of distinct primes)
- Option B: Add `require(Calc.mod(product(primes.tail), primes.head) != 0)` to CycleSieveSequence (structural invariant)
- Option C: Scope invariant to `nextGapCycleV2` require instead of full structural proof

### Phase 4: Remove @extern — NOT STARTED

Remove `@extern` annotation from `next()`. After Phases 1-3 prove all requires reachable from `next()`, this should be trivial.

---

## Related Tickets

| Ticket | Status | Relevance |
|--------|--------|-----------|
| `gap-positivity-proof.md` | Planning | Analyzes VC #2 (gap > 0) and VC #1 (nonEmpty) |
| `gap-positivity-proof-detailed.md` | Planning | Detailed trace of previous attempt |
| `sieve-properties-step5-coprime-to-modulus.md` | ✅ Complete | Added structural `isCoprime` invariant |
| `cycle-value-positive-or-zero.md` | Complete | Lemma regarding cycle values |

---

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-13 | Created ticket with 4-phase plan. Verified current state: 5230 valid. | Phase 1: Rewrite using `Calc.mod`, add explicit `current > lastSurvivor` assertion. |
| 2026-06-13 | **Phase 1 complete.** Added `assertCollectGapsV2AllPositive` + `assertAllGreaterThanReverse` to SieveSequenceNextLevel. 5292 valid. All 9 tests pass. | Proceed to Phase 2. |
| 2026-06-13 | **Phase 2 complete.** Added structural invariants to CycleSieveSequence: `isCoprime(apply(1), primes.tail)` and `mod(apply(1), head) != 0`. Expressed as direct computations (`primes.head + gapCycle.memCycle(0)`) because `integral` val is not yet initialized during require. 5300 valid. | Proceed to Phase 3. |
| 2026-06-13 | **Phase 3 structural invariant added.** Added `Calc.mod(SieveUtils.product(primes.tail), primes.head) != 0` to CycleSieveSequence. 5303 valid. | Attempted Phase 4 (remove @extern). |
| 2026-06-13 | **Phase 4 BLOCKED.** Removing @extern causes timeout on `gaps.nonEmpty` VC in `nextGapCycleV2`. The solver can't prove at least one survivor is found in `head * gapCycle.size` walk steps. This requires a periodicity/Euclid lemma that `mod(modulus, head) != 0` causes residues to cycle through all non-zero values modulo head. | ASK FOR HELP on nonEmpty proof strategy. |
