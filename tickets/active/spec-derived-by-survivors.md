# SpecDerivedBySurvivors — Value-Level Survivor Proof

**Created:** 2026-07-04
**Updated:** 2026-07-05
**Status:** 11 lemmas verified (one wrapper removed, one bridge-stub seed added). Expansion bridge approach identified; `assertModPreservesCoprime*` made public as the enabler. Bridge lemma not yet written.
**Full chapter:** 12160 valid, 0 invalid, 0 unknown.

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

### 2026-07-04 — Rotation lemma solved + head-squared edge case

- **Attempt 3 (success):** `assertNextHeadLessThanNewModulus` — **9/9 valid, 10.51s**. Proves `cycle(1) < head * modulus` for `head >= 3, modulus >= 2`. Uses `spec.apply(1).ensuring(res <= searchBound(1))` (already postcondition, no chaining) + Z3 arithmetic for `head * modulus > head + modulus`.
- Added `assertNextHeadLessThanHeadSquared` — **3/3 valid**, proves `cycle(1) < head^2` for ALL sequences (no preconditions), covers the S_0 edge case where `head=2, modulus=1` and `head*modulus=2 < 3=cycle(1)`.
- Both lemmas added to `SpecDerivedSieveSequence` AND `SpecDerivedBySurvivors`.
- Full chapter: 12138 valid, 0 invalid, 0 unknown
- OBJECTS.md updated: §6.6 52→54, §6.9 10→12, ch6 count 224→228

**Lesson:** The "wall" was never inherent — it was using the wrong tool. Two timeouts solved by using already-verified postconditions instead of re-proving via structural induction:
1. Integral monotonicity: used `assertCycleValuePositive` (which uses `assertGreaterThanAtIndex`) instead of unfolding `allGreaterThan` recursively
2. `cycle(1) < head*modulus`: used `spec.apply.ensuring` (already postcondition) instead of chaining `applyStrictlyIncreases` across `period` steps

### 2026-07-05 — Expansion bridge approach identified; lemmas made public

**Context reconstruction.** Reviewed the uncommitted working tree left by the previous
session. Two edits were in flight on `feature/prime_seq`:

1. `SpecCycleSieveEquivalence.scala` — `assertModPreservesCoprimeForPrime`,
   `assertModPreservesCoprimeRec`, `assertModPreservesCoprime` flipped
   `private def` → `def`. **Verified green** at `12160 valid, 0 invalid, 0 unknown`
   (per `logs/verify-watch.log` 02:10:56).
2. `SpecDerivedBySurvivors.scala` — removed the `assertNextHeadLessThanHeadSquared`
   delegator (still present in `SpecDerivedSieveSequence:1784`), added a stub lemma
   `assertMinimalCycleSurvivorPassSpecNextFilter(pos)`. The stub is currently a
   byte-for-byte duplicate of `assertCycleSurvivorPassesSpecNextFilter(pos)` (lines 36–42)
   — intended as a seed for the bridge lemma, not yet grown.

**Mathematical bridge identified (hand-verified, not yet in Stainless):**
`Calc.mod(integral(pos), head*modulus)` is the reduction that maps each cycle-integral
survivor into a `nextFiltered(cycle)` element. See "Expansion bridge — approach
identified" section above for the full argument.

**Decision (user, 2026-07-05):**
- "Make it public" half of the prior instruction → **done** (in-place, green).
- "Move to chapter 2" half → **rejected**. The three lemmas are entangled with
  chapter-6 `SieveUtils` helpers; chapter 2 currently has zero chapter-6 deps and moving
  them would create a backwards dependency. They stay public in place.

**Next action (deferred to next session):** write the bridge lemma
`assertCycleSurvivorAppearsInNextFiltered(pos)` by composing
`assertModPreservesCoprime` + `assertExpandedResiduesRepresentPeriod` +
`assertFilterListContainsIf`. Use the existing stub as the seed. **One lemma per verify
cycle per `<rule id="small-changes"/>`.**

### Current status assessment — Path to M3

The rotation anchor (`cycle(1) < head * modulus`) is now **SOLVED**. A bridge class
`SpecDerivedEquivalence` (4 lemmas) formally certifies that both `SpecDerivedSieveSequence`
and `SpecDerivedBySurvivors` operate on the same underlying data.

The remaining blocker for M3 is the **expansion bridge**: proving the pipeline survivors
(`nextFiltered`) correspond to the cycle-integral survivors. This is outside this class's
scope — it belongs in `SpecCycleSieveEquivalence` (which already has
`assertExpandedResiduesRepresentPeriod`).

### Expansion bridge — approach identified (2026-07-05)

**The mathematical bridge (verified by hand, not yet in code):**

For any cycle-integral survivor `integral(pos)` (where `mod(integral(pos), head) != 0`),
the reduced value `Calc.mod(integral(pos), head * modulus)` is:

1. In `[0, head*modulus)` — trivially, since it's a `mod` result.
2. **Still coprime to the tail primes** — because `head*modulus` is a multiple of every
   tail prime `p` (as `modulus = product(tailPrimes)`), reducing by `head*modulus` does
   not change `mod(_, p)`. So coprimality is preserved.
3. **Still not divisible by `head`** — `mod(mod(integral(pos), head*modulus), head) ==
   mod(integral(pos), head) != 0`.

Together, (1)+(2)+(3) put the reduced value in `nextFiltered(cycle)` via
`assertExpandedResiduesRepresentPeriod` + `assertFilterListContainsIf`. **This is the
cycle-survivor → pipeline-survivor direction.**

The reverse direction (every pipeline survivor `>= head` corresponds to a cycle-integral
survivor) is **not needed for M3**: the rotation in `nextRotatedGaps` aligns the pipeline
list to start at `cycle(1)`, chopping off any sub-`head` extras (e.g. the value `1` for
S_2). The remaining gaps then match `spec.next.gapList` via the already-proven
`assertSurvivorGapEqualsSpecNextGap`.

**Reusable fact already in the codebase:**

`SpecCycleSieveEquivalence` proves exactly the modulo-preserves-coprimality fact needed
for step (2):

- `assertModPreservesCoprimeForPrime(v, modulus, p)` — per-prime
- `assertModPreservesCoprimeRec(v, modulus, prefixProd, remaining)` — per-list, recursive
- `assertModPreservesCoprime(v, modulus, primes)` — top-level wrapper

**2026-07-05 change:** all three were flipped from `private def` to `def` (now public).
Verified green at `12160 valid`. This unblocks `SpecDerivedBySurvivors` from calling them
directly when building the bridge lemma.

**Layering note (do NOT move them to chapter 2):** An earlier plan was to *move* these
three lemmas to `ModOperations` (chapter 2) "where they belong." Investigation showed
they are entangled with `SieveUtils.assertMultiplePreservesDivisible`,
`SieveUtils.assertHeadDividesProduct`, `SieveUtils.assertIsCoprimeForAll`,
`SieveUtils.isCoprime`, `SieveUtils.product` — all chapter-6 helpers. Chapter 2 currently
has **zero** chapter-6 dependencies; moving them would create a backwards
chapter-2 → chapter-6 dependency. **Decision (user, 2026-07-05): keep them public in
place; do not move.**

**Next step (the actual M3 progress):** write the bridge lemma in
`SpecDerivedBySurvivors` — tentatively `assertCycleSurvivorAppearsInNextFiltered(pos)` —
which composes `assertModPreservesCoprime` + `assertExpandedResiduesRepresentPeriod` +
`assertFilterListContainsIf` to prove that every cycle-integral survivor's
`mod(_, head*modulus)` reduction appears in `nextFiltered(cycle)`. The current stub
`assertMinimalCycleSurvivorPassSpecNextFilter(pos)` (a duplicate of the existing lemma at
lines 36–42) is the seed for this — it should be grown into the real bridge lemma.

### Summary of what the class proved (11 verified lemmas + 1 stub seed)

| # | Lemma | VCs | What it proves |
|---|-------|-----|----------------|
| 1 | `assertCycleSurvivorCoprimeToCyclePrimes(pos)` | 8 | Survivor coprime to all primes |
| 2 | `assertSpecNextFilterEqCyclePrimes()` | 5 | `spec.next.filterValues == cyclePrimes` |
| 3 | `assertCycleSurvivorCoprimeToSpecNextFilter(pos)` | 10 | Survivor coprime to next filter |
| 4 | `assertCycleSurvivorPassesSpecNextFilter(pos)` | 8 | Survivor passes next filter (no `>=`) |
| 5 | `assertFirstSurvivorEqualsSpecNextHead()` | 4 | `integral(0) == spec.next.head.value` |
| 6 | `assertAllSurvivorsPassSpecNextFilter(count)` | 10 | All survivors in `[0,count)` pass filter |
| 7 | `assertAllSurvivorsPassSpecNextFilterFrom(from,count)` | 11 | Same, from arbitrary start |
| 8 | `assertIntegralIncreasingForCount(count)` | 14 | `integral(pos) < integral(pos+1)` |
| 9 | `assertIntegralGeIntegral0(pos)` | 20 | `integral(pos) >= integral(0)` |
| 10 | `assertSurvivorAcceptedBySpecNext(pos)` | 12 | Survivor accepted by `spec.next.accepts` |
| 11 | `assertNextHeadLessThanNewModulus()` | 9 | `cycle(1) < head * modulus` |
| — | `assertMinimalCycleSurvivorPassSpecNextFilter(pos)` | (stub) | **Seed for the bridge lemma — currently a duplicate of #4, to be grown into `assertCycleSurvivorAppearsInNextFiltered`** |

**Note:** `assertNextHeadLessThanHeadSquared()` was removed from this class on 2026-07-05
(it was a one-line delegator). It still lives in `SpecDerivedSieveSequence.scala:1784`,
so no proof was lost.

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
