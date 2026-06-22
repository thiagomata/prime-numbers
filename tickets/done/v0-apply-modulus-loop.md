# V0 Apply Modulus Loop: Residue Cycle Properties

**Created:** 2026-06-19
**Status:** Plan phase — not yet started
**Depends on:** v0-next-level-construction.md (completed, 5992+ valid)

## Related Tickets

- `sieve-properties-step5-coprime-to-modulus.md` — V2 coprime-to-modulus proof (completed). Most relevant: structural invariant approach, `assertMultiplePreservesDivisible` lemma, `assertExpandedCoprime` lemma, `assertResiduesAllCoprime`. This ticket targets the same concept (mod residues are coprime) but for V0's linear-scan generator, which is structurally different from V2's gap-cycle.
- `sieve-sequence-residue-representation-proof-object.md` — V2 residue representation. Valuable lessons on timeout splitting (big combined lemmas timeout — split into smaller pieces).
- `prove-apply1-is-prime.md` — V0 apply(1) primality (OPEN). Demonstrates that deep number theory is beyond SMT; our properties should stay structurally verifiable.
- `primorial-not-divisible-by-new-prime.md` — Euclid's lemma is NOT yet proved in the codebase. Our approach does NOT need Euclid's lemma (no multiplication needed — we use `assertAddPreservesNotZeroMod` and `APlusMultipleTimesBSameMod`).
- `check-project-guidance-docs-2026-06-17.md` — V0 implementation history. Key: generated values do NOT need to be prime, only coprime with filter primes.

## Goal

Verify structural properties about `Calc.mod(SpecSieveSequence.apply(k), filterModulus)` where `filterModulus = product(filterValues)`:

1. **P1 (Foundation)**: `isCoprime(Calc.mod(apply(k), filterModulus), filterValues)` — the residue modulo M is also coprime
2. **P2 (Membership)**: The residue belongs to the residues list
3. **P3 (Periodicity / Loop)**: The residues cycle with period = number of residues

## Current State

- `SpecSieveSequence` verified (5992+ valid)
- `apply(k)` postcondition: `res >= head.value && res <= searchBound(k) && accepts(res)` — i.e., `isCoprime(res, filterValues)`
- The key bridge lemmas **already exist** in the codebase:
  - `SieveUtils.assertMultiplePreservesDivisible(a, b, p)` (SieveUtils:117) — if `Calc.mod(b, p) == 0` then `Calc.mod(a * b, p) == 0`
  - `ModOperations.modAdd(a, c, b)` — relates `mod(a + c, b)` to `mod(a, b)` and `mod(c, b)`
  - `ModIdempotence.modIdempotence(a, b)` — `mod(mod(a, b), b) == mod(a, b)`
  - `SieveUtils.assertAddPreservesNotZeroMod(v, p, add)` — `mod(v, p) != 0` and `mod(add, p) == 0` implies `mod(v + add, p) != 0`
  - `SieveUtils.assertExpandedCoprime(r, i, modulus, primes)` — `r + i*modulus` stays coprime with all primes
  - `SieveUtils.assertResiduesAllCoprime(modulus, primes)` — all residues are coprime (soundness, NOT completeness)
  - `AdditionAndMultiplication.APlusMultipleTimesBSameMod(a, b, m)` — `mod(a + b*m, b) == mod(a, b)` for `m >= 0`

## Expected State

**P1 (Foundation)**: `assertApplyModIsCoprime(k)` verified in SpecSieveSequence.

**P2 (Membership)**: After adding a residues-completeness lemma, `assertApplyModInResiduesList(k)` verified.

**P3 (Loop)**: `assertApplyResiduePeriodicity(k)` verified — the "loop around M" property.

## Alternatives Considered

### For P1

**A1. Chain existing lemmas directly in V0** (RECOMMENDED):
- No new sub-lemmas needed. The chain `assertMultiplePreservesDivisible` + `modAdd` + `modIdempotence` bridges from `accepts(apply(k))` to `isCoprime(mod(apply(k), M), filterValues)`.
- Uses `assertIsCoprimeForAll` to expand `accepts(res)` over filterValues, then per-prime reasoning.
- Risk: minimal — only combines existing verified lemmas.

**A2. New sub-lemma**: Write a dedicated `modPreservesCoprimeRemainder` lemma in SieveUtils.
- Cleaner but duplicates existing functionality.
- Not needed — the existing lemmas chain directly.

### For P2

**B1. Add `assertResiduesComplete` lemma** (RECOMMENDED):
- Since `generateResidues` scans every value in `[0, M)`, completeness is true by construction.
- New lemma: `assertResiduesContainsAllCoprime(M, primes)` — if `isCoprime(v, primes)` and `0 <= v < M`, then `contains(residues(M, primes), v)`.
- Requires a `contains` helper or a custom membership lemma.

**B2. Skip P2**:
- P1 already gives the algebraic result without needing the residues list.
- P2 is "cosmetic" — nice for connecting to the residues concept but not necessary for P3.

### For P3

**C1. Counting-based proof** (RECOMMENDED):
- Prove: in any interval `[v, v + M)`, there are exactly R accepted values (where R = residues list size).
- Then: `apply(k + R) = apply(k) + M` and therefore `mod(apply(k+R), M) = mod(apply(k), M)`.
- Requires: `assertAcceptedCountInInterval` — a blocking/filtering lemma.

**C2. Direct periodic enumeration**:
- Show that the `accepts` predicate is periodic with period M (already provable via `assertExpandedCoprime`).
- Show that the sequence of residues of `apply(k)` mod M cycles because there are only finitely many residues.
- Weaker: only proves that EVERY residue repeats eventually, not that the period equals R.

**C3. Skip P3**:
- P1 is the foundational property. P3 is the "loop" but may require significant counting lemmas.
- Risk: counting arguments in Stainless can be heavy.

## Assumptions

- `assertMultiplePreservesDivisible`, `modAdd`, `modIdempotence` chain correctly (verified in their respective files)
- `assertIsCoprimeForAll` expands `accepts(res)` to per-prime mod facts
- `filterModulus > 0` (established by constructor)
- `filterValues` contains only positive values (by construction from primes)

## Risks (from related tickets)

1. **Timeout on postcondition chaining**: `sieve-sequence-residue-representation-proof-object.md` had timeout issues when proving `assertAcceptsAfterAddingModulus` as a single lemma. **Mitigation**: Split P1 into per-prime assertions (one assert per filter prime, then combine).
2. **Euclid's lemma NOT available**: `primorial-not-divisible-by-new-prime.md` documents that Euclid's lemma is not yet proved. **Not a risk for P1**: we use addition-based reasoning (modAdd, assertMultiplePreservesDivisible), never product-of-two-coprime-numbers.
3. **Counting argument complexity**: P3 may require heavy lemmas about quantity of accepted values per block. **Mitigation**: Start with P1 only; evaluate P3 feasibility after P1 is verified.
4. **3-failure rule**: If P3 exceeds 3 attempts, stop and ask for help.

## Validation

- `just verify` must pass green-to-green before and after each change
- Verification count must not decrease
- One assertion/lemma per change (AGENTS.md small-changes rule)
- Ticket updated after each interaction loop

## Hypotheses to Validate

| Hypothesis | How to Validate |
|------------|----------------|
| `assertMultiplePreservesDivisible` + `modAdd` + `modIdempotence` chain proves `Calc.mod(r, p) != 0` | Write a standalone test lemma first, then add to V0 |
| `assertIsCoprimeForAll` connects `accepts(res)` to per-prime mod facts | Inspect the lemma's signature and try in a test |
| P1 can be proved without any new sub-lemmas | Attempt to write P1 using only `assert()` calls to existing lemmas |
| The residues count can be expressed without timeout | Check if `residues(...).size` is computable without VC explosion |

## Notes on Related Ticket Freshness

- `sieve-properties-step5-coprime-to-modulus.md` — Dated 2026-06-13. Status says "Analysis Complete — Awaiting Implementation Decision" but the learning log shows it was completed (5230 valid). V0 is structurally different from V2 so the approach differs, but the `assertMultiplePreservesDivisible` and `assertExpandedCoprime` lemmas built there are foundational to P1.
- `sieve-sequence-residue-representation-proof-object.md` — Dated 2026-06-15 at 5349 valid. V0 landscape has advanced significantly (now 5992+). The timeout lesson (big lemma → split) is still valid.
- `prove-apply1-is-prime.md` — Still OPEN. Deep number theory problem. Confirms we should NOT try to prove primality; focus on structural coprime properties.
- `primorial-not-divisible-by-new-prime.md` — Dated 2026-06-19 at 6006. Euclid's lemma still unproved. Confirms our approach avoids needing it.
- All tickets written before the V0 linear-scan architecture was finalized may describe approaches that no longer apply. Focus on the lemmas and lessons, not the architectural proposals.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-19 | Ticket created. Three properties identified (P1 foundation, P2 membership, P3 loop). Key bridge lemmas already exist in codebase. Euclid's lemma not needed. P3 may be complex. Related tickets checked for lessons, with freshness noted. | Start with P1 implementation. |
| 2026-06-19 | **P1 Attempt 1 FAILED** — used recursion with `require(modulus == SieveUtils.product(values))` precondition. Timeout on `Calc.mod(r, p) != 0` (body assertion) and `require(modulus == SieveUtils.product(values.tail))` (recursive call). The latter fails because `modulus == product(values)` does NOT imply `modulus == product(values.tail)` (it's `p * product(values.tail)`). | Restructure to use prefix-product approach (like `expandedCoprimePreservesFilter`). |
| 2026-06-19 | **P1 Attempt 2 FAILED** — switched to prefix-product decomposition. Same two timeouts persisted: `Calc.mod(r, p) != 0` (body assertion) and `modulus == newPrefix * tailProd` (product equality for recursion). | Replace `modAdd` + `modIdempotence` with `modZeroPlusC` which directly proves `mod(a+c, b) == mod(c, b)` when `mod(a, b) == 0`. Add explicit `assert(value == q * modulus + r)`. |
| 2026-06-19 | **P1 SUCCEEDED** — 6059 valid, 0 invalid, 0 unknown. Key changes: `modZeroPlusC` instead of `modAdd`+`modIdempotence`; explicit `assert(value == q * modulus + r)`; explicit `assert(product(values) == p * tailProd)` and `assert(modulus == newPrefix * tailProd)`. All 171 tests pass. | P1 complete. Ready for P2 or P3. |
