# V0 Residue Cycle Proof (P2 + P3)

**Created:** 2026-06-19
**Status:** Planning — not yet started
**Depends on:** `v0-apply-modulus-loop.md` (P1 verified, 6059 valid)

## Related Tickets

- `v0-apply-modulus-loop.md` — P1 `assertApplyModIsCoprime` completed. Documents timeout issues with `modAdd`+`modIdempotence` solved by using `modZeroPlusC` directly.
- `sieve-properties-step5-coprime-to-modulus.md` — V2 coprime-to-modulus proof. `assertResiduesAllCoprime` proves soundness of residues (all are coprime) but NOT completeness. Path E stored residues as a structural field.
- `sieve-sequence-residue-representation-proof-object.md` — Tried `assertAcceptsAfterAddingModulus` as one lemma; timeout. Lesson: split into smaller pieces.
- `primorial-not-divisible-by-new-prime.md` — Euclid's lemma not yet proved. Not a concern here (no product-of-coprime reasoning needed).
- `prove-apply1-is-prime.md` — Still OPEN. Deep number theory. Our property is structural, not about primality.
- `v0-next-level-construction.md` — Lessons: `.ensuring` on class methods breaks type inference; one lemma at a time.
- `complete-prime-prefix-sieve-cycle.md` — Discusses SieveSequenceV0's bounded search shape.

## Related Articles

- `articles/cycle.md` — Defines Cycle, periodicity. Property 5.3 `valueMatchAfterManyLoops` proves `cycle(key) == cycle(key + size*m)`. This is the same periodicity pattern we want to prove for V0's residues.
- `articles/integral-cycle.md` — CycleIntegral. If we eventually construct a gap cycle from V0 residues, CycleIntegral is the mechanism.
- `articles/sieve-sequence.md` — Documents V2 sieve properties. Does NOT cover V0. Focuses on gap-cycle pipeline.
- `articles/modulo.md` — Foundational modulo properties used by P1 (`modZeroPlusC`, `modIdempotence`).
- `articles/list.md` — List properties including containment checks (relevant for P2).

## Goal

Add two properties on top of P1:

### P2: Residues Completeness

```
assertResiduesComplete(M, primes):
  forall v in [0, M): if isCoprime(v, primes) then contains(residues(M, primes), v)
```

Prove that every coprime value in `[0, M)` belongs to the residues list. Currently only soundness is proved (`assertResiduesAllCoprime` — all residues are coprime). Completeness follows from the construction of `generateResidues` which scans every value.

### P3: Residue Periodicity (the Loop)

```
assertApplyResidueCycles(k):
  Calc.mod(apply(k + R), filterModulus) == Calc.mod(apply(k), filterModulus)
```

where `R = residues(filterModulus, filterValues).size`.

This is the "loop around M" property. It requires proving `apply(k + R) == apply(k) + filterModulus`.

## Current State

- P1 `assertApplyModIsCoprime` verified at 6059
- `assertResiduesAllCoprime` exists (SieveUtils:716) — proves soundness only
- `generateResidues` (SieveUtils:242) scans `[0, M)` and collects coprime values — complete by construction but unproven
- `SieveSequenceV0` has `indexOfAccepted(value)` — returns the unique k such that `apply(k) = value`
- `expandedCoprimePreservesFilter` proves: if `isCoprime(r, values)` and `modulus = product(values)`, then `isCoprime(r + i*modulus, values)`
- `searchBoundPassesFilter(k)` proves `searchBound(k) = head + k*M` is always accepted
- `apply(k)` postcondition: `accepts(res)`, strict monotonicity proven by `applyStrictlyIncreases`
- V0 completeness: `indexOfAccepted(value)` returns an index for any accepted value

## Expected State

- P2: `assertResiduesComplete(M, primes)` verified in SieveUtils
- P3: `assertApplyResidueCycles(k)` verified in SieveSequenceV0
- 0 invalid, 0 unknown

## Approaches Considered

### P2: Single lemma in SieveUtils

Add `assertResiduesComplete` by structural induction on `[0, M)`.

```scala
def assertGenerateResiduesComplete(i: BigInt, modulus: BigInt, primes: List[BigInt]): Boolean = {
  require(i >= 0)
  require(i <= modulus)
  require(modulus > 0)
  require(ListUtils.checkAllPositive(primes))
  require(isCoprime(i, primes))
  decreases(modulus - i)
  if (i == modulus) false  // i = modulus is never coprime (modulus ≡ 0 mod each prime)
  else if (contains(generateResidues(i, modulus, primes), i)) true
  else assertGenerateResiduesComplete(i + 1, modulus, primes)
}.holds
```

**Risk**: `contains` on a list is recursive and may cause VC explosion. Alternative: use `ListUtils.valueExistInList`.

**Risk**: `generateResidues` is already called in `residues`. Adding a completeness lemma might duplicate computation (if we call `generateResidues` again) or require sharing the same list.

**Alternative**: Prove `contains(residues(M, primes), v)` by structural recursion on the result of `residues(M, primes)`, without re-scanning. This is more efficient but requires a custom lemma about `generateResidues`'s structure.

### P3: Three sub-steps

#### Step 1: Counting lemma
Prove that in any interval of length M starting at or above `head`, there are exactly R accepted values, where `R = residues(M, filterValues).size`.

```scala
def assertAcceptedCountInBlock(seq: SieveSequenceV0, k: BigInt): Boolean = {
  // in [head + k*M, head + (k+1)*M), exactly R values are accepted
}
```

**Challenge**: Counting in Stainless requires structural induction over the interval, which can be heavy when intervals are large.

**Alternative (no counting):** Use an inductive approach with `indexOfAccepted`:

1. `head + M` is accepted (`searchBoundPassesFilter(1)`). Let `p = indexOfAccepted(head + M)`.
2. Prove `apply(k + p) == apply(k) + M` by induction on k:
   - Base `k=0`: `apply(p) = apply(0) + M = head + M` — by definition of `indexOfAccepted`
   - Step: Assume `apply(k + p) = apply(k) + M`. Need to show `apply(k+1 + p) = apply(k+1) + M`.
     - Both are accepted and strictly after `apply(k) + M = apply(k + p)`
     - `nextDoesNotPassAcceptedValue` implies each is the "first accepted after the previous"
     - By periodicity of `accepts(v)` under addition of M, they must be equal
3. Therefore `mod(apply(k+p), M) = mod(apply(k) + M, M) = mod(apply(k), M)`.

**Then prove `p = R`** (or accept that `p` is an alternative residue count).

**Risk**: Step 2 uses induction on k and requires the periodicity of `accepts` (which already exists via `assertExpandedCoprime`/`expandedCoprimePreservesFilter`). The inductive step needs careful chaining.

**Risk**: Proving `p = R` is itself a counting lemma. But we may not NEED to prove `p = R` — we just need SOME period, and `p = indexOfAccepted(head + M)` is a valid (computable) period.

#### Step 2: The equality chain
Once `apply(k + p) == apply(k) + M` is proved:

```scala
assert(Calc.mod(apply(k + p), filterModulus) == Calc.mod(apply(k), filterModulus))
```

This follows from `mod(a + M, M) == mod(a, M)` (periodicity of modulo).

**Risk**: Minimal — this is the easy step.

### Simplified P3 (No Counting)

Skip the counting lemma entirely. Instead:

1. Compute `p = indexOfAccepted(head + M)` — this is a concrete value for any given V0 instance.
2. Prove `apply(k + p) == apply(k) + M` by induction on k (as described above).
3. Prove `Calc.mod(apply(k + p), M) == Calc.mod(apply(k), M)`.

This gives a "loop" with period `p` without needing to prove `p = R`. The period `p` is the total number of accepted values in `[head, head + M)`.

**Tradeoff**: Weaker statement (doesn't connect `p` to the residues list size), but avoids the heavy counting proof.

## Lessons from Related Tickets Applied

| Lesson | Source | How it applies |
|--------|--------|---------------|
| **One assertion per verify cycle** | All tickets + AGENTS.md | Split P2 and P3 into multiple changes |
| **Avoid big combined lemmas** | `sieve-sequence-residue-representation-proof-object.md` | `assertAcceptsAfterAddingModulus` timed out as one lemma. Split P3 into induction base, step, and final equality. |
| **Structural invariant over opaque proof** | `sieve-properties-step5-coprime-to-modulus.md` | For P3, use structural induction over k (V0's own structure), not opaque abstractions. |
| **Use `Calc.mod` and `Calc.div`** | AGENTS.md | Never use `%` operator. |
| **Never modify MemCycle/ModCycle/CycleIntegral** | AGENTS.md | P2 and P3 stay in SieveUtils and SieveSequenceV0. No core cycle types. |
| **Direct structural recursion** | `sieve-properties-step5-coprime-to-modulus.md` | P2 uses recursion over [0, M) or over the residues list. |
| **`contains` on lists may cause VC explosion** | `sieve-properties-step5-coprime-to-modulus.md` | For P2, verify that `contains` (or `valueExistInList`) doesn't time out. |
| **Timeout is failure, not retry** | AGENTS.md stop-and-ask rule | If P2 or P3 times out 3 times, stop and ask. |

## Assumptions

- `list contains value` / `valueExistInList` can be verified without timeout for the residue list
- `assertExpandedCoprime` / `expandedCoprimePreservesFilter` is sufficient to prove the periodic preservation of `accepts(value)` under addition of M
- The induction in P3 Step 2 can be discharged without counting
- `indexOfAccepted` works for any accepted value up to `head + M` (which is a large value for large primes)

## Risks

1. **P2 `contains` VC explosion**: `contains` is recursive and may time out on large residue lists. Mitigation: pre-verify with a small test case; if timeout, use structural recursion on `generateResidues` instead.
2. **P3 induction base**: `head + M` may be large and `indexOfAccepted` walks from `head` to `head + M`, which is linear in `M`. For large M, this may time out. Mitigation: prove `apply(R) == head + M` directly using the counting argument if the `indexOfAccepted` approach times out.
3. **P3 inductive step**: Proving `apply(k+1+p) == apply(k+1) + M` from `apply(k+p) == apply(k) + M` requires periodicity and the "no skipped accepted values" lemma. If the chain is too long, the solver may timeout.

## Validation Plan

1. Run `just verify` before and after each change (green-to-green)
2. After each change: 0 invalid, 0 unknown
3. Tests: `just test` passes
4. Update verification count in the ticket after each step

## Implementation Order

1. **P2**: Add `assertGenerateResiduesComplete` + `assertResiduesComplete` to SieveUtils
2. **P3 Step 1**: Add `assertPeriodBound` — prove `apply(indexOfAccepted(head+M)) == head + M`
3. **P3 Step 2**: Add `assertBlockShift` — prove `apply(k + p) == apply(k) + M` by induction on k, where `p = indexOfAccepted(head + M)`
4. **P3 Step 3**: Add `assertApplyResidueCycles` — prove `mod(apply(k+p), M) == mod(apply(k), M)` using `modZeroPlusC` (same technique as P1)

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-19 | Ticket created documenting the plan for P2 (residues completeness) and P3 (residue periodicity). Two approaches for P3: (A) counting lemma then periodicity, (B) indexOfAccepted-based induction without counting. Approach B preferred as it avoids counting. `sieve-sequence-residue-representation-proof-object.md` timeout lesson: split everything into smallest possible pieces. | Ready for implementation. Start with P2. |
| 2026-06-19 | **P2 SUCCEEDED** — 6103 valid, 0 invalid, 0 unknown. Added three lemmas to SieveUtils: `assertGenerateResiduesContainsCoprime(v, i, modulus, primes)` (core completeness lemma), `assertResiduesComplete(modulus, primes)` (top-level), `assertResiduesCompleteRec(i, modulus, primes)` (iteration). All 171 tests pass. | P2 complete. Ready for P3. |
| 2026-06-19 | **P3 SUCCEEDED** — 6283 valid, 0 invalid, 0 unknown. Added `assertReverseCoprimePreservation` (Lemma 1 — reverse periodic direction), `assertBlockShift` (Lemma 3 — induction using `.ensuring` with explicit postcondition), and `assertApplyResidueCycles` (Lemma 4 — takes `p` as parameter, uses `AdditionAndMultiplication.APlusMultipleTimesBSameMod` for mod identity). Key lesson: private lemmas inside the same class (like `expandedCoprimePreservesFilter`) propagate their semantic content to callers better than external `.holds` lemmas. The `.ensuring` approach with explicit postconditions was essential for making inductive facts visible at call sites. 171/171 tests pass. | P3 complete. |
