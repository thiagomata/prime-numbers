# Euclid H4 — `euclidTheorem` Strategy

**Created:** 2026-06-11
**Status:** Pending
**Depends on:** `euclid-full-formalization.md` (H1-H3 done)

---

## Goal

Uncomment and verify `euclidTheorem(primes): Boolean` — prove there exists a prime not in `primes`.

Current state: H1-H3 verified (4781 valid). H4 is commented out.

---

## The Problem

`euclidTheorem` constructs `result = newPrimeFromEuclid(primes)` (or inlines it), then needs to prove `!primes.contains(result)`.

Available facts:
- `primorialPlusOneModAny(primes)` — a `.holds` lemma (postcondition: `true`)
- `findSmallestDivisorResultModZero(n, d)` — proves `mod(n, d) == 0` where `n = primorial(primes)+1`
- `findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)` — proves `Prime.noDivisorInRange(n, 2, n)`

The gap: `primorialPlusOneModAny`'s `.holds` postcondition (`result == true`) doesn't expose element-level facts. The solver can't use it to prove `mod(n, p.value) != 0` for any specific `p` in `primes`.

---

## Constraints

- Can't delete/modify `primorialPlusOneModAny` (verified, in use)
- Can't modify MemCycle, ModCycle, CycleIntegral
- All existing lemmas use `.holds` — same opacity issue

---

## Options Considered

### Option A: Just try it — uncomment and see the error

**Pro:** Concrete error tells us exactly what VC fails.
**Con:** User expects it to fail; might waste a verify cycle.

### Option B: Write `lemmaPrimorialPlusOneHead(primes)`

Proves `mod(primorial(primes)+1, primes.head.value) != 0` directly (no `.holds` dependency). Uses same modular arithmetic as `primorialPlusOneTailLoop`'s head case.

**Problem:** Only works for the head of the full list. For tail elements, `primorial(tail) != primorial(full)`, so this lemma doesn't help.

### Option C: Accumulator-based `lemmaNotContains`

Write a lemma that iterates through `primes` AND tracks the prefix product (like `primorialPlusOneTailLoop`). At each step, proves the current head's value != `result.value` using the modular arithmetic.

**Structure:**
```scala
private def lemmaNotContainsLoop(prefix: List[Prime], remaining: List[Prime], result: Prime, n: BigInt): Boolean = {
  // n = primorial(prefix ++ remaining) + 1 (invariant maintained by caller)
  require(Calc.mod(n, result.value) == BigInt(0))
  decreases(remaining.size)
  if (remaining.isEmpty) true
  else {
    // Prove: remaining.head != result
    // Use: mod(primorial(prefix ++ remaining), head.value) == 0  and modZeroPlusC  and modSmallDividend
    // Then: if head == result, result.value == head.value, so mod(n, head.value) == 0 (from require)
    // But mod(n, head.value) != 0 from the arithmetic — contradiction
    // So remaining.head != result 
    remaining.head != result && lemmaNotContainsLoop(prefix :+ remaining.head, remaining.tail, result, n)
  }
}.holds
```

**Pro:** Works for all elements, no dependency on `.holds` opacity.
**Con:** Complex accumulator logic; duplicates `primorialPlusOneTailLoop` structure.

### Option D: Inline `primorialPlusOneModAny`'s proof in `euclidTheorem`

Restructure `euclidTheorem` to do the full accumulator-based proof inline, proving `!primes.contains(result)` as part of the same structural induction that proves `mod(n, p.value) != 0`.

---

## Recommended Approach

**Start with Option A** (just try it). The error is diagnostic — it tells us which specific VC fails and hints at the solver's inlining behavior. Then implement Option C or D based on the error.

Alternatively, **go straight to Option C** since the accumulator pattern is already working in `primorialPlusOneTailLoop` and `checkPrimorialModZeroTailLoop`.

---

## Validation

1. `just verify` after uncommenting (expect failure — note the exact VC)
2. Implement the chosen fix
3. `just verify` — target: 4782+ valid, 0 unknown
