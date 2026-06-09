# assertNoDivisorByFactorList — Solver Blockers

**Created:** 2026-06-09
**Status:** Blocked
**Depends on:** `prime-foundations-and-gap-proof.md`

---

## Goal

Prove: if `isCoprime(n, primes)` and `!isCoprime(d, primes)`, then `Calc.mod(n, d) != 0`.

This is the core lemma for `assertHeadIsPrime`: every `d < head` shares a factor with `primesTail`, and since `head` is coprime to `primesTail`, no `d` can divide `head`.

---

## Attempt Log

### Attempt 1: contradiction via `assertDivTransitive`

**Code:**
```scala
val p = findPrimeFactorInList(d, primes)
assert(assertPrimeFactorDivides(d, primes))     // Calc.mod(d, p) == 0
assert(assertIsCoprimeForAll(n, primes))         // Calc.mod(n, p) != 0
assert(p > 0)

if (Calc.mod(n, d) == BigInt(0)) {
  assert(assertDivTransitive(n, d, p))           // proves Calc.mod(n, p) == 0
  false                                           // contradiction → unreachable
} else { true }
```

**Result:** `CANCELLED` on `assert(p > 0)` — solver times out proving `findPrimeFactorInList > 0`.

### Attempt 2: added `assertFindPrimeFactorPositive` lemma + `assert(p > 0)`

**Result:** `CANCELLED` on `false` (line with `false`). The solver gets through `p > 0` but times out on the contradiction. The VC path condition shows the solver can't resolve:
- `assertDivTransitive(n, d, p)` (proves `Calc.mod(n, p) == 0`)
- `assertIsCoprimeForAll(n, primes)` (proves `Calc.mod(n, p) != 0`)
- Together they should make `false` unreachable, but solver times out before seeing the contradiction

### Attempt 3: drop contradiction branch, just assert result

**Code:**
```scala
assert(assertPrimeFactorDivides(d, primes))
assert(assertIsCoprimeForAll(n, primes))
Calc.mod(n, d) != BigInt(0)
}.holds
```

**Result:** `UNKNOWN`. Solver can't infer `Calc.mod(n, d) != 0` from the two lemmas. The connection `p|d ∧ p∤n ⇒ d∤n` is not made automatically.

---

## Hypotheses: Why Solver Fails

### H1: `findPrimeFactorInList` abstraction barrier

The solver doesn't know that `p = findPrimeFactorInList(d, primes)` is IN `primes`. The `assertPrimeFactorDivides` lemma proves `Calc.mod(d, p) == 0`, and `assertIsCoprimeForAll` proves `Calc.mod(n, q) != 0` for ALL `q` in primes. But the solver can't connect that `p` is one of those `q` values.

**Evidence:** `assertIsCoprimeForAll` is proven by structural recursion over primes, establishing `Calc.mod(n, primes.head) != 0` for each element. But this knowledge is stored per-element in the recursive proof, not as a general "forall p in primes" quantifier that the solver can apply.

**Validation:** Try inlining — instead of `findPrimeFactorInList`, iterate through primes directly and for each `p` where `Calc.mod(d, p) == 0`, prove `Calc.mod(n, d) != 0`.

### H2: `assertDivTransitive` internal complexity

`assertDivTransitive` has 7 internal assertions including `assertMultipleModZero(cb * ba, a)` which requires `k >= 0`. Proving `Calc.div(n, d) * Calc.div(d, p) >= 0` may require additional arithmetic reasoning.

**Evidence:** The VC for Attempt 2 shows `CANCELLED` on the `false` branch — the solver is trying to verify `assertDivTransitive`'s internal steps in this context and timing out.

**Validation:** Inline a simplified transitivity proof: `Calc.mod(n, d) == 0 ∧ Calc.mod(d, p) == 0 ⇒ Calc.mod(n, p) == 0`, without the full `assertMultipleModZero` chain.

### H3: `assertModZeroImpliesDivTimesBEqualsA` not sufficient

The lemma `assertModZeroImpliesDivTimesBEqualsA(a, b)` proves `Calc.div(a, b) * b == a`. But without a matching `a == b * Calc.div(a, b)` version, the solver may not be able to substitute in both directions.

**Evidence:** Mathematical rewriting of `n = d * Calc.div(n, d) = p * Calc.div(d, p) * Calc.div(n, d)` requires substitution from both directions.

**Validation:** Add `a == b * Calc.div(a, b)` variant and see if it helps.

### H4: SMT solver can't handle the quantifier-like reasoning

The statement "for all p in primes, Calc.mod(n, p) != 0" looks like a quantifier to the SMT solver, which is undecidable in general. Even though Stainless encodes it via structural induction, the solver may struggle to instantiate it with the specific `p`.

**Evidence:** This is a known limitation of SMT-based verification.

**Validation:** Use a direct recursive proof that iterates through primes (see Alternative Approach below).

---

## Alternative Approach: Direct Recursive Proof

Instead of `findPrimeFactorInList`, iterate through primes directly and handle each `p`:

```scala
def assertNoDivisorByFactorListRec(
  n: BigInt, d: BigInt, primes: List[BigInt]
): Boolean = {
  require(n > 1)
  require(d >= 2)
  require(ListUtils.checkAllPositive(primes))
  require(isCoprime(n, primes))
  require(!isCoprime(d, primes))
  decreases(primes.size)

  if (primes.isEmpty) {
    true  // unreachable: isCoprime(d, List()) = true, !isCoprime(d, List()) = false
  } else {
    val p = primes.head
    if (Calc.mod(d, p) == BigInt(0)) {
      // Found p that divides d: now prove Calc.mod(n, d) != 0
      assert(Calc.mod(n, p) != BigInt(0))  // from isCoprime(n, primes)
      if (Calc.mod(n, d) == BigInt(0)) {
        // Need: Calc.mod(n, d) == 0 ∧ Calc.mod(d, p) == 0 ⇒ Calc.mod(n, p) == 0
        // This contradicts Calc.mod(n, p) != 0
        assert(/* transitivity: prove directly */ )
        false
      } else { true }
    } else {
      assertNoDivisorByFactorListRec(n, d, primes.tail)
    }
  }
}.holds
```

**Key difference:** Directly uses `primes.head` (proven `> 0` by `checkAllPositive`) and iterates explicitly, avoiding `findPrimeFactorInList` abstraction. May need a custom transitivity inline.

### If this also times out: try `@extern` on `assertDivTransitive`

If even the direct iteration fails because of transitivity reasoning, the next step is to mark `assertDivTransitive` as `@extern` to bypass its internal verification, making it an axiom. Then re-try.

---

## Next Steps

1. Try the direct recursive proof (H1 validation)
2. If still blocked, add `@extern` to `assertDivTransitive` to make it an axiom
3. If that unblocks `assertNoDivisorByFactorList`, proceed to `assertHeadIsPrime`
4. Report solver limitations for future investigation
