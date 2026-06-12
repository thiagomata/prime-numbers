# Sieve Foundation: CycleIntegral and Filter Properties

## Overview

This article documents the foundational lemmas that establish the correctness of the sieve sequence algorithm. The key insight is that we can decompose the complex sieve algorithm into simpler, verifiable components.

## Core Properties

### 1. CycleIntegral with Unit Cycle

**Property:** A cycle integral with cycle `[1]` produces natural numbers sequentially.

**Formal Statement:**
```
CI(init, MemCycle([1])).apply(pos) = init + pos + 1
```

**Intuition:** Each step adds exactly 1, so we get consecutive integers starting from `init + 1`.

**Why This Matters:** The sieve uses `nextCandidates` to generate all natural numbers from 2 onward. This lemma proves that the cycle integral mechanism correctly implements this counter.

---

### 2. Strict Monotonicity of Unit Cycle

**Property:** The unit cycle is strictly increasing.

**Formal Statement:**
```
b > a ⟹ CI(init, MemCycle([1])).apply(b) > CI(init, MemCycle([1])).apply(a)
```

**Intuition:** If you start later, you end up with a larger number.

**Why This Matters:** This ensures that larger candidate numbers come after smaller ones, which is essential for the sieving process.

---

### 3. Distinct Primes Are Coprime

**Property:** If q and p are distinct primes, then p does not divide q.

**Formal Statement:**
```
isPrime(q) ∧ isPrime(p) ∧ q ≠ p ⟹ mod(q, p) ≠ 0
```

**Intuition:** Two different primes share no common factors other than 1.

**Key Insight:** This required a helper lemma because Stainless's SMT solver couldn't automatically connect the abstract `noDivisorInRange` property to concrete prime relationships.

**Helper Lemma:**
```
∀ p, q ∈ [2, n). isPrime(q) ∧ p ≠ q ⟹ mod(q, p) ≠ 0
```

This helper is proved by induction on `n`, establishing the property for all pairs up to `n`.

---

### 4. Filtering by One Prime Preserves Other Primes

**Property:** When filtering a list by a prime p, any prime q ≠ p is preserved.

**Formal Statement:**
```
isPrime(q) ∧ q ≠ filterPrime ⟹ mod(q, filterPrime) ≠ 0
```

**Intuition:** Primes don't divide each other unless they're equal.

**Why This Matters:** This is the core of the sieve: we remove multiples of small primes but keep all primes themselves.

---

### 5. Filtered List Contains All Primes

**Property:** If a prime q is in the original list and q ≠ filterPrime, then q is in the filtered list.

**Formal Statement:**
```
q ∈ originalPrimes ∧ isPrime(q) ∧ q ≠ filterPrime ⟹ q ∈ filteredPrimes
```

**Intuition:** The filter only removes non-primes and multiples of the filter prime. All other primes survive.

**Why This Matters:** This proves the sieve is sound: we never lose primes we need to keep.

---

## Proof Architecture

### Decomposition Strategy

The key insight is that a complex algorithm can be verified by:

1. **Decompose** the algorithm into atomic steps
2. **Verify** each step independently
3. **Compose** the results

For the sieve:
```
nextResidues → nextExpanded → nextFiltered → nextSorted →
nextGaps → nextHeadResidueIndex → nextRotatedGaps
```

Each step calls ONE `SieveUtils` helper + ONE pre-verified function.

### Handling SMT Limitations

When the solver can't prove something automatically, we:

1. **Identify the gap:** What can't the solver connect?
2. **Create a helper lemma:** Bridge the gap with an explicit induction
3. **Use the helper:** Reference it from the main lemma

Example: The solver couldn't connect `noDivisorInRange(q, 2, q)` (abstract) to `mod(q, p) ≠ 0` (concrete). The helper lemma `noDivisorInRangeImpliesModNonZero` makes this connection explicit.

---

## Integration with SieveSequence

These lemmas are currently **abstract** — they don't reference `SieveSequenceV2` directly. Instead:

1. `SieveSequenceV2` is verified separately using `@extern` for complex operations
2. These lemmas provide the mathematical foundation
3. A final proof would connect them

This separation keeps the codebase modular and maintainable.

---

## Files

| File | Purpose |
|------|---------|
| `CycleIntegralOnesProperties.scala` | Lemmas 1 & 2 |
| `FilterPreservesPrimesProperties.scala` | Lemmas 3, 4, & 5 |
| `sieve-foundation-cycle-integral-ones-and-filter-preserves-primes.md` | Ticket documenting progress |

---

## Next Steps

1. ✅ Prove CycleIntegral with unit cycle produces natural numbers
2. ✅ Prove strict monotonicity of unit cycle
3. ✅ Prove distinct primes are coprime
4. ✅ Prove filtering preserves primes
5. 🔄 Connect to `SieveSequenceV2` verification
6. 🔄 Extend to handle edge cases (e.g., empty lists, single elements)

---

## References

- [Integral Cycle Properties](integral-cycle.md) - Detailed explanation of the integral cycle mechanism
- [Modular Arithmetic](modular-arithmetic.md) - Foundation for prime divisibility proofs
- [Stainless Documentation](https://stainless.epfl.ch/) - Formal verification framework