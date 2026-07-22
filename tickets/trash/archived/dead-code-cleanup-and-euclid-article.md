# `.holds` Caching — The Key to the Euclid Proof

**Created:** 2026-06-12
**Updated:** 2026-06-12
**Status:** Completed
**Depends on:** `euclid-h4-strategy.md` (completed), `euclid-full-formalization.md` (completed)

---

## Discovery: `.holds` Caches Assertions for Callers

The fundamental mechanism that makes the Euclid theorem proof work is **how assertions
inside `.holds` lemmas are cached and become available to callers**.

### The Pattern

In `euclidTailLoop`, an assertion verifies a modular fact:
```scala
assert(Calc.mod(n, p) != BigInt(0))  // verified and cached
```

When `euclidTheorem` calls:
```scala
assert(euclidTailLoop(primes, d, n, BigInt(1)))
```

The cached assertion that `Calc.mod(n, p) != 0` for each `p` in `primes` is
available — which is exactly what's needed to prove `p != d` (since the caller
already knows `Calc.mod(n, d) == 0` from `findSmallestDivisorResultModZero`).

### Why This Matters

- **No need to enrich `ensuring` postconditions** to expose every internal fact
- **Simple `assert` statements** within `.holds` lemmas are sufficient
- **The solver uses cached assertions across function call boundaries**
- **This pattern is reusable** for any proof that needs to expose internal lemmas

The `.ensuring` clause (`res => res && valueNotMatchesAny(primes, v)`) packages
results for the caller, but the **cached asserts** inside the loop body are what
the solver actually uses to discharge inequalities at each recursive step.

### Confirmation

The proof succeeds: 4749/4749 VCs valid. The `euclidTailLoop` approach works
because it returns the raw conjunction (it is NOT a `.holds` lemma), so the
solver inlines it and gets all the `p != v` facts. Meanwhile, `primorialPlusOneModAny`
IS a `.holds` lemma whose cached assertions feed into `euclidTheorem`.

### Relationship to Article

This insight is documented in `articles/euclid-theorem.md` §4 (The `.holds` Caching Insight).
