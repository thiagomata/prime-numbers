# Use SpecSieveSequence to Build the Next-Level Sequence

**Created:** 2026-06-18
**Updated:** 2026-06-19
**Status:** Complete — `SpecSieveSequence.next` verified at 5992 valid.

**Related tickets:**
- `prove-apply1-is-prime.md` — failed attempt to prove `apply(1)` is prime directly (rendered obsolete by `nextPrime` which doesn't need it)
- `check-project-guidance-docs-2026-06-17.md` — primary V0 implementation
- `next-constructor-requirement-assertions.md` — V2 next-level helpers
- `walk-based-pipeline.md` — V2 walk-based gap collection

---

## Goal

Given `SpecSieveSequence(primes)` where `primes = [p_n, p_{n-1}, ..., 2]`, produce `SpecSieveSequence(newPrimes)` where `newPrimes = [p_{n+1}, p_n, ..., 2]`.

---

## Result

The full chain is verified and live:

```
AllPrimesSoFarList.nextPrime → AllPrimesSoFarList.next → SpecSieveSequence.next
```

| Component | Verified at | What it does |
|-----------|-------------|-------------|
| `searchNextPrimeUpTo` | 5843 | Bounded linear scan; postcondition proves `isPrime(res)`, `res.value >= current`, `noPrimesBetween(current, res.value)` |
| `newPrimeNotInList` | 5848 | Euclid prime is not in the input list |
| `notContainsFromValueNotMatchesAny` | 5876 | Bridge: `valueNotMatchesAny` ⇒ `!contains` on `SortedPrimeList` |
| `euclidPrimeGreaterThanHead` | 5876 | Euclid prime > head (by contradiction with `primeAtOrBelowHeadIsContained`) |
| `AllPrimesSoFarList.nextPrime` | 5898 | Postcondition: `res.value > head.value`, `isPrime(res.value)`, `noPrimesBetween(head+1, res.value)` |
| `primeIsCoprimeWithSmallerList` | 5974 | `isPrime(v)` + descending `primes` with `head < v` ⇒ `isCoprime(v, primeValues(primes))` |
| `noDivisorInRangeExcludesValue` | 5917 | Extracts `mod(n, value) != 0` from `noDivisorInRange(n, from, to)` for any value in range |
| `AllPrimesSoFarList.next` | 5980 | Constructs `SortedPrimeList(newPrime :: list.list)` + `AllPrimesSoFarList(…)` using nextPrime's postcondition |
| `SpecSieveSequence.next` | 5992 | Delegates to `AllPrimesSoFarList.next`, proves `isCoprime` via `primeIsCoprimeWithSmallerList` |

### Three constructor proofs resolved

| Proof | Required | How |
|-------|----------|-----|
| `SortedPrimeList.isDescending(newPrime :: list.list)` | `newPrime.value > head.value` | `nextPrime` postcondition assures this |
| `AllPrimesSoFarList.allPrimesSoFar(newSortedList)` | `isPrime(newPrime.value)` + `noPrimesBetween(head+1, newPrime.value)` | `nextPrime` postcondition assures both |
| `SpecSieveSequence(…)` constructor `isCoprime` | `isCoprime(newPrime.value, oldFilterValues)` | `primeIsCoprimeWithSmallerList` + `SortedPrimeList.assertTailDescending` |

---

## Stainless Lessons (learned while building this)

1. **`.ensuring` on class methods breaks type inference**: A class method returning `Prime` with `.ensuring(res => res.value > ...)` gets inferred as `BigInt` at call sites. **Fix**: move the method to the companion object.
2. **`primes.next()` vs `primes.next`**: Stainless confuses `primes.next()` with `primes.next.apply()` when the class also defines `apply(index: BigInt)`. **Fix**: omit parentheses for parameterless methods.
3. **`List[Prime]` vs `List[BigInt]`**: Bridging lemmas between `Prime.isPrime` and `SieveUtils.isCoprime` must use `List[Prime]` to carry the `value > 1` invariant — `List[BigInt]` requires extra `checkAllBiggerThanOne` preconditions.
4. **`!contains` bridge needs `valueNotMatchesAny` access**: Connecting `euclidTheorem`'s non-membership result to `AllPrimesSoFarList.contains` requires structural induction inside `PrimeProperties` (where `valueNotMatchesAny` is accessible). Making `valueNotMatchesAny` public would enable a cleaner bridge from outside.
5. **`noDivisorInRangeExcludesValue`**: A dedicated lemma that extracts a specific point-fact from a range predicate is the cleanest pattern for bridging range checks to element-level checks.
6. **Proof by contradiction without `assert(false)`**: Writing `if (d <= head.value) { lemmaThatProvesContains(d, list) }` is enough — Stainless sees `contains && !contains` = false and marks the branch unreachable.

---

## What was NOT needed

- The "prime in (p, p²)" deep number theory result — `searchNextPrimeUpTo`'s bounded scan proves `noPrimesBetween(head+1, res)` without it.
- `mod(product(tail), newPrime) != 0` — the V0 constructor doesn't check this. (V2's cycle-based construction may need it separately.)
- `Prime(newPrimeValue)` wrapper call — the whole chain works with `Prime` objects directly; no raw value needs wrapping at the call site.
