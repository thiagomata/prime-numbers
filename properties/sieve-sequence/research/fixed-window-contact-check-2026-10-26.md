# A few fixed-window zero-contact checks

**Status:** Exact finite arithmetic check, performed 2026-10-26. No universal
trapping property, asymptotic claim or Stainless verification is asserted.

## What is measured

In the [continuous-contact construction](../../../candidates/continuous-contact-research-directions.md),
an integer start n has zero pair height exactly when both n and n+2 avoid
the installed proper-divisor filters. Each such pair is a 2-cell in the
corresponding focused sequence at that stage.

Choose the five fixed closed endpoint windows below before running the check.
Both endpoints must lie inside the window: lo<=n and n+2<=hi. Begin with
prime filters2,3,5, then install every further prime through floor(sqrt(hi)).
The checked zero sets are nested subsets of each window's initial contacts.

This uses the prime-filter variant. Its positive integer heights count
distinct proper prime factors and are not the same as the all-integer
construction's proper-divisor heights. Their zero sets agree at these final
certification stages. No floating-point near-zero threshold or sampled area
is used as evidence of an integer contact.

## Results

| Endpoint window | Initial contacts after 2,3,5 | Final certified pairs | First empty at filter |
|---|---:|---:|---|
| [10,50] | 5 | 4 | never in this check |
| [100,150] | 5 | 3 | never in this check |
| [155,175] | 2 | 0 | 13 |
| [200,250] | 4 | 2 | never in this check |
| [1000,1100] | 11 | 5 | never in this check |

The final sets are:

- [10,50]: (11,13),(17,19),(29,31),(41,43).
- [100,150]: (101,103),(107,109),(137,139).
- [155,175]: empty.
- [200,250]: (227,229),(239,241).
- [1000,1100]: (1019,1021),(1031,1033),(1049,1051),(1061,1063),(1091,1093).

All final sets match independent trial-primality tests on both endpoints.
Filtering through sqrt(hi) is sufficient: every composite endpoint at most hi
has a prime factor at most sqrt(hi). Each listed prime endpoint remains
protected against its own filter by activation in the full function.

## A fence that empties

For [155,175] the exact history is

| Installed prime filters | Remaining contacts |
|---|---|
| 2,3,5 | (161,163),(167,169) |
| 2,3,5,7 | (167,169) |
| 2,3,5,7,11 | (167,169) |
| 2,3,5,7,11,13 | none |

The causes are 161=7*23 and 169=13^2. The two candidate contacts rise off
the real axis at different filters. This agrees with the earlier
[reverse-history audit](reverse-rejection-history-audit.md). It is a genuine
negative example to unconditional fixed-fence persistence.

## Exact reproduction

Run the following with python3 -B; it writes no files and uses only stdlib.
The contact predicate checks installed proper divisors. The independent
oracle tests all possible integer divisors through each endpoint's square
root, not merely the listed prime filters.

```python
from math import isqrt

windows = [(10, 50), (100, 150), (155, 175), (200, 250), (1000, 1100)]

def prime(n):
    return n >= 2 and all((n // d) * d != n
                         for d in range(2, isqrt(n) + 1))

primes = [p for p in range(2, isqrt(max(hi for lo, hi in windows)) + 1)
          if prime(p)]

def zero_height(n, installed):
    return all(not (p < n and (n // p) * p == n) for p in installed)

for lo, hi in windows:
    installed = [2, 3, 5]
    alive = {a for a in range(lo, hi - 1)
             if zero_height(a, installed) and zero_height(a + 2, installed)}
    initial = len(alive)
    print("WINDOW", lo, hi, "INITIAL", initial, sorted(alive))
    first_empty = None
    for p in primes:
        if p <= 5 or p > isqrt(hi):
            continue
        installed.append(p)
        new = {a for a in range(lo, hi - 1)
               if zero_height(a, installed) and zero_height(a + 2, installed)}
        assert new <= alive
        killed = sorted(alive - new)
        alive = new
        if not alive and first_empty is None:
            first_empty = p
        print("FILTER", p, "REMAINING", len(alive), "KILLED", killed)
    oracle = {a for a in range(lo, hi - 1) if prime(a) and prime(a + 2)}
    assert alive == oracle
    print("FINAL", [(a, a + 2) for a in sorted(alive)],
          "FIRST_EMPTY", first_empty, "LIMIT", isqrt(hi), "ORACLE_PASS")
```

## Meaning and limitation

Persistent contacts in the four successful fences are actual twin pairs.
The empty fence demonstrates that having candidate contacts initially does
not guarantee that any remain. These five ordinary numerical windows cannot
be treated as windows beyond a hypothetical last twin pair.

The measurement concerns fixed activated arithmetic contacts. An actual
sieve stream eventually passes a genuine prime pair; that removal from its
forward tail is not proper-divisor rejection and does not destroy the
completed continuous function's contact there.

The entire continuous curve may still change between integer inputs after
its contact set is certified. This diagnostic validates integer zeros only.
It illustrates both outcomes of the trapping proposal; it does not establish
the missing hypothesis that a suitable fence must stay nonempty arbitrarily
far out.
