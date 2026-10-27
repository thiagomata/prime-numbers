# Candidate pairs versus remaining shot capacity in fixed windows

**Status:** Exact finite arithmetic check, 2026-10-26. The conditional
subtraction argument is mathematical; no general surplus or infinitude
theorem, Stainless verification or historical novelty is claimed.

## Why empty fences do not settle the question

The [fixed-window contact check](fixed-window-contact-check-2026-10-26.md)
found both nonempty and empty final fences. This refutes unconditional fence
persistence, but not a conditional certificate based on candidate population
exceeding the total remaining destruction capacity.

This experiment reuses exactly those five closed endpoint windows. Both
endpoints must remain inside the fence. Start with filters 2, 3, 5 and install
every further prime through floor(sqrt(upper endpoint)). Every tested filter
is smaller than every value in its window, so there is no self-prime deletion.

## Budget definition and proof

At a checkpoint t let V_t be all currently accepted integer values in the
fixed endpoint window [lo,hi]. Let G_t count its complete candidate pairs,
and let P_t contain the still-uninstalled primes at most sqrt(hi). Define

```math
U_t=\sum_{p\in P_t}\#\{v\in V_t:p<v,\ p\mid v\}.
```

U_t is calculated using the current accepted values, before running the
remaining filters or identifying any final twin. It deliberately counts a
value twice if two future primes divide it, and includes values that are
not endpoints of any candidate pair.

Let T_t be the total number of accepted values actually removed by those
future filters as they run. A value cannot be removed twice; its eventual
first rejection contributes one incidence already included in U_t. Therefore

```math
T_t\le U_t.
```

After filters 2 and 3, candidate 2-gaps are endpoint-disjoint. Any destroyed pair
contains a removed value, and one removed value cannot destroy two pairs.
Assign each destroyed pair its first removed endpoint. These assignments
are distinct, so

```math
\begin{aligned}
G_{\mathrm{final}}&\ge G_t-T_t\\
&\ge G_t-U_t,\\
G_{\mathrm{final}}&\ge\max(0,G_t-U_t).
\end{aligned}
```

Thus G_t>U_t certifies a surviving pair without choosing which pair it is.
Completion of the square-root filter horizon certifies any such survivor as
twin prime. This uses the established [2-Gap Isolation](../two-gap-isolation-after-filter-three.md)
and [Local Survival Threshold](../sharp-local-two-gap-survival-threshold.md)
mechanism; the static multi-filter budget here is an intentionally conservative
version of that argument.

## Initial budgets and actual outcomes

The initial checkpoint is just after filters 2, 3, 5. T counts all actual accepted
shots, including shots that destroy no still-alive candidate pair.

| Endpoint window | G0 | Initial U | Actual T | Guaranteed pairs from initial U | Actual final pairs |
|---|---:|---:|---:|---:|---:|
| [10,50] | 5 | 1 | 1 | 4 | 4 |
| [100,150] | 5 | 4 | 4 | 1 | 3 |
| [155,175] | 2 | 2 | 2 | 0 | 0 |
| [200,250] | 4 | 5 | 5 | 0 | 2 |
| [1000,1100] | 11 | 14 | 12 | 0 | 5 |

The initial static budget certifies the first two fences immediately. Failure
of that initial inequality in the last two positive fences is inconclusive,
not evidence that those fences empty.

## Certificates that appear after one filter

Recompute the same conservative budget after each installed filter. The
earliest strict certificates are:

| Endpoint window | Installed through | Candidates G_t | Remaining capacity U_t | Guaranteed final pairs |
|---|---:|---:|---:|---:|
| [10,50] | 5 | 5 | 1 | 4 |
| [100,150] | 5 | 5 | 4 | 1 |
| [155,175] | none qualifies | — | — | — |
| [200,250] | 7 | 4 | 3 | 1 |
| [1000,1100] | 7 | 9 | 8 | 1 |

This directly exhibits the proposed situation: after some filters have run,
more candidate pairs remain than all the conservatively budgeted future shots.
The computation of U_t does not consult the future pair outcome.

For [100,150], the four actual accepted shots are 119, 133 at filter 7, then
121, 143 at filter 11. The five initial pairs cannot all be destroyed by four
shots. In fact only two pairs are destroyed:121 belongs to the already
destroyed pair (119,121), and 143 destroys no initial pair. These wasted shots
explain why the bound guarantees only one of the three actual surviving pairs.

For [200,250], filter 7 removes 203 and 217, neither destroying a candidate
pair. Four candidate pairs therefore remain, while the remaining budget has
only three shots: 209 at 11, and 221, 247 at 13. At least one pair must survive.

In [155,175], there is no spare capacity: the two actual shots 161 and 169
destroy its two pairs. Nothing in the sufficient inequality predicts survival.

## Exact reproduction

Run this stdlib-only snippet with python3 -B. It writes no files. The final
primality oracle and future actual-shot totals are validation controls, not
inputs to the earlier certificates.

```python
from math import gcd, isqrt

windows = [(10, 50), (100, 150), (155, 175), (200, 250), (1000, 1100)]

def prime(n):
    return n >= 2 and all((n // d) * d != n
                         for d in range(2, isqrt(n) + 1))

for lo, hi in windows:
    future = [p for p in range(7, isqrt(hi) + 1) if prime(p)]
    values = {n for n in range(lo, hi + 1) if gcd(n, 30) == 1}

    def pairs(v):
        return {a for a in range(lo, hi - 1) if a in v and a + 2 in v}

    def budget(v, primes):
        return sum(sum(p < n and (n // p) * p == n for n in v)
                   for p in primes)

    initial = len(pairs(values))
    u0 = budget(values, future)
    cert = (5, initial, u0) if initial > u0 else None
    total = 0
    rows, records = [], []
    for i, p in enumerate(future):
        shots = {n for n in values if p < n and (n // p) * p == n}
        before = pairs(values)
        values -= shots
        after = pairs(values)
        assert len(before - after) <= len(shots)
        total += len(shots)
        remaining = budget(values, future[i + 1:])
        records.append((len(after), remaining, total))
        if cert is None and len(after) > remaining:
            cert = (p, len(after), remaining)
        rows.append((p, sorted(shots), len(after), remaining))
    final = pairs(values)
    oracle = {a for a in range(lo, hi - 1) if prime(a) and prime(a + 2)}
    assert final == oracle
    assert u0 >= total
    assert len(final) >= max(0, initial - u0)
    assert len(final) >= max(0, initial - total)
    for population, remaining, used in records:
        assert remaining >= total - used
        assert len(final) >= max(0, population - remaining)
    print("WINDOW", lo, hi, "G0", initial, "U", u0, "T", total,
          "FINAL", len(final), "EARLIEST_CERT", cert)
    print("FILTER_ROWS", rows)
print("ALL_CAPACITY_AND_PRIMALITY_CHECKS_PASS")
```

## What this establishes and what remains open

The user's surplus proposal succeeds in these finite examples, even though
unconditional fence persistence is false. Candidate identification plus an
independent upper bound on future accepted shots can force a survivor without
following every possible candidate history.

The experiment does not prove that this inequality occurs infinitely often
or eventually in every relevant range. Bounding U_t sharply and proving a
sufficient actual local G_t are still necessary for such a theorem. No global
complete-period count is substituted for a local population, and no numerical
fence is asserted to lie beyond a hypothetical last pair.

These are fixed proper-divisor contacts. Passing a pair in the advancing head
stream is different from destroying it by a divisor. Integer zero-set results
do not imply stabilization of the full continuous curve between integers.
