# Distinguished Head Spacer

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Empirical status:** REINFORCED — `d_head <= q^2-q-3` in 186/186 window-pass transitions; the bound is quadratic so this holds trivially at large p. See "Empirical status" section.

## Candidate Hypothesis

Let `S_q` be the bi-infinite periodic set of post-filter 2-gap starts. Define
the forward distance from the head to the next start by

```math
d_{head}(q)=\min\{s-q:s\in S_q,\ s\ge q\}.
```

Suppose, for infinitely many heads `q`,

```math
d_{head}(q)\le q^2-q-3.
```

## Why It Is Sufficient

Let `s=q+d_head(q)`. The candidate bound gives

```math
q\le s\le q^2-3,
```

so `s+2<q^2`. Since `s` is a post-filter 2-gap start, both endpoints avoid
all primes below `q`; the square bound makes both endpoints prime.

This condition is weaker than bounding every cyclic spacer. It controls only
the empty region immediately in front of the distinguished head.

## Established Inputs

- [Rotation and the local boundary](../properties/sieve-sequence/rotation-preserves-cyclic-gap-counts.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

The inequality is close to the desired local-placement theorem. Its value as a
candidate is that it isolates the single relevant spacer, but global counts and
rotation invariance currently provide no bound on its phase relative to `q`.

## Empirical status (window scale, p to ~19000)

Source: `python/src/sieve_sequence/window_cli.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantity: `d_head` = forward distance from head
`q` to the first post-filter 2-gap start `s >= q`. The candidate's concrete
sufficient condition is `d_head <= q^2 - q - 3`.

The condition holds in **186/186** transitions: `d_head <= q^2-q-3` always, by
a enormous margin at large p.

| range | d_head min | median | max | bound `q^2-q-3` (min) |
|-------|-----------|--------|-----|------------------------|
| dense (p 5..991) | 0 | 16 | 148 | 22 (at q=7) |
| sparse (p ~1000..19000) | 0 | ~50 | ~600 | ~10^6 (at q~1000) |

Trend (log-log, n=152): `d_head ~ p^(+0.31)`, r = +0.44 — a weak/noisy
finite-range fit. Through the measured range, `d_head` remains far below the
quadratic bound. The fit does not prove subquadratic asymptotic growth.

### No counterexample

Zero failures.

### What this does and does not establish

- **Does:** show that at window scale to p~19000 the first post-filter 2-gap
  start lies comfortably within the safe window in all 186 measured cases.
- **Does not:** make the condition discriminating over this sample—the observed
  distances are much smaller than the available quadratic bound. The
  candidate's value is conceptual (isolating the head spacer), not empirically
  distinctive. The finite run proves neither subquadratic growth nor recurrence
  at infinitely many stages.

## Strategic assessment after empirical review

This is the correct localization of the problem, but its post-filter
inequality is almost equivalent to asking whether the desired safe-window
2-gap exists. The `d_head` measurement therefore records the outcome after the
filter rather than identifying why future filters cannot keep selecting the
head neighborhood.

Use #8 as a boundary condition for stronger mechanisms, not as the first proof
target. A useful theorem would control how the distinguished spacer changes
from the current sequence through several future filters; that hereditary
relationship would address the head-cherry-picking concern directly.
