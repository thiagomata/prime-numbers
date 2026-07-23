# Short-Window Discrepancy

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Candidate Hypothesis

Let the exact complete-period density of post-filter 2-gap starts be

```math
\delta_q=
\frac12
\prod_{\substack{3\le r<q\\r\text{ prime}}}
\left(1-\frac2r\right).
```

Write the exact safe-window count as

```math
|S_q\cap W_q|=|W_q|\delta_q+E_q.
```

Suppose, for infinitely many `q`, the discrepancy satisfies

```math
|E_q|<|W_q|\delta_q.
```

The weaker one-sided condition `E_q>-|W_q|delta_q` is already sufficient.

## Why It Is Sufficient

The candidate inequality gives

```math
|S_q\cap W_q|
\ge |W_q|\delta_q-|E_q|>0.
```

The positive integer count yields a square-safe 2-gap and therefore a
twin-prime certificate.

## Established Inputs

- [Exact global 2-gap count](../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Batched short-window discrepancy boundary](../properties/sieve-sequence/batched-short-window-discrepancy-boundary.md)

## Limitation

The complete-period CRT formula determines the main term but supplies no such
short-window error bound. Proving the candidate requires distributional input
beyond total counts and per-prime residue frequencies.

## Empirical status (window scale, p to ~19000)

Source: `candidates/analysis/measure_candidates.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantities: `main_term = |W| * delta_q` (the
complete-period-density expected count) and `E_q = G_local - main_term` (the
short-window discrepancy, using the *pre-filter* 2-gap count as the observed
count; see `candidates/analysis/README.md` for this convention). The candidate's
one-sided sufficient condition is `E_q > -main_term`.

The condition holds in **186/186** transitions: the discrepancy never comes
close to cancelling the main term.

| quantity | min | median | max |
|----------|-----|--------|-----|
| `main_term` | 4.2 | 2,705 | 1.61e6 |
| `E_q` | -1.79e5 | -96.5 | 12.5 |

Note `E_q` is usually slightly negative (the pre-filter window count is a bit
below the complete-period prediction) but its magnitude is far smaller than
`main_term`. The ratio `|E_q| / main_term` has max ~0.35 in the dense range and
shrinks at large p. **No meaningful trend exponent for `E_q` itself** — it is a
difference of two large numbers, so a log-log fit is numerically meaningless;
the load-bearing fact is the one-sided bound, which holds in every transition.

### No counterexample

Zero failures of `E_q > -main_term`.

### What this does and does not establish

- **Does:** show that at window scale to p~19000 the short-window discrepancy
  never overwhelms the main term — the complete-period density is a reliable
  guide to the window count, within a factor that stays well under the survival
  threshold. A proof using #10 may assume `E_q > -main_term` at this scale
  without contradicting data.
- **Does not:** prove the discrepancy bound for all p, nor discharge the actual
  analytic obligation (a non-circular short-window error estimate). Note the
  convention caveat: observed count here is pre-filter; the candidate statement
  is about post-filter. Window-scale only; does not touch infinitude.
