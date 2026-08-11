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
