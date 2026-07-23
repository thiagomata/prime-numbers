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
p<=991 + sparse to p~19000). The run recorded `main_term = |W| delta_q`, but
computed the reported discrepancy as

```math
E_{\mathrm{measured}}=G_{\mathrm{local}}-|W|\delta_q,
```

where `G_local` is the **pre-filter** 2-gap count. The hypothesis instead
defines

```math
E_q=|S_q\cap W_q|-|W|\delta_q
```

from the **post-filter** count. These are different quantities. Consequently,
the earlier “pass 186/186” label and its discrepancy ratios do not test this
candidate and are withdrawn. The recorded column may remain a pre-filter
window diagnostic, but it cannot be interpreted as `E_q`.

### What must be measured

Recompute `E_q` as `surviving - main_term` and report both the two-sided ratio
`|E_q|/main_term` and the one-sided margin. The one-sided inequality
`E_q>-main_term` is algebraically equivalent to `surviving>0`, so measuring it
only reproduces the outcome. The informative empirical stress test is the
stronger two-sided discrepancy bound and its scaling.

## Strategic assessment after empirical review

The candidate is analytically natural, but its weak one-sided form is a
restatement of local survival. Its value lies in proving a genuinely
non-circular two-sided or relative discrepancy estimate from the arithmetic of
the filters. Until the post-filter discrepancy is computed, this candidate is
**unmeasured as stated** and should not be ranked from the current column.
