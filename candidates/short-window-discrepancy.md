# Short-Window Discrepancy

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Empirical status:** INCONCLUSIVE — post-filter `E_q` now computed (lineage, one-sided holds 24/24), but the load-bearing two-sided bound `|E_q| < main_term` is still pending. See "Empirical status (post-filter E_q, lineage experiment)".

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

## Relation To The Collision-Energy Program

This candidate's discrepancy `E_q` compares the final post-filter safe-window
2-gap count with a complete-period density main term. It does not directly
control the accepted-anchor strike-density error

```math
\varepsilon
=
\frac HN-\frac1p
```

that appears in the exact harmful-excess identity

```math
b=H\beta+2L\varepsilon.
```

Therefore candidate #10 is not presently one of the scalar inputs to the
#13/#22/#21 orthogonal energy chain. Candidate #23 is the separate
accepted-strike-density theorem required there. Any future reduction from
`E_q` to `epsilon` must be
proved explicitly rather than inferred from their similar discrepancy
language.

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

## Empirical status (post-filter `E_q`, lineage experiment)

The post-filter discrepancy `E_q = surviving - main_term` (using the
POST-filter count, correcting the window pass's pre/post error) is now
computed per layer by the lineage experiment
(`candidates/analysis/run_lineage.py`).

**Q=101, 24 layers:** `E_q` ranges over `[+8.60, +1489.60]` — positive at
every layer (the post-filter surviving count exceeds the complete-period main
term). The one-sided sufficient condition `E_q > -main_term` therefore holds
trivially at all 24 layers (as the note's review observed, this is
algebraically equivalent to `surviving > 0`).

The two-sided bound `|E_q| < main_term` — the genuinely informative form that
the review identified as the real test — is **not yet evaluated** end-to-end
at scale: the lineage records `E_q` and `main_term` but does not currently
emit the two-sided ratio. That is a small extension to the runner; flagged
here as the next measurement for this candidate. Honest scope: one window,
one chain; the one-sided form holds everywhere but is a restatement of
survival, and the load-bearing two-sided form is still pending.
