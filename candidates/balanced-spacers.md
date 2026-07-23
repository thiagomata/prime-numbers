# Balanced Spacers

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Candidate Hypothesis

Let `S_q` be nonempty after filtering, let `M_q` be its period modulus, and let

```math
G_q=|S_q\bmod M_q|>0,
\qquad
\overline D_q=\frac{M_q}{G_q}.
```

Suppose the maximum post-filter spacer satisfies

```math
D_{max}(q)\le C(q)\overline D_q
```

and, for infinitely many `q`,

```math
C(q)\frac{M_q}{G_q}<q^2-q-2.
```

## Why It Is Sufficient

The two inequalities give `D_max(q)<q^2-q-2`. The bounded post-merge spacer
argument then places a surviving 2-gap start in the square-safe interval.

As an additional classical analytic input, Mertens-type product estimates give
the average 2-gap-start spacer a scale comparable to `log(q)^2`; this
asymptotic is not established by the project notes linked below. With that
additional input, any proved imbalance factor satisfying

```math
C(q)=o\!\left(\frac{q^2}{\log(q)^2}\right)
```

would be sufficient asymptotically.

## Established Inputs

- [Exact global 2-gap count](../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Complete-period versus local boundary](../properties/sieve-sequence/batched-short-window-discrepancy-boundary.md)

## Limitation

An average does not bound an extreme spacer. The head may lie in a rare large
empty arc even while almost all other spacers are small. The balance factor is
the unproved content.

## Empirical status: not measured this pass

This candidate bounds an imbalance factor `C(q)` relating the maximum spacer to
the average spacer over the full period modulus `M_q` — whole-period data.
The window-scale stress-test sieves only `[q,q^2)` and cannot measure either
`D_max(q)` or the period average `\overline D_q = M_q/G_q`. Deferred to a
deeper (whole-period) pass. Note the candidate's existential form ("there
exists `C(q)`") means it could not be *confirmed* by measurement in any case —
only falsified by showing the factor grows without bound.

## Strategic assessment after empirical review

The average-to-maximum step is the whole difficulty here. Exact global counts
can make the average spacer small while allowing a rare empty arc to contain
the distinguished head. Consequently, the universal balance factor is a much
stronger target than the square-safe conclusion requires.

Proof priority is low in this form. Small complete-period measurements can
estimate the extreme-to-average ratio and reject implausible proposed bounds,
but a head-conditioned quantile bound or a mesoscopic local balance theorem
would be more relevant than controlling the maximum over every phase.
