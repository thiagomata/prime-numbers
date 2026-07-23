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
