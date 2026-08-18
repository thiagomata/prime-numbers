# Log-Over-Linear Decay Specialization

**Status:** Conditional mathematical consequence of the
[Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md).
Not a claim about the real modular filter.

## Meaning

If the adversarial share decays like `c\log r/r`, the cumulative
adversarial budget grows like `c\log Q` -- the same order as the quadratic
window's own logarithmic corrections -- producing a genuine finite critical
threshold `c=2` for the square window, unlike the reciprocal-decay family.

## Setup

Suppose `alpha_r ~ c\log r/r` for fixed `c>0`, in the position-blind
adversarial/random mixture of
[Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md).
(For a finite initial prefix the shares must be defined separately so they
remain in `[0,1]`; this changes only the final constant, not the asymptotic
tail below.)

## Property

```math
\begin{aligned}
A(Q)
&\sim c\sum_{r < Q}\frac{\log r}{r}
&&[-\log(1-x)\sim x]\\
&\sim c\log Q.
&&[\text{Prime Number Theorem By Partial Summation}]
\end{aligned}
```

Consequently,

```math
\begin{aligned}
e^{-A(Q)}&\asymp Q^{-c},\\
\lambda_Q^{\mathrm{mix}}
&\asymp C\frac{Q^{2-c}}{(\log Q)^2}.
\end{aligned}
```

The square-window phase diagram is therefore

```math
\begin{aligned}
c < 2&\Longrightarrow\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,\\
c\ge 2&\Longrightarrow\lambda_Q^{\mathrm{mix}}\longrightarrow0.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

For `c<2` the divergence is polynomial, so the empty-window bound is
summable and every sufficiently large square window is nonempty almost
surely under the spatial-uniformity premise.

## What This Does And Does Not Say

This is the same schedule family whose head-recurrence behavior is studied
in [Bad/Random Head Boundary](bad-random-head-boundary.md), where the
critical threshold is `c=1`, strictly below this file's `c=2` -- there is an
intermediate regime `1\le c<2` in which square-safe windows remain populated
almost surely while head recurrence fails almost surely. Compare
[Reciprocal-Decay Specialization](reciprocal-decay-specialization.md), which
has no finite critical threshold at all. The safe-window conclusion is not
claimed for the real sieve.

## Related

- [Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md)
- [Reciprocal-Decay Specialization](reciprocal-decay-specialization.md)
- [Bad/Random Head Boundary](bad-random-head-boundary.md)
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §4.3](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
