# Reciprocal-Decay Specialization

**Status:** Conditional mathematical consequence of the
[Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md).
Not a claim about the real modular filter.

## Meaning

If the adversarial share decays like `c/r`, the cumulative adversarial
budget only grows like `log log Q` -- far too slowly to threaten the
quadratic square-window supply. Every fixed `c>0` therefore leaves the
window eventually and permanently nonempty under the spatial-uniformity
premise, for every finite decay rate.

## Setup

Suppose `alpha_r ~ c/r` for fixed `c>0` and sufficiently large primes `r`,
in the position-blind adversarial/random mixture of
[Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md).

## Property

```math
\begin{aligned}
A(Q)
&\sim c\sum_{r < Q}\frac1r
&&[-\log(1-x)\sim x]\\
&\sim c\log\log Q.
&&[\text{Prime Harmonic Sum}]
\end{aligned}
```

Therefore

```math
e^{-A(Q)}\asymp\frac1{(\log Q)^c}
```

and, substituting into the mixed expected occupancy,

```math
\lambda_Q^{\mathrm{mix}}
\asymp
C\frac{Q^2}{(\log Q)^{2+c}}\longrightarrow\infty.
\qquad[\text{Q.E.D.}]
```

The window population grows polynomially in `Q` despite the extra
`(\log Q)^{-c}` loss, so the empty-window probabilities are summable and,
by the first Borel-Cantelli lemma, every sufficiently large square window is
nonempty almost surely under the spatial model -- for every fixed `c>0`, not
just small ones.

## What This Does And Does Not Say

Reciprocal decay is the gentlest of the two decaying-share families studied
here; [Log-Over-Linear Decay Specialization](
log-over-linear-decay-specialization.md) shows a schedule that decays only
slightly faster (`c\log r/r`) does have a finite critical threshold
(`c=2`), unlike this family. The safe-window conclusion is not claimed for
the real sieve.

## Related

- [Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md)
- [Log-Over-Linear Decay Specialization](log-over-linear-decay-specialization.md)
- [Constant-Share Trivial Fatality](constant-share-trivial-fatality.md) --
  the `alpha_r` non-decaying case.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §4.3](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
