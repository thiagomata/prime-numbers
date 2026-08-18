# Growing Square Windows Under Adversarial/Protective Parent Mixing

**Status:** Mathematically proved conditional on a quadratic eligible-supply
premise (`B(Q) \asymp C_0 Q^2`) for the balanced good (protective parent)
companion, mixed with the balanced adversarial companion under
position-blind, independent parent-label assignment. Not a claim about the
real modular filter.

## Meaning

The protective policy removes the balanced-random companion's density
penalty by preserving every eligible target child; the only local loss left
is the cumulative adversarial-label probability. This does not move the
square-window phase boundary (the quadratic window still dominates
logarithmic factors away from the boundary), but it does change the exact
polynomial order right at the boundary.

## Setup

Let `B(Q) \asymp C_0 Q^2` be the number of eligible lineages supplied by the
fully protective model in the square window, with adversarial labels
assigned independently and position-blindly as in
[Fixed-Cohort Survival Under Adversarial/Protective Parent Mixing](
fixed-cohort-survival-adversarial-protective-mixing.md), and
`A(Q)=\sum_{r<Q}-\log(1-\alpha_r)`.

## Property

Each of the `B(Q)` eligible lineages survives with probability `e^{-A(Q)}`
(from the fixed-cohort result), so

```math
X_Q^{\mathrm{adversarial/protective}}
\sim
\text{Binomial}\left(B(Q),e^{-A(Q)}\right),
\qquad
\lambda_Q^{\mathrm{adversarial/protective}}
:=\mathbb E[X_Q^{\mathrm{adversarial/protective}}]
=B(Q)e^{-A(Q)}
\asymp C_0Q^2e^{-A(Q)}.
```

The empty-window probability satisfies

```math
\begin{aligned}
\Pr(X_Q^{\mathrm{adversarial/protective}}=0)
&=\left(1-e^{-A(Q)}\right)^{B(Q)}\\
&\le e^{-\lambda_Q^{\mathrm{adversarial/protective}}}.
&&[1-x\le e^{-x}]
\end{aligned}
```

Taking logarithms gives the phase boundary
`\log\lambda_Q^{\mathrm{adversarial/protective}}=2\log Q-A(Q)+O(1)`, so for
every fixed `epsilon>0`,

```math
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{adversarial/protective}}\longrightarrow\infty,\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{adversarial/protective}}\longrightarrow0.
\end{aligned}
```

In the first regime the empty-window probabilities are summable and the
first Borel-Cantelli lemma gives only finitely many empty square windows
almost surely -- with no independence premise needed for that direction.

For the representative schedule `alpha_r ~ c log(r)/r`, `A(Q)\sim c\log Q`
and

```math
\lambda_Q^{\mathrm{adversarial/protective}}\asymp C_0Q^{2-c},
```

giving eventual nonempty windows almost surely for `c<2`, a critical
order-one expected population at `c=2`, and expectation tending to zero for
`c>2`. The leading threshold `c=2` matches the adversarial/random companion
exactly, but the boundary term differs:

```math
\begin{aligned}
\lambda_Q^{\mathrm{adversarial/random}}
&\asymp C\frac{Q^{2-c}}{(\log Q)^2},\\
\lambda_Q^{\mathrm{adversarial/protective}}
&\asymp C_0Q^{2-c}.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

At `c=2`, the random mixture's expectation tends to zero while the
protective mixture retains only an order-one expectation -- still
insufficient by itself for eventual almost-sure nonemptiness.

## Related

- [Balanced good (protective parent) 2-gap companion process](../model.md)
- [Fixed-Cohort Survival Under Adversarial/Protective Parent Mixing](
  fixed-cohort-survival-adversarial-protective-mixing.md) -- supplies the
  per-lineage survival probability `e^{-A(Q)}` used here.
- [Head Recurrence Under Adversarial/Protective Parent Mixing](
  head-recurrence-adversarial-protective-mixing.md)
- [Bad/Random Square-Window Boundary](
  ../../balanced-randomized-2-gap/properties/bad-random-square-window-boundary.md)
  -- the adversarial/random companion's analogous result, compared above.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §5.4](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
