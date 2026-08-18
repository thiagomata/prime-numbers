# Bad/Random Square-Window Boundary

**Status:** Conditional mathematical theorem about the bad/random companion.
Assumes mixed surviving starts obey the spatial-uniformity model. Not a claim
about the real modular filter.

## Meaning

For a position-blind mixture of adversarial and random harmful-index
selection, the expected square-window population crosses from unbounded growth
to decay at a precise cumulative adversarial budget. The boundary is set by
the quadratic window length competing against the cumulative excess hazard.

## Setup

Let the square-safe window have length `L_Q ~ Q^2`, and let the per-filter
adversarial share be `alpha_r in [0,1]`. Define the cumulative adversarial
budget

```math
A(Q):=\sum_{r < Q}-\log(1-\alpha_r).
```

The [Cumulative Local Hazard Law](../../properties/cumulative-local-hazard-law.md)
specializes because `1 - f_r = (1 - alpha_r)(1 - 2/r)`.

## Property

The expected mixed population is

```math
\begin{aligned}
\lambda_Q^{\mathrm{mix}}
&=L_Q\delta_Q^{\mathrm{mix}}
&&[\text{Expected Uniform Occupancy}]\\
&\asymp
C\frac{Q^2}{(\log Q)^2}e^{-A(Q)}.
&&[\text{Substitution}]
\end{aligned}
```

Taking logarithms exposes the threshold:

```math
\log\lambda_Q^{\mathrm{mix}}
=2\log Q-2\log\log Q-A(Q)+O(1).
```

Therefore, for every fixed `epsilon > 0`,

```math
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,
&&[\text{Subcritical Adversarial Budget}]\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow0.
&&[\text{Supercritical Adversarial Budget}]
\end{aligned}
```

The boundary `A(Q) = 2 log Q + o(log Q)` requires its lower-order terms; the
`-2 log log Q` contribution cannot be discarded there.

Under uniform placement, an empty-window estimate has the usual form
`Pr(X_Q = 0) <= e^{-lambda_Q^{mix}}`. Whenever
`sum_{Q prime} e^{-lambda_Q^{mix}} < infinity`, the first Borel-Cantelli lemma
gives only finitely many empty square windows almost surely. A convenient
sufficient condition is `lambda_Q^{mix} >= (1 + epsilon) log Q` for all
sufficiently large `Q`. $\blacksquare$

## What This Does And Does Not Say

The boundary is `A(Q) ~ 2 log Q`. The specializations
[Reciprocal-Decay](reciprocal-decay-specialization.md) and
[Log-Over-Linear Decay](log-over-linear-decay-specialization.md) substitute
specific `alpha_r` schedules; [Constant-Share Trivial Fatality](constant-share-trivial-fatality.md)
treats the case where `alpha_r` does not decay. The safe-window conclusion is
not claimed for the real sieve.
