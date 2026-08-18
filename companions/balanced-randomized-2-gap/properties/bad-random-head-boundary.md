# Bad/Random Head Boundary

**Status:** Conditional mathematical theorem about the bad/random companion.
Assumes uniform head marginals and, for the divergent direction,
independence or an adequate weak-mixing substitute between head events.
Not a claim about the real modular filter.

## Meaning

The head is a single distinguished position, so it receives no quadratic
window reserve the way a square-safe window does -- its occurrence
probability is just the surviving local density itself. Turning a divergent
sum of these probabilities into almost-sure recurrence additionally needs
independence, or a sufficiently strong weak-mixing substitute, between
head events at successive layers -- a strictly stronger requirement than
the square-window case, which needs no such premise for its convergent
direction.

## Setup

Let `H_Q` be the event that the head is a 2-gap at stage `Q`, in the
position-blind adversarial/random mixture of
[Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md),
with mixed density `\delta_Q^{\mathrm{mix}}` and cumulative adversarial
budget `A(Q):=\sum_{r<Q}-\log(1-\alpha_r)` as defined there.

## Property

Under uniform head marginals,

```math
\Pr(H_Q)
\asymp
\delta_Q^{\mathrm{mix}}
\asymp
\frac{C}{(\log Q)^2}e^{-A(Q)}.
```

Under adequate cross-layer mixing, the second Borel-Cantelli lemma gives

```math
\sum_{Q\text{ prime}}\Pr(H_Q)=\infty
\Longrightarrow
H_Q\text{ occurs infinitely often almost surely}.
```

For `alpha_r ~ c/r` ([Reciprocal-Decay Specialization](
reciprocal-decay-specialization.md)),

```math
\Pr(H_Q)\asymp\frac{C}{(\log Q)^{2+c}},
```

and the sum over prime `Q` diverges for every fixed `c`. Reciprocal decay is
therefore compatible with infinitely many head events under mixing, for
every finite decay rate.

For `alpha_r ~ c\log r/r` ([Log-Over-Linear Decay Specialization](
log-over-linear-decay-specialization.md)),

```math
\Pr(H_Q)\asymp\frac{C}{Q^c(\log Q)^2}.
```

Using prime density `dQ/\log Q`, the corresponding series has the same
convergence behavior as `\int^\infty dx/(x^c(\log x)^3)`. Therefore

```math
\begin{aligned}
c < 1
&\Longrightarrow
\sum_{Q\text{ prime}}\Pr(H_Q)=\infty,\\
c\ge 1
&\Longrightarrow
\sum_{Q\text{ prime}}\Pr(H_Q) < \infty.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

For `c<1`, adequate mixing implies infinitely many head events almost
surely. For `c\ge1`, the first Borel-Cantelli lemma implies only finitely
many head events almost surely -- no independence assumption is needed for
that convergent direction.

## What This Does And Does Not Say

The head threshold `c=1` is stricter than the log-over-linear-decay
square-window threshold `c=2` from
[Log-Over-Linear Decay Specialization](log-over-linear-decay-specialization.md).
There is an intermediate regime `1\le c<2` in which square-safe windows
remain populated almost surely under the spatial model, while head
recurrence fails almost surely in the mixed companion. Neither conclusion
is claimed for the real sieve.

## Related

- [Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md)
- [Reciprocal-Decay Specialization](reciprocal-decay-specialization.md)
- [Log-Over-Linear Decay Specialization](log-over-linear-decay-specialization.md)
- [Head Recurrence Under Adversarial/Protective Parent Mixing](
  ../../balanced-good-2-gap/properties/head-recurrence-adversarial-protective-mixing.md)
  -- the balanced-good companion's analogous head result, for comparison.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §4.4](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
