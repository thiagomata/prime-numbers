# Head Recurrence Under Adversarial/Protective Parent Mixing

**Status:** Mathematically proved conditional on a bounded-below head
availability premise (`b_Q \ge b > 0`) and, for the divergent direction,
independence or adequate weak cross-layer mixing between head events. For
the balanced good (protective parent) companion, mixed with the balanced
adversarial companion under position-blind, independent parent-label
assignment. Not a claim about the real modular filter.

## Meaning

At the distinguished head position, the protective policy can preserve an
eligible lineage but cannot manufacture one that was never eligible. Given
availability, the lineage need only avoid every adversarial label in its
chain. This changes which side of the critical logarithmic schedule counts
as recurrent, compared with the adversarial/random companion, even though
both mixtures share the same leading threshold scale.

## Setup

Let `b_Q` be the head's availability probability and suppose `b_Q \ge b > 0`
for all sufficiently large `Q`. Let `H_Q` be the event that the head is a
2-gap at stage `Q`, and `A(Q)=\sum_{r<Q}-\log(1-\alpha_r)` as in
[Fixed-Cohort Survival Under Adversarial/Protective Parent Mixing](
fixed-cohort-survival-adversarial-protective-mixing.md).

## Property

Conditional on availability, the lineage must avoid every adversarial
assignment in its chain, so

```math
\Pr(H_Q)=b_Qe^{-A(Q)}.
```

The lower bound on `b_Q` makes the recurrence criterion equivalent, up to
positive constants, to `\sum_{Q\text{ prime}}e^{-A(Q)}`. Under adequate
cross-layer mixing, the second Borel-Cantelli lemma gives

```math
\sum_{Q\text{ prime}}e^{-A(Q)}=\infty
\Longrightarrow
H_Q\text{ occurs infinitely often almost surely}.
```

If the series converges, the first Borel-Cantelli lemma gives only finitely
many head events almost surely, with no independence premise needed for
that direction.

For `alpha_r \sim c\log(r)/r`, `e^{-A(Q)}\asymp Q^{-c}`, so the prime-head
series behaves like `\sum_{Q\text{ prime}} Q^{-c}`, which diverges at `c=1`
and converges for `c>1`:

```math
\begin{aligned}
c\le1
&\Longrightarrow
\text{infinitely many head events almost surely, with mixing},\\
c > 1
&\Longrightarrow
\text{only finitely many head events almost surely}.
\end{aligned}
```

This boundary differs from adversarial/random mixing, where the
balanced-random head density contributes an extra `(\log Q)^{-2}` factor:

```math
\begin{aligned}
\Pr(H_Q^{\mathrm{adversarial/random}})
&\asymp\frac1{Q^c(\log Q)^2},\\
\Pr(H_Q^{\mathrm{adversarial/protective}})
&\asymp\frac{b_Q}{Q^c}.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

At `c=1`, the adversarial/random prime series converges while the
adversarial/protective series diverges: the protective parent policy moves
the critical boundary itself into the recurrent side, even though both
mixtures share the same leading threshold scale. For the gentler schedule
`alpha_r \sim c/r`, the occurrence probability is comparable to
`(\log Q)^{-c}` and the sum over prime heads diverges for every fixed finite
`c`.

## Related

- [Balanced good (protective parent) 2-gap companion process](../model.md)
- [Fixed-Cohort Survival Under Adversarial/Protective Parent Mixing](
  fixed-cohort-survival-adversarial-protective-mixing.md) -- supplies the
  per-lineage survival probability `e^{-A(Q)}` used here.
- [Growing Square Windows Under Adversarial/Protective Parent Mixing](
  growing-square-window-adversarial-protective-mixing.md)
- The adversarial/random companion's analogous head-recurrence result is
  compared above; as of this writing it is registered in
  [`balanced-randomized-2-gap/README.md`](
  ../../balanced-randomized-2-gap/README.md) as "Bad/Random Head Boundary"
  but not yet filed as its own property file.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §5.5](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
