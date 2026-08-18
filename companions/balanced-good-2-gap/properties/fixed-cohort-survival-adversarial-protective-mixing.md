# Fixed-Cohort Survival Under Adversarial/Protective Parent Mixing

**Status:** Mathematically proved for the balanced good (protective parent)
companion, mixed with the balanced adversarial companion under
position-blind, independent parent-label assignment. Not a claim about the
real modular filter.

## Meaning

Follow a fixed finite cohort of lineages through a chain of filters. At each
filter, a surviving lineage independently becomes an adversarial parent
(destroys its target child) with probability `alpha_r`, or a protective
parent (preserves it) with probability `1-alpha_r`. Removing the random
factor `1-2/r` that the balanced-random companion pays at every filter makes
each surviving transition cheaper, but a fixed positive adversarial share
still wipes the cohort out almost surely -- redundancy only postpones
extinction, it does not prevent it.

## Setup

Let `N_0` be the number of locally relevant lineages at the start of the
chain, followed through filters `r<Q`. At filter `r`, each surviving lineage
independently receives the adversarial label with probability `alpha_r` (its
target child is destroyed) or the protective label with probability
`1-alpha_r` (its target child is preserved), and

```math
A(Q):=\sum_{r<Q}-\log(1-\alpha_r).
```

## Property

One lineage survives the complete chain with probability

```math
\begin{aligned}
P_Q
&=\prod_{r < Q}(1-\alpha_r)
&&[\text{Survive Every Independent Filter Label}]\\
&=e^{-A(Q)}.
&&[\text{Definition Of }A(Q)]
\end{aligned}
```

Independence between lineages gives

```math
X_Q\sim\text{Binomial}(N_0,P_Q),
\qquad
\mathbb E[X_Q]=N_0e^{-A(Q)},
\qquad
\Pr(X_Q > 0)=1-\left(1-e^{-A(Q)}\right)^{N_0}.
```

For one filter this reduces to
`X_{k+1}\mid X_k=N\sim\text{Binomial}(N,1-\alpha_r)`, with immediate wipeout
probability `alpha_r^N`: population redundancy is useful under blind label
assignment, since every relevant lineage must draw the adversarial label in
the same transition to erase the cohort in one step.

If `alpha_r=alpha>0` is constant, then

```math
P_Q=(1-\alpha)^{\pi(Q)+O(1)}\longrightarrow0,
```

so every one of the finite `N_0` lineages eventually draws the adversarial
label with probability one, and the fixed cohort becomes extinct almost
surely -- even though every lineage still has `r-2` descendants elsewhere in
the complete period at every step.

Compared with the adversarial/random mixture (adversarial vs. uniform
placement), the adversarial/protective law removes the random-placement
factor entirely:

```math
\begin{aligned}
s_r^{\mathrm{adversarial/random}}
&=(1-\alpha_r)\left(1-\frac2r\right),\\
s_r^{\mathrm{adversarial/protective}}
&=1-\alpha_r.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

This improvement is local: it does not overcome a fixed positive adversarial
share repeated through infinitely many filters.

## Related

- [Balanced good (protective parent) 2-gap companion process](../model.md)
- [Growing Square Windows Under Adversarial/Protective Parent Mixing](
  growing-square-window-adversarial-protective-mixing.md) -- the same
  mixture's square-window analogue.
- [Head Recurrence Under Adversarial/Protective Parent Mixing](
  head-recurrence-adversarial-protective-mixing.md)
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §5.3](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
