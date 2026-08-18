# Global Persistence Independence

**Status:** Mathematically proved for every balanced companion, with no
stochastic premise. This is a fact about constructed companion processes, not a
claim about the real modular filter. The matching real-sieve global count is
[Global 2-Gap Count](../../properties/sieve-sequence/exact-global-two-gap-count.md).

## Meaning

No choice of the two harmful copy indices can change the number of surviving
descendants. Random, adversarial, friendly, and mixed companions all have the
same global population growth law. This matters because any later local
extinction cannot be blamed on exhausting the complete-period supply: the
population keeps growing unboundedly under every balanced policy.

## Setup

Let `G_k` be the 2-gap descendants before installing prime `r_k`, with
`N_k = |G_k|`. Every balanced companion removes exactly two of each parent's
`r_k` copies, regardless of which two.

## Property

```math
\begin{aligned}
N_{k+1}
&=\sum_{g\in\mathcal G_k}(r_k-2)
&&[\text{Exactly Two Copies Removed Per Parent}]\\
&=(r_k-2)N_k.
&&[\text{Simplification}]
\end{aligned}
```

Iterating,

```math
\begin{aligned}
N_k
&=N_0\prod_{i < k}(r_i-2)
&&[\text{Iteration}]\\
&>0
&&[r_i\ge5]\\
&\longrightarrow\infty.
&&[\text{Every Factor Is At Least }3]
\end{aligned}
```

Hence global 2-gap persistence holds for every adversarial schedule. $\blacksquare$

The recurrence is identical to the proved real-sieve count in
[Global 2-Gap Count](../../properties/sieve-sequence/exact-global-two-gap-count.md);
the companion family shares it by construction.

## What This Does And Does Not Say

It says the complete-period 2-gap count grows without bound for every
companion. It does **not** say anything about where survivors land: a balanced
adversarial companion can drive local or head occupancy to zero forever while
the global count explodes (see
[Targeted Head Suppression](../balanced-adversarial-2-gap/properties/targeted-head-suppression.md)).
Local survival is governed by the [Cumulative Local Hazard Law](cumulative-local-hazard-law.md)
and the per-model specializations, not by this global recurrence.
