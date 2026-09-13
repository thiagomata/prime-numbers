# Cumulative Local Hazard Law

**Status:** Mathematically proved for deterministic conditional hazards of a
tracked companion lineage, and separately for observed nested-cohort ratios. Spatial window and
head conclusions built on this law require additional premises stated where
they are used.

## Meaning

The filter's effect on an eligible lineage is described by its probability of
destruction conditional on earlier survival. This probability is distinct from
the observed fraction destroyed in a finite population.
The cumulative product of one-step survival factors is exactly the exponential
of a cumulative hazard. This law is the framework every per-model phase
threshold specializes.

## Setup

All filter sums run over primes `r_0 <= r < Q` for a fixed `r_0 >= 5`.
Let `f_r` be the deterministic probability of destroying a specified candidate
conditional on initial eligibility and survival through every earlier filter.
Every factor, including the finite prefix, must satisfy `0 <= f_r < 1`.
Define its relative hazard by

```math
w_r:=\frac{f_r}{2/r}=\frac{rf_r}{2}.
```

The benchmark `2/r` is the random destruction rate; `w_r = 1` recovers random,
`w_r = 0` is the good endpoint, and `w_r = r/2` is complete local destruction.
Assume `f_r < 1` for every filter on the tracked chain.

## Property

Define the cumulative local hazard

```math
D(Q)
:=\sum_{r < Q}-\log(1-f_r)
=\sum_{r < Q}-\log\left(1-\frac{2w_r}{r}\right).
```

Then the complete tracked survival factor is exactly

```math
\begin{aligned}
P(Q)
&=\prod_{r < Q}(1-f_r)
&&[\text{Conditional Probability Chain Rule}]\\
&=\exp\left(\sum_{r < Q}\log(1-f_r)\right)
&&[\text{Product To Sum}]\\
&=e^{-D(Q)}.
&&[\text{Definition Of }D(Q)]
\end{aligned}
```

$\blacksquare$

For the random benchmark `w_r = 1`,

```math
\begin{aligned}
D_{\mathrm{random}}(Q)
&=\sum_{r < Q}-\log\left(1-\frac2r\right)\\
&=2\log\log Q+O(1),
\end{aligned}
```

so `P_random(Q) \asymp C / (log Q)^2`. The `O(1)` reflects the Meissel-Mertens
constant absorbed from the prime harmonic sum; the leading coefficient `2`
comes from the two harmful copies.

## What This Does And Does Not Say

The product uses conditional probabilities; filter independence is not needed
for the chain rule. For a fixed nested cohort with no births or immigration,
there is a different exact identity. Writing `L_r` for its pre-filter count,
`H_r` for its losses, and `\widehat f_r=H_r/L_r`, we have

```math
\frac{L_{\mathrm{final}}}{L_{\mathrm{initial}}}
=\prod_r(1-\widehat f_r).
```

This ratio telescopes because `L_next=L_r-H_r`. Moving windows or expanding
populations do not satisfy this accounting identity automatically.

## Premises For Probability Applications

All window and head events must be defined on a common probability space.
For a window with `B(Q)` eligible histories, assume each history has survival
probability `P(Q)`; then linearity gives `E[X_Q]=B(Q)P(Q)`. For a head candidate,
assume availability `b_Q >= b > 0` and this survival law conditional on
availability; then `Pr(H_Q)=b_Q P(Q)`.

**Blind placement** means the additional bound
`Pr(X_Q=0) <= exp(-E[X_Q])`. Uniform one-point marginals do not imply it.
If these upper bounds are summable over prime heads, the first Borel–Cantelli
lemma gives eventual window occupancy without independence across windows.

For head recurrence, put `S(X)=sum_{Q<=X} Pr(H_Q)`. **Adequate mixing** means,
when `S(X)` diverges,

```math
\sum_{P,Q\le X}\Pr(H_P\cap H_Q)=(1+o(1))S(X)^2,
```

where both indices run over prime heads. The Kochen–Stone criterion then gives
infinitely many head events almost surely. A convergent head series gives
only finitely many events by the first Borel–Cantelli lemma without mixing.
These are additional assumptions, not consequences of the balanced count law.

A factor equal to one in destruction eliminates that tracked candidate or
cohort. It does not eliminate future candidates in newly chosen windows.
