# Cumulative Local Hazard Law

**Status:** Mathematically proved for a tracked companion lineage, with no
stochastic premise beyond `f_r < 1` on the tracked chain. Spatial window and
head conclusions built on this law require additional premises stated where
they are used.

## Meaning

The filter's local effect on a tracked lineage is determined by the total
realized destruction fraction `f_r`, regardless of whether that fraction arose
from random choice, bad labels, targeting, or another allocation mechanism.
The cumulative product of one-step survival factors is exactly the exponential
of a cumulative hazard. This law is the framework every per-model phase
threshold specializes.

## Setup

For a tracked local segment at filter `r`, let `L_r > 0` be the gaps present
before the filter and `H_r` the number destroyed. The realized destruction
fraction and dimensionless worse-than-random factor are

```math
f_r:=\frac{H_r}{L_r},
\qquad
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
&&[\text{Survive Every Filter}]\\
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

so `P_random(Q) ~ C / (log Q)^2`. The `O(1)` reflects the Meissel-Mertens
constant absorbed from the prime harmonic sum; the leading coefficient `2`
comes from the two harmful copies.

## What This Does And Does Not Say

It gives the exact tracked survival exponent once the sequence `(f_r)` is
known. It does **not** by itself imply a square-window or head recurrence
theorem: those need a separate supply premise (how many eligible starts land in
a window or at the head) and, for almost-sure conclusions, a mixing premise.
Those premises are stated in the per-model files that specialize this law.

If one filter has `f_r = 1`, local extinction is immediate and the cumulative
hazard is infinite from that point.
