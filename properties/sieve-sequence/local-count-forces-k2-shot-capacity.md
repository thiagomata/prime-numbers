# A Local Count Forces the k=2 Shot-Capacity Premise

**Status:** Mathematically proved (conditional local-count lemma). Stainless
verification is not claimed here.

## Meaning

Candidate #14 needs two complete 2-gaps close enough that one incoming filter
cannot destroy both. This property gives an exact sufficient local count: if
too many 2-gap starts lie in the fixed square window, they cannot all remain
separated by the distance required to avoid the `k=2` shot-capacity premise.

The theorem is a finite ordered-point argument. It does not assume that local
2-gaps are uniformly distributed, and it does not derive the required count
from a complete-period count.

## Setup

Fix a future prime head `Q` and a conditioned filter layer with incoming prime
`r`, where

```math
5\le r<Q.
```

Let

```math
W_Q=[Q,Q^2)
```

and suppose the layer contains `N` complete 2-gaps in this window, with starts

```math
Q\le x_1<x_2<\cdots<x_N
\qquad\text{and}\qquad
x_i+2<Q^2.
```

Because every quantity is an integer, completeness gives

```math
x_N\le Q^2-3.
```

Define the available start range and the forbidden minimum separation by

```math
L_Q=Q^2-Q-3,
\qquad
d_r=2r-2.
```

## Local Count Threshold

If

```math
\boxed{
N\ge
\left\lfloor\frac{L_Q}{d_r}\right\rfloor+2,
}
```

then some consecutive starts `x_i<x_{i+1}` satisfy

```math
x_{i+1}+2-x_i<2r.
```

Equivalently,

```math
\boxed{
G_r(W_Q)\ge
\left\lfloor
\frac{Q^2-Q-3}{2r-2}
\right\rfloor+2
}
```

forces the bounded-pair premise at layer `r`.

## Proof

Assume for contradiction that no consecutive pair has an enclosure shorter
than `2r`. Then, for every `1\le i<N`,

```math
\begin{aligned}
x_{i+1}+2-x_i
&\ge 2r
&&[\text{Contradiction Hypothesis}]\\
x_{i+1}-x_i
&\ge 2r-2
&&[\text{Simplification}]\\
&=d_r.
&&[\text{By Definition}]
\end{aligned}
```

Summing the consecutive differences telescopes:

```math
\begin{aligned}
x_N-x_1
&=
\sum_{i=1}^{N-1}(x_{i+1}-x_i)
&&[\text{Telescoping}]\\
&\ge
(N-1)d_r.
&&[\text{By the Separation Bound}]
\end{aligned}
```

The square-window endpoints give the opposite bound:

```math
\begin{aligned}
x_N-x_1
&\le
(Q^2-3)-Q
&&[\text{By the Endpoint Bounds}]\\
&=
Q^2-Q-3
&&[\text{Simplification}]\\
&=
L_Q.
&&[\text{By Definition}]
\end{aligned}
```

Therefore the contradiction hypothesis implies

```math
(N-1)d_r\le L_Q.
```

But the assumed count threshold gives

```math
\begin{aligned}
N-1
&\ge
\left\lfloor\frac{L_Q}{d_r}\right\rfloor+1
&&[\text{By the Count Hypothesis}]\\
&>
\frac{L_Q}{d_r},
&&[\text{Floor Property}]
\end{aligned}
```

where `d_r>0` because `r>=5`. Multiplying by `d_r` yields

```math
(N-1)d_r>L_Q,
```

contradicting the necessary inequality above. Hence some consecutive pair
satisfies

```math
x_{i+1}+2-x_i<2r.
\qquad[\text{Q.E.D.}]
```

## Consequence For Candidate #14

Set

```math
J_r=[x_i,x_{i+1}+2).
```

Both complete 2-gaps lie in `J_r`, so `G_r(J_r)>=2`. The proved shot-spacing
identity is

```math
\sigma_r(2)=2r.
```

The close-pair conclusion therefore gives

```math
\operatorname{len}(J_r)
=x_{i+1}+2-x_i
<2r
=\sigma_r(2).
```

Thus `J_r` satisfies candidate #14's per-layer premise with `k_r=2`. The
incoming filter has at most one shot in `J_r`; after filter `3`, one shot
destroys at most one of the two endpoint-disjoint 2-gaps. At least one of the
two gaps survives this layer.

## Exact Boundary

The threshold is exact for an arbitrary ordered set constrained only by the
window endpoints. If

```math
N=
\left\lfloor\frac{L_Q}{d_r}\right\rfloor+1,
```

the abstract points

```math
Q,\ Q+d_r,\ Q+2d_r,\ \ldots
```

can fit inside the available start range, and every consecutive enclosure has
length at least `2r`. Additional sieve-specific residue information may yield
a stronger threshold, but order and window width alone do not.

The theorem does not prove that

```math
G_r(W_Q)\ge
\left\lfloor
\frac{Q^2-Q-3}{2r-2}
\right\rfloor+2
```

holds at every layer or for infinitely many future heads. Establishing such a
conditioned short-window population bound remains the unresolved placement
problem. Complete-period abundance by itself does not supply it.

## Related

- [Bounded pair separation gives the k=2 interval premise](
  interval-premise-from-pair-existence.md
  ) — converts the close pair produced here into the shot-capacity premise.
- [Fixed-k shot spacing](
  stable-small-k-shot-spacing.md
  ) — supplies the exact identity `sigma_r(2)=2r`.
- [Sharp local 2-gap survival threshold](
  sharp-local-two-gap-survival-threshold.md
  ) — a different local-count condition based on the exact number of accepted
  filter strikes.
- [Hereditary shot-spacing capacity](
  ../../candidates/hereditary-shot-spacing-capacity.md
  ) — candidate #14, whose per-layer `k=2` premise this property discharges
  under an explicit local-count hypothesis.
