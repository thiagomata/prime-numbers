# Local Density Forces a Close-Pair Matching Bound

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

After filters `2` and `3` are installed, all complete 2-gap starts occupy one
residue class modulo `6`. This arithmetic spacing turns a local population
count into more than a yes-or-no close-pair certificate: it gives an explicit
lower bound on both the number of qualifying consecutive pairs and the number
of pairwise disjoint certificates.

The theorem is finite and deterministic. It assumes neither uniform
distribution nor independence, and it does not claim that its lower bound
grows along every future-window chain.

## Setup

Fix an incoming filter `r>=5`. Let

```math
x_1<x_2<\cdots<x_N
```

be `N>=1` complete 2-gap starts at a post-filter-3 layer, contained in an
integer range of length at most `L`:

```math
x_N-x_1\le L.
```

Every start satisfies `x_i=5 modulo 6`. Define

```math
d=2r-2
```

and call the consecutive edge `i` **qualifying** when

```math
x_{i+1}+2-x_i<2r,
```

equivalently, when

```math
x_{i+1}-x_i<d.
```

Let `P` be the number of qualifying edges, and let `D` be the maximum number
of qualifying edges with no shared start. Finally, define

```math
\Delta
=
6\left\lceil\frac d6\right\rceil,
```

the least multiple of `6` not smaller than `d`.

## Property

The raw qualifying-edge count satisfies

```math
\boxed{
P
\ge
\max\left(
0,
\left\lceil
\frac{\Delta(N-1)-L}{\Delta-6}
\right\rceil
\right).
}
```

The disjoint certificate count satisfies

```math
\boxed{
D\ge\left\lceil\frac P2\right\rceil.
}
```

Combining the two gives

```math
\boxed{
D
\ge
\left\lceil
\frac12
\max\left(
0,
\left\lceil
\frac{\Delta(N-1)-L}{\Delta-6}
\right\rceil
\right)
\right\rceil.
}
```

## Proof of the Raw-Edge Bound

Because every start is congruent to `5 modulo 6`, each positive consecutive
difference

```math
g_i=x_{i+1}-x_i
```

is a positive multiple of `6`. Hence every qualifying difference is at least
`6`.

A nonqualifying difference satisfies `g_i>=d`. Since it is a multiple of `6`,
it must satisfy

```math
g_i\ge\Delta.
```

There are `P` qualifying differences and `N-1-P` nonqualifying differences.
Summing and telescoping therefore gives

```math
\begin{aligned}
x_N-x_1
&=\sum_{i=1}^{N-1}g_i
&&[\text{Telescoping}]\\
&\ge6P+\Delta(N-1-P)
&&[\text{By the Two Difference Bounds}]\\
&=\Delta(N-1)-(\Delta-6)P.
&&[\text{Simplification}]
\end{aligned}
```

The containing-range hypothesis gives the opposite bound:

```math
\begin{aligned}
L
&\ge x_N-x_1
&&[\text{By the Range Bound}]\\
&\ge\Delta(N-1)-(\Delta-6)P.
&&[\text{By Telescoping}]
\end{aligned}
```

Since `r>=5`, `d>=8`, so `\Delta>=12` and `\Delta-6>0`. Rearranging yields

```math
P
\ge
\frac{\Delta(N-1)-L}{\Delta-6}.
```

The count `P` is a nonnegative integer. Applying the ceiling and the zero
floor proves

```math
P
\ge
\max\left(
0,
\left\lceil
\frac{\Delta(N-1)-L}{\Delta-6}
\right\rceil
\right).
\qquad[\text{Q.E.D.}]
```

## Proof of the Matching Bound

Every qualifying edge has an index `i` in the path on
`x_1,\ldots,x_N`. Split the qualifying indices into their odd-indexed and
even-indexed classes.

Two distinct indices of the same parity differ by at least `2`, so their edges
share no start. Each parity class is therefore a matching. Together the two
classes contain all `P` qualifying edges, so the larger class contains at
least

```math
\left\lceil\frac P2\right\rceil
```

edges. Since `D` is the maximum matching size,

```math
D\ge\left\lceil\frac P2\right\rceil.
\qquad[\text{Q.E.D.}]
```

## Capacity-Surplus Corollary

If the ordinary `k=2` capacity surplus is positive,

```math
(N-1)d>L,
```

then `\Delta>=d` implies

```math
\Delta(N-1)-L>0.
```

The raw-edge lower bound gives `P>=1`, and the matching bound gives `D>=1`.
Thus the theorem recovers the existence of one close pair. More importantly,
it quantifies additional certificates whenever

```math
\Delta(N-1)-L
```

is substantially larger than `\Delta-6`.

Each of the `D` disjoint close-pair certificates leaves a distinct 2-gap
survivor under filter `r`. Therefore the next-layer local population satisfies

```math
G_{r^+}\ge D.
```

## Consequence for Candidate #18

This theorem proves the algebraic conversion that candidate #18 needs. To
prove unbounded redundancy along selected future-window chains, it is now
enough to establish that

```math
\frac{\Delta_r(G_r(W_Q)-1)-L_Q}{\Delta_r-6}
```

has an unbounded positive lower bound at every required layer.

That is still a conditioned local-density theorem. Neither the present
algebra nor a complete-period 2-gap count proves it.

## Related

- [Isolation of 2-gaps after filtering by 3](
  two-gap-isolation-after-filter-three.md
  ) — supplies the common start class modulo `6`.
- [A local count forces the k=2 shot-capacity premise](
  local-count-forces-k2-shot-capacity.md
  ) — proves the corresponding existence threshold without quantifying
  redundancy.
- [Redundant close-pair capacity](
  ../../candidates/redundant-close-pair-capacity.md
  ) — asks whether the disjoint lower bound grows throughout infinitely many
  conditioned chains.
