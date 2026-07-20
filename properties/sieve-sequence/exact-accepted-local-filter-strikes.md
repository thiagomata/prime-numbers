# Exact Accepted Filter Strikes in the Next Safe Window

**Status:** Mathematically proved, using Bertrand's postulate. Stainless
verification is not claimed here.

## Meaning

Counting every multiple of the new filter prime substantially overestimates
local destruction: most such multiples were already removed by smaller prime
filters. This property counts exactly the multiples that are still accepted.

## Setup

Let `p>=5` be the current head, let `q` be the next prime after `p`, and let

```math
M=\prod_{r<p}r.
```

The transition installs filter `p`. Consider the next safe window

```math
W=[q,q^2)
```

and define

```math
K=\left\lfloor\frac{q^2-1}{p}\right\rfloor.
```

## Property

The accepted multiples of `p` in `W` before applying filter `p` are exactly

```math
pr
\quad\text{where }r\text{ is prime and }p\le r\le K.
```

Their exact number is therefore

```math
A(p,q)=\pi(K)-\pi(p-1).
```

## Proof

Every multiple in the half-open window has the form `pk` with

```math
2\le k\le K.
```

The lower bound follows from `p<q<2p`. The value `pk` survives all old filters
exactly when `k` has no prime divisor smaller than `p`, because `p` itself is
coprime to `M`.

Bertrand's postulate gives `q<2p`, hence

```math
K<\frac{q^2}{p}<4p\le p^2.
```

If `k<p^2` were composite and had no prime factor below `p`, both of its prime
factors would be at least `p`, forcing `k>=p^2`, a contradiction. Thus every
accepted `k` in the range is prime and at least `p`. The converse is immediate:
every such prime `k` is coprime to `M`.

## Comparison With The Raw Bound

The number of all multiples of `p` in `W` is

```math
R(p,q)=
\left\lfloor\frac{q^2-1}{p}\right\rfloor
-\left\lfloor\frac{q-1}{p}\right\rfloor.
```

Always `A(p,q)<=R(p,q)`, often by a large margin. Only the `A(p,q)` accepted
multiples can actually be removed by the transition.

## Limitation

Not every removed accepted value is necessarily an endpoint of a 2-gap.
Therefore `A(p,q)` is an exact strike count but only an upper bound on the
number of destroyed local 2-gaps.
