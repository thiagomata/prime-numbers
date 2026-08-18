# Filtering Attrition Bound for Close-Pair Matchings

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

A collection of disjoint close-pair certificates is more resistant to
filtering than the raw edge count. Because a matching uses each 2-gap start at
most once, deleting one start can destroy at most one selected certificate.

This gives a sharp deterministic matching-attrition bound. It does not assert
that the maximum matching is monotone.

## Setup

Let the old complete 2-gap starts be

```math
x_1<x_2<\cdots<x_N
```

and let the new starts be an ordered subsequence obtained by deleting `H`
old starts. No new 2-gap starts are introduced by filtering.

Fix old and new start-difference thresholds `d` and `d'` satisfying

```math
d'\ge d.
```

An adjacent edge is qualifying when its start difference is strictly smaller
than the applicable threshold. Let `D_old` and `D_new` be the maximum sizes of
matchings of qualifying edges in the old and new paths.

## Property

```math
\boxed{
D_{\mathrm{new}}
\ge
D_{\mathrm{old}}-H.
}
```

## Proof

Choose an old qualifying matching of maximum size `D_old`. Its edges are
vertex-disjoint, so every old start is incident to at most one selected edge.
Deleting `H` starts can therefore destroy at most `H` edges of this fixed
matching. At least

```math
D_{\mathrm{old}}-H
```

selected edges retain both endpoints.

Take one retained selected edge `(x_i,x_{i+1})`. Its endpoints were adjacent
in the old ordering, and both survive, so they remain adjacent in the new
subsequence. Their difference is unchanged and satisfies

```math
\begin{aligned}
x_{i+1}-x_i
&<d
&&[\text{Old Selected Edge Is Qualifying}]\\
&\le d'.
&&[\text{Threshold Does Not Decrease}]
\end{aligned}
```

The retained selected edges remain vertex-disjoint, so they form a qualifying
matching in the new path. Since `D_new` is the maximum new matching size,

```math
D_{\mathrm{new}}
\ge
D_{\mathrm{old}}-H.
\qquad[\text{Q.E.D.}]
```

If the right side is negative, the inequality remains true because
`D_new>=0`.

## Sharpness

The coefficient `1` cannot be reduced. Take old starts

```math
5,\ 11
```

with old threshold `d=8`. Their difference is `6`, so `D_old=1`. Delete the
start `11`, giving `H=1` and a new path with no edge, hence `D_new=0`.
Therefore

```math
D_{\mathrm{new}}
=
D_{\mathrm{old}}-H
=0.
```

## Sieve-Sequence Form

For consecutive conditioned layers with incoming primes `r<s`, use

```math
d=2r-2,
\qquad
d'=2s-2.
```

If filter `r` destroys `H_r` complete local 2-gap starts, then

```math
\boxed{
D(Q,s)\ge D(Q,r)-H_r.
}
```

New adjacencies and the larger threshold may supply additional matching edges;
the theorem ignores those gains.

## Limitation

The bound can be zero when the filter destroys at least `D_old` starts. It does
not prove reconstruction, matching monotonicity, or a positive lower envelope
through an arbitrarily long conditioned chain.

## Related

- [Filtering attrition bound for raw close pairs](
  filtering-attrition-bound-raw-close-pairs.md
  ) — deleting one start can remove two raw incident edges.
- [Redundant close-pair capacity](
  ../../candidates/redundant-close-pair-capacity.md
  ) — defines the maximum disjoint certificate count.
- [Local density forces a close-pair matching bound](
  local-density-forces-close-pair-matching.md
  ) — supplies a static matching lower bound from local population density.
