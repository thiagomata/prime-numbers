# Filtering Attrition Bound for Raw Close Pairs

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

Filtering can destroy many close-pair certificates, but deleting one 2-gap
start can remove at most the two qualifying path edges incident to that start.
When the next layer uses a larger close-pair threshold, every old qualifying
edge whose endpoints survive remains qualifying.

This gives a sharp deterministic attrition bound. It does not assert that the
raw close-pair count is monotone.

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

An old adjacent edge `(x_i,x_{i+1})` is qualifying when

```math
x_{i+1}-x_i<d.
```

Let `P_old` and `P_new` be the old and new qualifying-edge counts, using
thresholds `d` and `d'`, respectively.

## Property

```math
\boxed{
P_{\mathrm{new}}
\ge
P_{\mathrm{old}}-2H.
}
```

## Proof

The old starts form a path. Every deleted start is incident to at most two old
path edges, so the `H` deleted starts are collectively incident to at most
`2H` old qualifying edges. Therefore at least

```math
P_{\mathrm{old}}-2H
```

old qualifying edges have both endpoints surviving.

Take one such edge `(x_i,x_{i+1})`. Its endpoints were adjacent in the old
ordering, so no old start lies strictly between them. Because both endpoints
survive, they are still adjacent in the new subsequence. Their difference is
unchanged and satisfies

```math
\begin{aligned}
x_{i+1}-x_i
&<d
&&[\text{Old Edge Is Qualifying}]\\
&\le d'.
&&[\text{Threshold Does Not Decrease}]
\end{aligned}
```

Thus every surviving old qualifying edge is counted by `P_new`. Hence

```math
P_{\mathrm{new}}
\ge
P_{\mathrm{old}}-2H.
\qquad[\text{Q.E.D.}]
```

If the right side is negative, the inequality remains true because
`P_new>=0`.

## Sharpness

The coefficient `2` cannot be reduced under these assumptions. Take starts

```math
5,\ 11,\ 17,
```

old threshold `d=8`, and new threshold `d'=12`. Both old differences are `6`,
so `P_old=2`. Delete the middle start `11`, giving `H=1`. The new difference
is `12`, which is not strictly smaller than `d'=12`, so `P_new=0`. Therefore

```math
P_{\mathrm{new}}
=
P_{\mathrm{old}}-2H
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
P(Q,s)\ge P(Q,r)-2H_r.
}
```

New adjacencies across deleted starts and the larger threshold may add further
qualifying edges; the theorem ignores those gains and remains a lower bound.

## Limitation

The bound may be zero or negative when `H_r` is large. It does not prove that
short separators reconstruct fast enough, that `P` is monotone, or that a
conditioned chain retains a positive matching.

## Related

- [Redundant close-pair capacity](
  ../../candidates/redundant-close-pair-capacity.md
  ) — defines `P(Q,r)` and the equivalent compressed-separator threshold.
- [Absence of 2-gaps is stable](
  absence-of-two-gaps-is-stable.md
  ) — filtering cannot create a new 2-gap from merged positive gaps.
- [Local density forces a close-pair matching bound](
  local-density-forces-close-pair-matching.md
  ) — supplies static lower bounds from the local population.
