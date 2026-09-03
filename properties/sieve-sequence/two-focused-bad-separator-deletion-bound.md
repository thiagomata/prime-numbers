# Two-Focused Bad-Separator Deletion Bound

**Status:** Mathematically proved. The measurement section is finite empirical
evidence. Stainless verification is not claimed.

## Meaning

The post-filter-3 2-focused compression alternates

```text
2-cell, run-cell, 2-cell, run-cell, ...
```

around the complete cycle. A run-cell `R` is the sum of every non-2 raw gap
between its neighboring 2-gaps.

This property treats the 2-cells as vertices and the run-cells as edges. An
incoming filter can destroy both endpoints of an edge only for three explicit
congruence classes of its run value. Every other edge protects at least one of
its neighboring 2-gaps. The number and arrangement of the exceptional edges
therefore give direct deterministic survival bounds.

This is not an argument about the sum of shot distances. It is a local
adjacency obstruction to simultaneous deletion.

## Endpoint Arithmetic

Consider one focused block

```math
[2,R,2].
```

If the first 2-gap starts at `x`, its endpoints and those of the next 2-gap are

```math
x,\quad x+2,\quad x+R+2,\quad x+R+4.
```

Filter `p>=5` can destroy both 2-gaps only if one endpoint of the first and one
endpoint of the second are congruent modulo `p`. The four possible cross-pair
differences are

```math
R,\quad R+2,\quad R+2,\quad R+4.
```

Define the separator to be **bad for `p`** when

```math
p\mid R(R+2)(R+4),
```

and **good** otherwise. Then

```math
\boxed{
\text{both adjacent 2-gaps are destroyed}
\quad\Longrightarrow\quad
R\text{ is bad for }p.
}
```

Equivalently, every good separator guarantees that at least one of its two
adjacent 2-gaps survives. With start separation `d=R+2`, the three bad cases
are exactly `p|d`, `p|d-2`, or `p|d+2` from the [Pair Local Factor] property.

## Cyclic Deletion-Graph Bound

Let a complete focused cycle have `N>0` 2-cell vertices and `N` separator
edges. For one incoming filter, write

```math
B=\#\{\text{bad separator edges}\},
\qquad
D=\#\{\text{destroyed 2-cells}\},
\qquad
S=N-D.
```

Every edge joining two destroyed vertices is bad. If `S>0`, let `c` be the
number of cyclic runs of destroyed vertices. The number `t` of
destroyed-destroyed edges is

```math
t=D-c.
```

Every destroyed run is separated from the next by at least one survivor, so
`c<=S`. Hence

```math
\begin{aligned}
t&\ge D-S,\\
D-S&\le B,\\
2D&\le N+B.
\end{aligned}
```

If `S=0`, every edge joins two destroyed vertices, so `B=N`; the same final
bound holds. Therefore

```math
\boxed{
D\le\left\lfloor\frac{N+B}{2}\right\rfloor,
\qquad
S\ge\left\lceil\frac{N-B}{2}\right\rceil.
}
```

In particular, extinction requires `B=N`: **every** focused separator must be
bad.

If `k` consecutive 2-cells are destroyed, the `k-1` separators between them
join destroyed pairs and are therefore consecutive bad edges. Thus

```math
\boxed{
\text{maximum destroyed-vertex run}
\le
1+\text{maximum bad-edge run},
}
```

unless the whole cycle is destroyed, in which case every edge is bad.

## Linear Window Bound

For a linear block of `m` 2-cells, let `b` of its `m-1` internal separators be
bad. Removing those bad edges divides the good-edge graph into at most `b+1`
path components. A destroyed set contains no adjacent pair along a good edge,
so it contains at most the sum of the maximum independent-set sizes of those
paths. Consequently

```math
\boxed{
\text{survivors in the block}
\ge
\left\lceil\frac{m-b-1}{2}\right\rceil.
}
```

The simplest and most useful special case needs no rounding formula: if the
block contains one good separator, its two adjacent 2-gaps cannot both be
destroyed, so the block contains a survivor.

## The `2p-4` Certificate

Every post-filter-3 raw gap is even, so every focused run sum `R` is positive
and even. If `R` is bad, one of `R`, `R+2`, or `R+4` is a positive even
multiple of the odd prime `p`. The smallest possible such multiple is `2p`.
Therefore

```math
\boxed{R\text{ bad}\quad\Longrightarrow\quad R\ge2p-4.}
```

Its contrapositive is

```math
\boxed{R<2p-4\quad\Longrightarrow\quad R\text{ good}.}
```

This is exactly candidate #14's `k=2` close-pair condition. Indeed, the two
2-gap starts differ by `R+2`, and all four endpoints lie in an interval of
length `R+4<2p`, which contains at most one filter shot. The graph formulation
explains the same certificate as an obstruction to simultaneous deletion.

## Exact Bad-Separator Frequency

Let `C_p(R)` count focused separators of value `R` in a fixed population and
define the three channel counts

```math
A_j
=
\sum_{\substack{R\\p\mid R+j}}C_p(R),
\qquad
j\in\{0,2,4\}.
```

The channels are disjoint for `p>=5`, because membership in two channels
would make `p` divide one of `2` or `4`. Therefore the exact bad count is

```math
\boxed{B_p=A_0+A_2+A_4.}
```

Consecutive post-filter-3 2-gap starts are both `5 modulo 6`. Their start
separation is `R+2`, so

```math
R\equiv4\pmod6.
```

Combining this phase with divisibility by `p` turns the three channels into
explicit progressions modulo `6p`. If `p` is `1 modulo 6`, then

```math
\begin{aligned}
p\mid R+4&\Longleftrightarrow R=2p-4+6pk,\\
p\mid R&\Longleftrightarrow R=4p+6pk,\\
p\mid R+2&\Longleftrightarrow R=6p-2+6pk,
\end{aligned}
\qquad k\ge0.
```

If `p` is `5 modulo 6`, then

```math
\begin{aligned}
p\mid R&\Longleftrightarrow R=2p+6pk,\\
p\mid R+4&\Longleftrightarrow R=4p-4+6pk,\\
p\mid R+2&\Longleftrightarrow R=6p-2+6pk,
\end{aligned}
\qquad k\ge0.
```

These formulas calculate the frequency exactly from the run-value histogram.
They also give weighted deterministic bounds. Writing

```math
T_R=\sum_R R C_p(R),
```

one has, for `p` equal to `1 modulo 6`,

```math
(2p-4)A_4+4pA_0+(6p-2)A_2\le T_R,
```

and, for `p` equal to `5 modulo 6`,

```math
2pA_0+(4p-4)A_4+(6p-2)A_2\le T_R.
```

If `N=sum_R C_p(R)`, both cases imply the universal frequency bound

```math
\boxed{
\frac{B_p}{N}
\le
\frac{T_R/N}{2p-4}
=
\frac{\operatorname{average}(R)}{2p-4}.
}
```

For the complete pre-filter period, the classical Mertens product estimate
applied to the exact ratio below gives

```math
\operatorname{average}(R)
=
\frac PN-2
=O(\log^2p).
```

Consequently

```math
\boxed{
\frac{B_p}{N}
=O\left(\frac{\log^2p}{p}\right)
\longrightarrow0.
}
```

This is a deterministic complete-period rarity theorem; no random residue
model is used. The Mertens asymptotic is an external classical dependency.
The conclusion does not prevent a short head-relative block from being
concentrated entirely among the globally rare bad separators.

## Complete-Period Good Separator

Let `P` be the complete period immediately before installing prime `p>=5`, and
let `N` be its exact number of 2-gaps. The focused alternation law gives `N`
run-cells whose total is `P-2N`, so their average is

```math
\frac{P-2N}{N}=\frac PN-2.
```

The exact global 2-gap count gives

```math
\frac PN
=
6\prod_{\substack{r\text{ prime}\\5\le r<p}}
\frac r{r-2}.
```

Every factor is greater than one, and the primes form a subset of all odd
integers from `5` through `p-2`. Therefore

```math
\begin{aligned}
\frac PN
&\le
6\prod_{\substack{5\le m\le p-2\\m\text{ odd}}}
\frac m{m-2}\\
&=
6\frac{p-2}{3}\\
&=2p-4.
\end{aligned}
```

The average focused run consequently satisfies

```math
\frac PN-2\le2p-6<2p-4.
```

At least one focused run is no larger than the average, so every complete
pre-filter period contains a separator `R<2p-4`. Hence

```math
\boxed{
\text{every complete pre-filter period contains a good separator and a
protected adjacent pair.}
}
```

This complete-period statement is unconditional. Its limitation is
positional: the protected pair may occur anywhere in a primorial-scale period,
far outside the head-relative square window.

## Finite Window Measurement

A read-only pass over `data/sieve-sequence/first_gaps_per_seq.csv` reconstructed
the 2-focused separators between consecutive pre-filter 2-gaps lying wholly
inside each stored immediate square window.

Across 186 complete windows with incoming prime `5<=p<=1123`:

- the windows contained 646,492 internal focused separators in total;
- 2,080 had `R>=p`, while only 159 reached `R>=2p-4`;
- the exact channel totals were `(A_0,A_2,A_4)=(12,0,16)`;
- 28 of the 159 separators in the possible bad range were actually bad;
- no window had every internal separator bad;
- the median bad-separator fraction was `0`;
- the maximum bad fraction was `0.6`, at `p=7`;
- the maximum consecutive bad-separator run was `2`;
- only 16 windows contained any bad separator; and
- no measured window after `p=463` contained a bad separator.

The zero observed `A_2` count is a scale effect, not an identity: that channel
starts only at `R=6p-2`, and exact complete-period enumeration already finds
86 such separators at incoming `p=23`.

These observations strongly reinforce the adjacency mechanism at finite
scale. They do not prove that every future conditioned square window contains
a good separator.

## Exact Remaining Obligation

The desired local theorem is now concrete:

> Through every required conditioned layer for infinitely many future heads,
> the relevant square-window focused block contains a separator `R` for which
> `p` divides none of `R`, `R+2`, and `R+4`.

One such separator forces a surviving 2-gap at that layer. Candidate #14 and
the redundant close-pair candidate give existing hereditary and quantitative
forms of this obligation. The complete-period average proves the corresponding
global statement but cannot localize its witness.

## Related

- [Two-Focused Compression Alternation Law](
  two-focused-alternation-law.md)
- [Two-Gap Pair Local Factor By Separation](
  two-gap-pair-local-factor-by-separation.md)
- [A Local Count Forces the k=2 Shot-Capacity Premise](
  local-count-forces-k2-shot-capacity.md)
- [Local Density Forces a Close-Pair Matching Bound](
  local-density-forces-close-pair-matching.md)
- [Hereditary Shot-Spacing Capacity](
  ../../candidates/hereditary-shot-spacing-capacity.md)
- [Redundant Close-Pair Capacity](
  ../../candidates/redundant-close-pair-capacity.md)
