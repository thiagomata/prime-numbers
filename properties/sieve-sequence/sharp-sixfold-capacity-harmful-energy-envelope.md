# Sharp Sixfold-Capacity Harmful-Energy Envelope

**Status:** Mathematically proved conditional local-capacity theorem.
Stainless verification is not claimed.

## Meaning

After filters `2` and `3`, every residue class modulo an incoming prime has
an explicit local capacity because 2-gap starts in that class are separated
by `6r`. This property composes that capacity with candidate #21's exact
two-harmful-class quadratic energy.

The result is the sharp energy envelope obtainable from the total start
population and the common one-class capacity. It reduces the extremal problem
to at most three possible harmful totals.

## Setup

Let `r>2`. Let a local window contain `G>0` complete 2-gap starts, with
residue counts

```math
c_a
\qquad(a\bmod r).
```

Assume every residue class satisfies the common capacity

```math
0\le c_a\le B.
```

For the square-safe window in the Close-Pair Matching Bound property,

```math
B
=
\left\lfloor
\frac{Q^2-Q-3}{6r}
\right\rfloor+1.
```

Necessarily

```math
G=\sum_{a\bmod r}c_a\le rB.
```

Define

```math
\mu=\frac Gr,
```

```math
\delta_0=c_0-\mu,
\qquad
\delta_{-2}=c_{-2}-\mu,
```

and

```math
\mathcal Q_r
=
\frac{r}{2(r-2)}
(\delta_0+\delta_{-2})^2
+
\frac12(\delta_0-\delta_{-2})^2.
```

## Exact Feasible Harmful Total

Put

```math
s=c_0+c_{-2},
\qquad
d=c_0-c_{-2}.
```

The two harmful classes can contain at most `2B` starts and no more than the
total population:

```math
s\le\min(G,2B).
```

The other `r-2` classes have total capacity `(r-2)B`, so

```math
G-s\le(r-2)B.
```

Therefore

```math
\boxed{
\ell\le s\le u,
}
```

where

```math
\ell=\max(0,G-(r-2)B),
\qquad
u=\min(G,2B).
```

For fixed `s`, the two constraints `0<=c_0,c_(-2)<=B` give

```math
\boxed{
|d|\le\min(s,2B-s).
}
```

All these integer bounds are attainable whenever `G<=rB`: the remaining
`G-s` starts can be distributed among the other `r-2` classes with capacity
`B`.

## Sharp Energy Maximum

In `(s,d)` coordinates,

```math
\mathcal Q_r
=
\frac{r}{2(r-2)}
\left(
s-\frac{2G}{r}
\right)^2
+
\frac12d^2.
```

For fixed `s`, the maximum uses

```math
|d|=\min(s,2B-s).
```

Define

```math
F_{r,G,B}(s)
=
\frac{r}{2(r-2)}
\left(
s-\frac{2G}{r}
\right)^2
+
\frac12\min(s,2B-s)^2.
```

This is convex on each side of `s=B`. Let

```math
\mathcal S
=
\{\ell,u\}
\cup
\left(
\{B\}\text{ if }\ell\le B\le u
\right).
```

Then

```math
\boxed{
\max_{\substack{\sum_ac_a=G\\0\le c_a\le B}}
\mathcal Q_r
=
\max_{s\in\mathcal S}F_{r,G,B}(s).
}
```

This is the sharp conclusion available from the common class capacity and
the total population.

## Exact One-Layer Criterion

Let

```math
T=G\left(1-\frac2r\right).
```

The capacity theorem alone certifies candidate #21's one-layer scalar ellipse
exactly when

```math
\boxed{
\max_{s\in\mathcal S}F_{r,G,B}(s)
<
\frac{T^2}{2}.
}
```

Unlike the symmetric box criterion in the Harmful-Residue Box Bound property, this condition retains
the asymmetric relation between the absolute class capacity `B` and the
uniform mean `G/r`.

It is explicit in `G`, `r`, and the window capacity. It can therefore be used
as a deterministic population threshold: for fixed `Q,r`, determine the
least integer `G<=rB` for which the inequality holds.

## Boundary

This property proves the sharp composition, not the required lower bound for
the actual conditioned population `G`.

If the criterion fails, no improvement is possible using only the facts
`sum c_a=G` and `c_a<=B`; an extremal integer histogram realizes the displayed
maximum. If it holds, the harmful scalar terms are controlled without
equidistribution, candidate #13, or candidate #23.

The remaining one-layer question is whether existing algebraic population
properties force the actual `G` above this explicit threshold at a given
layer. That question may return to the local-abundance/parity boundary.

Even a positive answer at every layer would not prove candidate #21's global
weighted budget. The One-Layer Ellipse Non-Composition property shows that the local ellipses do not compose.
The separate cumulative capacity target is a direct estimate for

```math
\sum_iw_iC_i,
```

where `C_i` is this property's realized sharp envelope at layer `i`.
The Terminal Harmful-Excess Energy property classifies the required scale precisely:

```math
\sum_iw_iC_i
<
\frac{T^2}{2W}
```

already forces a positive final population because the harmful-excess energy
`E_b` is bounded by the left side. Thus the cumulative capacity target is a
terminal conditioned-chain theorem, not an independently noncircular
component waiting to be combined with harmless dispersion.

## Validation

The formula was checked by exhaustive exact rational enumeration for

```math
r\in\{5,7,11\},
\qquad
1\le B\le8,
\qquad
1\le G\le rB.
```

For every parameter tuple, the maximum over all feasible integer harmful
counts equaled the displayed three-point formula. These finite checks
validate the extremal derivation only.

## Related

- [Harmful residue capacity after filter three](
  harmful-residue-capacity-after-filter-three.md
  )
- [Sharp harmful-residue box inside the collision ellipse](
  sharp-harmful-residue-box-inside-collision-ellipse.md
  )
- [Endpoint sampling and strike density recombine into harmful residues](
  endpoint-sampling-strike-density-harmful-residue-bridge.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
- [One-layer harmful ellipses do not compose](
  one-layer-harmful-ellipses-do-not-compose.md
  )
- [Weighted harmful-excess energy is already terminal](
  weighted-harmful-excess-energy-is-terminal.md
  )
