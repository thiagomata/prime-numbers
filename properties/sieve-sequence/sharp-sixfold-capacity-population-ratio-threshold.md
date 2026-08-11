# Sharp Sixfold-Capacity Population-Ratio Threshold

**Status:** Mathematically proved conditional local-population theorem.
Stainless verification is not claimed.

## Meaning

The Sixfold-Capacity Energy Envelope property gives an exact but three-point capacity criterion for the harmful
scalar energy. This property solves that criterion in scale-free form.

Let `B` be the common one-class capacity and `G` the local 2-gap population.
The harmful scalar ellipse is certified exactly when `G/B` exceeds an
explicit threshold. That threshold is strictly larger than `2`, approaches
`2` as the incoming prime grows, and is always below `3`.

Thus one layer's harmful scalar ellipse requires only a quantified
strengthening of the ordinary two-class survival condition `G>2B`. The
remaining one-layer challenge is proving that population ratio for the actual
conditioned population.

The One-Layer Ellipse Non-Composition property shows that satisfying this comparison at every layer does not
by itself prove candidate #21's smaller global weighted allowance. A
separate aggregate theorem is still required.

## Setup

Let `r>=5` be prime. Assume a residue histogram with total population `G>0`
and common class capacity `B>0`:

```math
\sum_{a\bmod r}c_a=G,
\qquad
0\le c_a\le B.
```

Define the scale-free population ratio

```math
\rho=\frac GB.
```

Necessarily `0<rho<=r`.

The Sixfold-Capacity Energy Envelope property gives the sharp harmful scalar energy by maximizing

```math
F(s)
=
\frac{r}{2(r-2)}
\left(
s-\frac{2G}{r}
\right)^2
+
\frac12\min(s,2B-s)^2
```

over

```math
s\in\{\ell,u\}
\cup
\left(
\{B\}\text{ if }\ell\le B\le u
\right),
```

where

```math
\ell=\max(0,G-(r-2)B),
\qquad
u=\min(G,2B).
```

The candidate #21 one-layer scalar allowance is

```math
\frac12
\left(
G\left(1-\frac2r\right)
\right)^2.
```

## The Threshold

Define

```math
\boxed{
\rho_*(r)
=
\frac{
2r\sqrt r
}{
2\sqrt r+(r-2)^{3/2}
}.
}
```

Then the sharp capacity envelope lies strictly inside the scalar ellipse if
and only if

```math
\boxed{
\rho>\rho_*(r).
}
```

Equivalently,

```math
\boxed{
G>\rho_*(r)B.
}
```

## Decisive Filled-Harmful Branch

For `rho>=2`, the upper feasible harmful total is

```math
u=2B.
```

This is the histogram corner

```math
c_0=c_{-2}=B.
```

Its imbalance is zero, and its harmful excess is

```math
b
=
2B-\frac{2G}{r}
=
2B\left(1-\frac{\rho}{r}\right).
```

The scalar energy is

```math
\frac{2r}{r-2}
B^2
\left(
1-\frac{\rho}{r}
\right)^2.
```

The allowance is

```math
\frac{B^2}{2}
\left(
\rho\frac{r-2}{r}
\right)^2.
```

The strict energy inequality is equivalent to

```math
4r(r-\rho)^2
<
\rho^2(r-2)^3.
```

All quantities are nonnegative for `rho<=r`, so taking square roots gives

```math
2\sqrt r(r-\rho)
<
\rho(r-2)^{3/2}.
```

Solving for `rho` gives exactly

```math
\rho>\rho_*(r).
```

## Why The Other Branches Do Not Raise The Threshold

If `rho<=2`, the capacity polytope permits `s=G`: every start can lie in a
harmful class. Then

```math
b=G\left(1-\frac2r\right),
```

and its `r/(2(r-2))` coefficient is larger than `1/2`. The scalar allowance
therefore fails. Hence any successful ratio must exceed `2`.

For `rho>=2`, the other the Sixfold-Capacity Energy Envelope property branches are:

1. `s=0` while `rho<=r-2`;
2. `s=B` while `rho<=r-1`;
3. `s=G-(r-2)B` while `rho>=r-2`.

For `s=0`, direct cancellation of `rho^2` reduces the desired inequality to

```math
4r<(r-2)^3,
```

which holds for every `r>=5`.

For `s=B`, after clearing positive denominators the difference between the
allowance and the branch energy is

```math
\left((r-2)^3-4r\right)\rho^2
+
4r^2\rho
-
2r^2(r-1).
```

Its leading coefficient is positive for `r>=5`, it is increasing for
`rho>=0`, and its value at `rho=2` is positive. Thus this branch fits for
every `rho>=2`.

For the lower endpoint at `rho>=r-2`, put

```math
t=\rho-r+2,
\qquad
0\le t\le2.
```

On `0<=t<=1`, the cleared difference is a concave quadratic in `t`, so its
minimum occurs at an endpoint; both endpoint values are positive for
`r>=5`. On `1<=t<=2`, the allowance term increases while the branch's
distance terms decrease, and positivity at `t=1` proves the whole interval.

Consequently, no branch other than `s=2B` raises the threshold.

## Comparison With Ordinary Survival

The usual two-class capacity argument needs only

```math
G>2B.
```

The scalar collision budget needs

```math
G>\rho_*(r)B.
```

The threshold is strictly above `2`. Indeed,

```math
\frac{\rho_*(r)}2
=
\frac{r}{
2+(r-2)\sqrt{(r-2)/r}
}
>1,
```

because `sqrt((r-2)/r)<1`.

It is below `3` for every `r>=5`; clearing the positive radicals reduces this
to an elementary inequality, with the smallest case `r=5` already strict and
the gap increasing thereafter.

Finally,

```math
\boxed{
\lim_{r\to\infty}\rho_*(r)=2.
}
```

This follows by dividing numerator and denominator by `r^(3/2)`:

```math
\rho_*(r)
=
\frac{2}{
2/r+(1-2/r)^{3/2}
}
\longrightarrow2.
```

## Boundary

This is a sharp conditional theorem for the harmful scalar terms. It does not
prove

```math
G>\rho_*(r)B
```

for the actual conditioned square-window population.

The new threshold makes that remaining theorem precise. It is only a
constant-factor strengthening of `G>2B`, but near late layers both are
order-`Q` local-abundance statements. Proving the ratio throughout a future
chain may still encounter the same parity boundary as candidates #14 and
#19.

The theorem also controls only the harmful scalar energy. Candidate #22's
harmless-class dispersion remains an independent component of #21.

It is a one-layer comparison, not a cumulative composition theorem; see
The One-Layer Ellipse Non-Composition property.

## Validation

The threshold and active branch were checked against the Sixfold-Capacity Energy Envelope property's exact
three-point maximum for

```math
r\in\{5,7,11,17,29,53,97,211\}.
```

The computed thresholds decrease from approximately `2.312786` at `r=5`
toward `2`. Dense rational samples on both sides of each threshold agreed
with the strict algebraic criterion. These checks validate branch selection
only; the proof is the symbolic comparison above.

## Related

- [Sharp sixfold-capacity harmful-energy envelope](
  sharp-sixfold-capacity-harmful-energy-envelope.md
  )
- [Harmful residue capacity after filter three](
  harmful-residue-capacity-after-filter-three.md
  )
- [Sharp harmful-residue box inside the collision ellipse](
  sharp-harmful-residue-box-inside-collision-ellipse.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
- [One-layer harmful ellipses do not compose](
  one-layer-harmful-ellipses-do-not-compose.md
  )
