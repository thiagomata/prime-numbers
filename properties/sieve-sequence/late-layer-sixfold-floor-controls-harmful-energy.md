# Late-Layer Sixfold Floor Controls Harmful Energy

**Status:** Mathematically proved conditional layer-range theorem.
Stainless verification is not claimed.

## Meaning

Candidate #19's population floor is designed only to leave one 2-gap after
the two harmful residue classes are removed. Property #62 needs a slightly
larger population-to-capacity ratio to control the full harmful quadratic
energy.

Property #63 gives the exact comparison cutoff. This property translates that
cutoff into a simple layer condition: in the late part of a future square
window, candidate #19's ordinary survival floor is already strong enough for
that layer's harmful scalar ellipse. No additional residue equidistribution
is needed for this one-layer comparison.

## Setup

Let `Q>=7`, let `r` be an odd prime with `5<=r<Q`, and define

```math
L=Q^2-Q-3,
\qquad
B=\left\lfloor\frac{L}{6r}\right\rfloor+1.
```

Property #62's sharp population ratio is

```math
\rho_*(r)
=
\frac{2r\sqrt r}{2\sqrt r+(r-2)^{3/2}}.
```

Property #63 proves that candidate #19's floor

```math
G\ge2B+1
```

guarantees `G>rho_*(r)B` exactly when

```math
B<\kappa(r),
\qquad
\kappa(r)=\frac1{\rho_*(r)-2}.
```

## A Uniform Lower Bound For The Cutoff

For every `r>=5`,

```math
\boxed{
\kappa(r)>\frac r2.
}
```

To prove this, write

```math
\rho_*(r)
=
\frac{2}{
2/r+(1-2/r)^{3/2}
}.
```

For `0<x<1`, Taylor's formula with integral remainder gives

```math
(1-x)^{3/2}
>
1-\frac32x+\frac38x^2.
```

Indeed, the second derivative is

```math
\frac34(1-x)^{-1/2}>\frac34
```

away from the initial endpoint. Substituting `x=2/r` yields

```math
\begin{aligned}
\frac2r+\left(1-\frac2r\right)^{3/2}
&>
1-\frac1r+\frac{3}{2r^2}\\
&>
\frac{r}{r+1}.
\end{aligned}
```

The last strict difference is

```math
\frac{r+3}{2r^2(r+1)}>0.
```

Taking reciprocals of positive quantities gives

```math
\rho_*(r)
<
\frac{2(r+1)}r
=
2+\frac2r.
```

Therefore

```math
\rho_*(r)-2<\frac2r,
```

and hence

```math
\kappa(r)
=
\frac1{\rho_*(r)-2}
>
\frac r2.
```

## The Late-Layer Range

Assume

```math
\boxed{
L<3r(r-1).
}
```

Then

```math
\frac{L}{6r}<\frac{r-1}{2}.
```

Because `(r-1)/2` is an integer,

```math
\left\lfloor\frac{L}{6r}\right\rfloor
\le
\frac{r-3}{2}.
```

Consequently,

```math
B\le\frac{r-1}{2}<\frac r2<\kappa(r).
```

Property #63 now gives

```math
2B+1>\rho_*(r)B.
```

Thus the conditional implication is

```math
\boxed{
\left[
L<3r(r-1)
\ \text{and}\
G\ge2B+1
\right]
\Longrightarrow
G>\rho_*(r)B.
}
```

By property #62, the sharp sixfold-capacity envelope for the two harmful
classes then lies strictly inside candidate #21's one-layer harmful scalar
allowance.

## Explicit Position In The Chain

The layer condition is equivalent to

```math
r>
\frac{
1+\sqrt{1+\frac43(Q^2-Q-3)}
}{2}.
```

A simpler sufficient condition is

```math
r\ge\frac{Q}{\sqrt3}+1.
```

Indeed, that inequality gives

```math
3r(r-1)
\ge
Q^2+\sqrt3Q
>
Q^2-Q-3=L.
```

Therefore candidate #19's ordinary floor, if proved, controls the harmful
scalar energy against its local allowance throughout this explicit
late-layer range.

## What Remains In The Early Layers

When

```math
L\ge3r(r-1),
```

this sufficient comparison no longer applies. The exact test remains

```math
B<\kappa(r).
```

Failure of the simple late-layer condition does not imply failure of that
exact test, and failure of the exact test means only that candidate #19's
minimum floor is insufficient. The actual conditioned population may be
larger.

The theorem therefore separates the scalar problem:

- late layers need no stronger one-layer population premise than candidate
  #19;
- early and middle layers still need either surplus above candidate #19's
  floor or a direct harmful-residue energy estimate.

It does not prove candidate #19's hereditary floor at any layer.

It also does not allocate the late-layer energies inside candidate #21's
global weighted allowance. Property #65 proves that local ellipse membership
does not compose; a direct estimate for `sum_i w_i Q_i` remains separate.
Property #66 proves that success at the required global scale is already a
terminal survival theorem, not an independently noncircular component.

## Validation

The inequalities were checked for every prime pair

```math
7\le Q\le1009,
\qquad
5\le r<Q,
```

and for the integer boundaries immediately below and above
`L=3r(r-1)`. Every layer satisfying the displayed late condition also
satisfied `B<kappa(r)` and `2B+1>rho_*(r)B`.

These checks validate the boundary arithmetic only; the proof is the
inequality chain above.

## Related

- [Capacity population-threshold hierarchy](
  capacity-population-threshold-hierarchy.md
  )
- [Sharp sixfold-capacity population-ratio threshold](
  sharp-sixfold-capacity-population-ratio-threshold.md
  )
- [Sixfold harmful-residue capacity](
  ../../candidates/sixfold-harmful-residue-capacity.md
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
