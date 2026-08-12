# Pointwise Two-Class Margin Does Not Imply The Collision Budget

**Status:** Mathematically proved logical insufficiency result. Stainless
verification is not claimed.

## Meaning

Candidate #12's existing pointwise residue-deviation bound, together with its
strict one-step survival margin, does not imply candidate #21's stronger
quadratic scalar budget.

An exact integer residue histogram can put equal positive deviations in both
harmful classes. Their difference vanishes, but their sum is large enough to
exceed the collision allowance. The required replacement is therefore a
joint ellipse for the two harmful deviations, not merely a common
coordinatewise bound.

This does not claim that the constructed histogram is realized by every
actual sieve window.

## Integral Countermodel

Fix a prime

```math
r\ge5
```

and let the total 2-gap-start population be

```math
G=2r^2.
```

The uniform residue mean is

```math
\frac Gr=2r.
```

Put

```math
E=(r-2)(r-1).
```

Assign the two harmful residue counts

```math
c_0=c_{-2}=2r+E,
```

and assign

```math
c_a=2
```

to each of the other `r-2` residue classes.

The total count is

```math
\begin{aligned}
2(2r+E)+2(r-2)
&=
4r+2(r-2)(r-1)+2r-4\\
&=
2r^2\\
&=
G.
\end{aligned}
```

Thus this is an exact nonnegative integer residue histogram.

## Pointwise Bound

The harmful deviations are

```math
\delta_0=\delta_{-2}=E.
```

Every harmless deviation is

```math
2-2r=-2(r-1).
```

Since `r>=5`,

```math
2(r-1)\le(r-2)(r-1)=E.
```

Therefore the full pointwise candidate #12 hypothesis holds:

```math
\boxed{
\max_{a\bmod r}
\left|c_a-\frac Gr\right|
\le E.
}
```

## Survival Margin

Candidate #12's strict one-step margin for the word `(2)` is

```math
2E<G\left(1-\frac2r\right).
```

Here

```math
2E=2(r-2)(r-1),
```

while

```math
G\left(1-\frac2r\right)
=
2r(r-2).
```

Because `r-1<r`,

```math
\boxed{
2E<G\left(1-\frac2r\right).
}
```

Thus candidate #12's stated sufficient condition guarantees that some
2-gaps survive this one filter.

## Collision-Budget Failure

The Sampling-Density Recombination property gives

```math
b=\delta_0+\delta_{-2}=2E,
\qquad
\Delta=\delta_0-\delta_{-2}=0.
```

The one-layer scalar energy is therefore

```math
\begin{aligned}
\mathcal Q
&=
\frac{r}{2(r-2)}b^2+\frac12\Delta^2\\
&=
\frac{r}{2(r-2)}
\left(
2(r-2)(r-1)
\right)^2\\
&=
2r(r-2)(r-1)^2.
\end{aligned}
```

Let

```math
T=G\left(1-\frac2r\right)=2r(r-2).
```

Candidate #21's complete one-layer allowance is

```math
\frac{T^2}{2}
=
2r^2(r-2)^2.
```

Their ratio is

```math
\begin{aligned}
\frac{\mathcal Q}{T^2/2}
&=
\frac{(r-1)^2}{r(r-2)}\\
&=
1+\frac1{r(r-2)}\\
&>
1.
\end{aligned}
```

Hence

```math
\boxed{
\mathcal Q>\frac{T^2}{2}.
}
```

The scalar harmful-residue energy alone exceeds candidate #21's entire
one-layer allowance, even though candidate #12's pointwise survival margin is
strictly positive.

## Required Stronger Shape

The two statements serve different purposes:

- candidate #12's current margin prevents both harmful counts from covering
  the entire population;
- candidate #21 requires their centered sum and difference to lie inside the
  ellipse

  ```math
  \frac{r}{2(r-2)}
  (\delta_0+\delta_{-2})^2
  +
  \frac12(\delta_0-\delta_{-2})^2
  <
  \frac{T^2}{2}.
  ```

The ellipse is the correct direct scalar theorem shape. A coordinatewise box
strictly contained in the survival range can still protrude outside it along
the same-sign direction.

## Validation

The histogram totals, pointwise bounds, strict survival margin, and quadratic
violation were checked with exact integer arithmetic for every prime

```math
5\le r\le97.
```

These finite checks validate the construction only; the displayed algebra is
universal for every prime `r>=5`.

## Related

- [Endpoint sampling and strike density recombine into harmful residues](
  endpoint-sampling-strike-density-harmful-residue-bridge.md
  )
- [Local pattern-residue balance](
  ../../candidates/local-pattern-residue-balance.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
