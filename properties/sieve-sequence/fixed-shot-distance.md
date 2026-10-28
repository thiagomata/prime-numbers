# Fixed Shot Distance For 2-Gap Copies

**Status:** Stainless verified.

## Meaning

A real 2-gap does not give the incoming prime two arbitrary harmful copy
indices. Once the right endpoint's harmful lift offset is known, the left
endpoint's harmful lift offset is forced by a fixed modular displacement that
depends only on the old period and the incoming prime, not on the particular
2-gap.

This is the arithmetic reason a rigid-pair companion should draw a translate
of one fixed pair, rather than a uniformly random two-element subset.

## Object Geometry

The two harmful lift indices are not independent choices. They are attached
to the two endpoints of one copied 2-gap object. A copy can lose its left
endpoint, or it can lose its right endpoint, but those endpoint tests belong
to the same rigid gap whose internal length is `2`.

Once the copy index that deletes the right endpoint is fixed, the copy index
that deletes the left endpoint is therefore forced by the unique lift
displacement whose old-period step contributes exactly `2` modulo the incoming
head. The modular formula below is the coordinate expression of this object
geometry: the object structure couples the two shots before any probabilistic
model is introduced.

## Setup

Let `M` be the old period and let `p > 2` be the incoming head prime with
`mod(M,p) != 0`. Let an old real 2-gap have endpoints

```math
a,\quad a+2.
```

For each endpoint, define the forbidden lift offset as the unique copy index
in `[0,p)` that makes the lifted endpoint divisible by `p`:

```math
\begin{aligned}
k_L &: \quad a + k_L M \equiv 0 \pmod p,\\
k_R &: \quad a+2 + k_R M \equiv 0 \pmod p.
\end{aligned}
```

Let `d` be the canonical inverse-step offset for the residue `2`:

```math
dM \equiv 2 \pmod p,\qquad 0 \le d < p.
```

Equivalently, `d == 2*M^{-1} mod p`.

## Property

The left forbidden lift offset is the fixed translate of the right forbidden
lift offset:

```math
\begin{aligned}
k_L &\equiv k_R + d \pmod p,\\
dM &\equiv 2 \pmod p.
\end{aligned}
```

Thus the unordered harmful pair is always a translate of the fixed pair
`{0,d}` in `Z/pZ`.

## Proof

The right endpoint condition gives

```math
a + 2 + k_R M \equiv 0 \pmod p.
```

Adding the fixed separation relation `dM == 2 mod p` gives

```math
a + 2 + k_R M + dM \equiv 2 \pmod p.
```

Subtracting `2` leaves

```math
a + (k_R+d)M \equiv 0 \pmod p.
```

So `k_R+d` is a zero-making lift offset for the left endpoint. The left
endpoint has a unique zero-making lift offset in `[0,p)`, so reducing
`k_R+d` modulo `p` gives exactly `k_L`. `[Q.E.D.]`

## Verification

The property is verified in
[`SpecSieveSeqTwoGapProperties::assertRightForbiddenLiftOffsetHasFixedSeparation`](../../src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala).

The verified statement uses the repository's canonical offset witness:

```scala
val fixedSeparation =
  BezoutUtils.coprimeStepResidueOffset(step, p, BigInt(2))
val shiftedRightOffset =
  Calc.mod(rightOffset + fixedSeparation, p)

leftOffset == shiftedRightOffset
```

Focused verification:

```text
just verify assertRightForbiddenLiftOffsetHasFixedSeparation
total: 98 valid: 98
```

Chapter regression:

```text
just verify-ch 6
total: 4691 valid: 4691
```

## Boundary

This property fixes the local pair geometry for one incoming prime and one
old 2-gap. It does not by itself compute short-block hit probabilities,
circular boundary corrections, or empirical hit rates. Those are separate
modeling steps built on this fixed-distance fact.
