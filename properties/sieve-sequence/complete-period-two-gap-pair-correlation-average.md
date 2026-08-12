# Complete-Period Two-Gap Pair-Correlation Average

**Status:** Mathematically proved (complete-period theorem). Stainless
verification is not claimed here.

## Meaning

After filters `2` and `3`, every 2-gap start has the fixed phase
`5 modulo 6`. Removing that phase gives a cyclic set of start indices. The
autocorrelation of any finite cyclic set has an exact mean: summing over every
difference counts every ordered pair exactly once.

For a new prime, multiplying all differences by that prime merely permutes the
complete difference period. Thus collision separations have exactly the same
complete-period average as arbitrary separations.

## Quotient Encoding

Let `P` be a finite set of installed primes containing `2` and `3`, and write

```math
M=\prod_{p\in P}p=6M',
\qquad
M'=\prod_{\substack{p\in P\\p\ge5}}p.
```

Let `S` be the cyclic 2-gap starts modulo `M`. Every `x in S` satisfies

```math
x\equiv5\pmod6.
```

Therefore it has a unique representation

```math
x\equiv5+6u\pmod M
```

with `u modulo M'`. Define the quotient start set

```math
U
=
\{u\pmod{M'}:5+6u\in S\}.
```

The map `u -> 5+6u` is a bijection between `U` and `S`. Hence

```math
G:=|U|=|S|
=
\prod_{\substack{p\in P\\p\ge5}}(p-2).
```

## Cyclic Pair Correlation

For `h modulo M'`, define

```math
A(h)
=
\#\{u\in U:u+h\in U\},
```

where addition is cyclic modulo `M'`.

The value `A(h)` counts ordered pairs of cyclic 2-gap starts separated by

```math
6h\pmod M.
```

## Exact Complete-Period Average

Every ordered pair `(u,v) in U^2` has a unique cyclic difference

```math
h=v-u\pmod{M'}.
```

Conversely, every term counted by `A(h)` is one such ordered pair. Therefore

```math
\boxed{
\sum_{h\bmod M'}A(h)=G^2.
}
```

The exact mean is

```math
\boxed{
\frac1{M'}
\sum_{h\bmod M'}A(h)
=
\frac{G^2}{M'}.
}
\qquad[\text{Q.E.D.}]
```

## Multiplication By A New Prime

Let `r` be a prime not in `P`. Then

```math
\gcd(r,M')=1,
```

so multiplication by `r` permutes the residue classes modulo `M'`. Hence

```math
\boxed{
\sum_{h\bmod M'}A(rh)
=
\sum_{h\bmod M'}A(h)
=
G^2.
}
```

Thus separations divisible by the new prime have exactly the uniform
correlation mean when `h` ranges through one complete quotient period.

## Prefix Decomposition

For an integer `H>=0`, write

```math
H=qM'+s,
\qquad
0\le s<M'.
```

Periodicity and the complete-period theorem give

```math
\sum_{h=1}^{H}A(rh)
=
qG^2
+
\sum_{h=1}^{s}A(rh).
```

Define the prefix discrepancy

```math
\mathcal E(H;r)
=
\sum_{h=1}^{H}A(rh)
-
\frac{H}{M'}G^2.
```

Then the complete blocks cancel exactly:

```math
\boxed{
\mathcal E(H;r)
=
\sum_{h=1}^{s}A(rh)
-
\frac{s}{M'}G^2.
}
```

Because `0<=A(h)<=G`, the immediate bound is

```math
\boxed{
|\mathcal E(H;r)|\le sG.
}
```

This bound is exact in scale for an arbitrary cyclic set but is generally too
large for candidate #21.

## Relation To The Four-Point Product

The correlation `A(h)` counts translations of the two-gap pair with endpoint
offsets

```math
\{0,2,6h,6h+2\}.
```

The [two-gap pair local-factor theorem](
two-gap-pair-local-factor-by-separation.md
) computes the same complete-period count as a CRT product. The identity

```math
\sum_{h\bmod M'}A(h)=G^2
```

therefore also gives an exact complete-period average of those local-factor
products.

## Limitation

When the relevant separation range satisfies `H<M'`, there is no complete
block and

```math
s=H.
```

Then complete-period averaging alone gives no cancellation beyond the trivial
bound `|E(H;r)|<=HG`. This is precisely the late-layer regime where the
primorial quotient is much larger than the square-window separation range.

A useful proof needs additional control of the correlation prefix, for example
through its Fourier spectrum, a short-range singular-series average, or
another structural property of the CRT product set `U`.

## Related

- [Two-gap pair local factor by separation](
  two-gap-pair-local-factor-by-separation.md
  )
- [Weighted collision-energy chain survival](
  weighted-collision-energy-chain-survival.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
