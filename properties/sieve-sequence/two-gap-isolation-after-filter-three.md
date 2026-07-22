# Isolation of 2-Gaps After Filtering by 3

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

Once both `2` and `3` are installed filters, one accepted value cannot be the
shared endpoint of two 2-gaps. This changes the sharp destruction capacity of
one later filter strike from two possible 2-gaps to one.

## Setup

Assume the current modulus `M` is divisible by `6`. A 2-gap is a pair
`(x,x+2)` whose endpoints are both coprime to `M`.

## Property

Two 2-gaps cannot overlap as

```math
(x,x+2)
\qquad\text{and}\qquad
(x+2,x+4).
```

Equivalently, every accepted value is an endpoint of at most one 2-gap.

## Proof

Among the three values

```math
x,\quad x+2,\quad x+4,
```

exactly one is divisible by `3`. Because `3` divides `M`, that value cannot be
accepted. Therefore all three values cannot simultaneously be endpoints of
two overlapping 2-gaps.

There is also a useful positional form. Since both endpoints must be coprime
to `2` and `3`, every 2-gap start satisfies

```math
x\equiv5\pmod 6.
```

Possible 2-gap starts are consequently separated by at least `6` in value.

## Consequence For Filtering

A filter removes individual accepted values. A destroyed 2-gap must contain
the removed value as an endpoint. Since no accepted value belongs to two
2-gaps, one removed value destroys at most one 2-gap.

Thus, after filter `3` is installed,

```math
\text{destroyed 2-gaps}
\le
\text{removed accepted values}.
```

## Limitation

Isolation limits destruction efficiency; it does not guarantee that any
2-gaps exist in a chosen interval. It is an upper-capacity theorem, not a
local-abundance theorem.
