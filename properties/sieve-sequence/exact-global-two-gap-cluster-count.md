# Exact Global Count of `(2,4,2)` Two-Gap Clusters

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

Once filters `2` and `3` are installed, consider the cyclic gap word
`(2,4,2)`. It contains two endpoint-disjoint 2-gaps in an enclosing span of
`8`. Repetition and filtering give an exact recurrence for the number of these
clusters in a complete period: installing a new prime `r>=5` multiplies their
count by `r-4`.

Thus the absolute cluster population grows at every stage after filter `5`,
even though its proportion among all accepted positions may decrease.

## Setup

Let the current modulus `M` be divisible by `6`. Count cyclic occurrences of

```math
(2,4,2)
```

in the complete accepted gap cycle, and call that count `C_M`. Equivalently,
an occurrence starting at `a` consists of four consecutive accepted values

```math
a,\quad a+2,\quad a+6,\quad a+8.
```

Let `r>=5` be a new prime not dividing `M`.

## Exact One-Filter Recurrence

The expanded cycle contains `r` copies of every old cluster:

```math
a+jM+\{0,2,6,8\},
\qquad
0\le j<r.
```

Exactly four copies are struck at one of their four endpoints, and the other
`r-4` copies survive intact. No new `(2,4,2)` occurrence can be created by
filtering. Therefore

```math
C_{rM}=(r-4)C_M.
```

## Proof

Because `gcd(M,r)=1`, each endpoint offset `h in {0,2,6,8}` has one forbidden
copy-index class:

```math
j\equiv-(a+h)M^{-1}\pmod r.
```

The four classes are distinct. Equality of two classes would imply that `r`
divides a nonzero difference between two offsets. Those differences are

```math
2,\quad4,\quad6,\quad8,
```

and no prime `r>=5` divides any applicable endpoint difference: `5` and `7`
divide none of them, while every prime `r>=11` exceeds them. Hence exactly
four of the `r` copies lose an endpoint and exactly `r-4` retain the complete
word.

It remains to show that the filtering step cannot create additional
occurrences. After filter `2`, all accepted gaps are positive and even. A new
gap is either one copied old gap or a sum of at least two consecutive old
gaps.

- A merged gap cannot equal `2`, because the sum of two positive even gaps is
  at least `4`.
- A merged gap can equal `4` only as `2+2`. But consecutive 2-gaps would
  require three accepted values `x,x+2,x+4`, one of which is divisible by
  `3`. This is impossible because filter `3` is installed.

Thus every new gap of size `2` or `4` is a copied old gap. Every new
`(2,4,2)` word is consequently an intact copy of an old `(2,4,2)` word. There
are no created occurrences to add to the `r-4` surviving copies, so

```math
C_{rM}=(r-4)C_M
\quad\text{[Q.E.D.]}.
```

## Closed Product

For the wheel with installed filters `{2,3}`, the accepted residues are
`1` and `5` modulo `6`. Its cyclic gap word contains exactly one
`(2,4,2)` occurrence, so `C_6=1`.

For any finite installed-prime set `P` containing `{2,3}`,

```math
C(P)
=
\prod_{\substack{p\in P\\p\ge5}}(p-4).
```

The first factors are

```math
1,\quad3,\quad7,\quad9,\quad13,\ldots
```

for installed primes `5,7,11,13,17,...`. Hence `C(P)` is positive at every
stage and strictly increases whenever a prime greater than `5` is installed.

The total accepted population multiplies by `r-1`, whereas the cluster count
multiplies by `r-4`. Therefore the cluster proportion is multiplied by

```math
\frac{r-4}{r-1}<1.
```

The absolute count grows while the relative density decreases.

## Limitation

This is an exact complete-cycle theorem. It does not bound the number of
clusters inside a particular short interval such as `[q,q^2)`, nor does it
bound the maximum distance between consecutive clusters.

Lifting a short interval through every repeated copy gives exact aggregate
survival, but all surviving copies may still lie outside one designated
component. A local conclusion requires an additional placement, exterior
capacity, or copy-index selection theorem.

## Related

- [Exact global two-gap count](exact-global-two-gap-count.md) — the analogous
  recurrence with factor `r-2` for individual 2-gaps.
- [Exact filter frequency across repeated copies](
  copy-index-filter-frequency.md
  ) — supplies the forbidden copy-index classes.
- [Isolation of 2-gaps after filtering by 3](
  two-gap-isolation-after-filter-three.md
  ) — excludes consecutive 2-gaps and hence creation of a merged 4-gap.
- [Fixed-k shot spacing](stable-small-k-shot-spacing.md) — proves that a
  length-8 cluster exists in every sufficiently developed complete wheel.
