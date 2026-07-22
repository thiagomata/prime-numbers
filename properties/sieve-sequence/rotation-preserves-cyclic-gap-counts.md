# Rotation Preserves Cyclic Gap Counts

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

Rotation changes which accepted value is used as the origin of a cyclic gap
sequence. It does not filter values, merge gaps, or change the global number
of gaps of any size.

## Setup

Let

```math
G=(g_0,g_1,\ldots,g_{T-1})
```

be a cyclic gap list. For an offset `j`, its rotation is

```math
\operatorname{rot}_j(G)
=(g_j,g_{j+1},\ldots,g_{T-1},g_0,\ldots,g_{j-1}).
```

## Property

For every gap value `d`, rotation preserves its multiplicity:

```math
\#\{i:g_i=d\}
=
\#\{i:\operatorname{rot}_j(G)_i=d\}.
```

In particular, rotation preserves the global cyclic 2-gap count exactly.

## Proof

Rotation is a bijection on the index set `{0,1,...,T-1}`. It permutes the
existing entries without changing any entry's value. Counting entries equal to
`d` before and after the permutation therefore gives the same result.

## What Rotation Can Change

Rotation can change:

- which accepted value is represented at index zero;
- whether a particular cyclic gap appears internally or across the displayed
  end-to-start boundary of a linearized list;
- whether the gap immediately following the chosen head has value `2`.

These are origin or presentation effects. They are not destruction.

## Local-Window Boundary

A coordinate window such as `[q,q^2)` is not defined only by cyclic indices;
it is tied to absolute values. Global rotation invariance therefore does not
imply that a fixed absolute window receives the same number of 2-gaps after a
transition. Filtering changes the accepted set before rotation, and the new
origin only describes the resulting cycle.

## Limitation

Rotation provides no equidistribution theorem for 2-gap positions. Treating a
rotation as a random reshuffle, or as evidence that every short slice receives
its proportional share of gaps, adds an assumption not contained in the
operation itself.
