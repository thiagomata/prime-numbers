# Two-Focused Compression Alternation Law

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

The 2-focused compression (used by the gap-heatmap views: every 2-gap
keeps its own cell, each maximal run of consecutive non-2 gaps collapses
to one cell equal to its sum) has an exact structural law: post-3, its
cells strictly alternate between 2-cells and run-cells around the cycle,
so **exactly half of the compressed cells are 2-gaps at every stage** —
not approximately, not asymptotically, provably and permanently.

This makes the compressed representation the natural coordinate system
for invariant design: 2-gap *presence* is structurally perpetual there,
and the Mertens density decay — which forbids any absolute-density
component in a dream invariant — relocates entirely into the run values.
Everything open about spacing concentrates into one observable: the run
sums.

## Setup

A post-3 stage has installed filter 3. Let its gap cycle contain `N`
2-gaps. Define the 2-focused compression: collapse each maximal cyclic
run of consecutive non-2 gaps into a single cell equal to its sum; keep
each 2-gap as a cell.

## No Adjacent 2-Gaps

Suppose the raw cycle contained adjacent 2-gaps: survivors

```math
v,\quad v+2,\quad v+4.
```

Their residues mod 3 are `v, v+2, v+4`, which are pairwise distinct, so
one of the three values is `0 mod 3` and was removed by filter 3 — a
contradiction. Hence no two 2-gaps are adjacent in any post-3 gap cycle.
`[Q.E.D.]`

(The same mod-3 fact underlies candidate #2's one-strike-one-gap step
and the no-creation argument of the 2-gap placement saturation
property.)

## Alternation And The Exact Share

By non-adjacency, every maximal cyclic run of non-2 gaps between two
consecutive 2-gaps is nonempty. Walking the cycle therefore visits

```math
2\text{-cell},\ \text{run-cell},\ 2\text{-cell},\ \text{run-cell},\ \ldots
```

in strict alternation, so the two cell classes have equal counts:

```math
\boxed{
\#2\text{-cells}=\#\text{run-cells}=N,
\qquad
\frac{\#2\text{-cells}}{\#\text{cells}}=\frac12
}
\qquad[\text{Q.E.D.}]
```

at every post-3 stage, independent of the stage, the filter depth, and
the placement history.

## Where The Decay Lives

The sum of all gaps is the period `Pi`, of which the 2-cells carry `2N`.
The run cells therefore carry `Pi - 2N`, and the average run value is

```math
\frac{\Pi-2N}{N}=\frac1{d}-2,
\qquad d=\frac{N}{\Pi},
```

the reciprocal density. The Mertens decay `d ~ C/log^2 Q` never makes
2-cells scarcer — they stay at exactly half — it lengthens the runs:
average run `~ (1/C) log^2 Q`. In compressed coordinates, spacing
control and density control are the same statement about run sums.

## Role

- [Dream sequence self-propagating invariant](
  ../../candidates/dream-sequence-self-propagating-invariant.md) — the
  alternation law is its Component 0: a perpetual, scale-free presence
  structure requiring no lemma. The open local content (Lemma A′)
  becomes pure run-value control: a window fails exactly when a run sum
  exceeds it.
- The gap-heatmap views (`python/src/sieve_sequence/gap_heatmap.py`) are
  already computed in this representation; View B's shared-safe-2
  alignment operates on alternating cell sequences.

## Validation

Exact enumeration of real stages (raw sieve, complete periods):

| Filters | Gaps | 2-gaps | Cells | 2-cells | Share |
|---|---:|---:|---:|---:|---:|
| 2,3,5 | 8 | 3 | 6 | 3 | 0.5000 |
| 2,3,5,7 | 48 | 15 | 30 | 15 | 0.5000 |
| 2,3,5,7,11 | 480 | 135 | 270 | 135 | 0.5000 |

No adjacent `2,2` in any raw cycle. These checks confirm the derivation;
the theorem rests on the proof above.

## Related

- [Two-gap placement saturation and the cross-fiber coupling boundary](
  two-gap-placement-saturation.md) — shares the mod-3 non-adjacency fact.
- [Local surplus](../../candidates/local-surplus.md) — the
  one-strike-one-gap step built on the same post-3 disjointness.
- [Absence of 2-gaps is stable](absence-of-two-gaps-is-stable.md)
- [Dream sequence self-propagating invariant](
  ../../candidates/dream-sequence-self-propagating-invariant.md)
