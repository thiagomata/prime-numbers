# Digit-Dust Collapse And Clustering

**Status:** Mathematically proved. Stainless verification is not claimed.
Validated exactly on chains `r=(5)`, `(5,7)`, `(5,7,11)`.

## Meaning

The uniform-digit companion collapses completely: its value set is a
restricted-digit set, its value count is a closed product, its 2-gap count
is a finite transfer-matrix product — and simultaneously it clusters
completely: every period contains gaps of a fixed positive fraction of
the period. Together these prove, by explicit construction, that collapse
and local occupancy are independent: a process can share every count law
of the real sieve and still swallow every window.

## Collapse Laws

**Law 1 (exact digit representation).** After layers `r_1..r_m` the
value set is exactly

```math
S_m=\Bigl\{x_0+\sum_kj_kP_{k-1}\ :\ x_0\in\{1,5\},\ j_k\in\{2,\ldots,r_k-1\}\Bigr\}.
```

Membership is decided digit by digit — no residue computation, no CRT.

**Law 2 (closed value count).** Every value leaves exactly `r-2` lifts:

```math
|S_m|=2\prod_{k=1}^m(r_k-2).
```

Validated: `6, 30, 270` for `m=1,2,3`.

**Law 3 (transfer-matrix 2-gap count).** Every 2-gap starts at
`v = 5 (mod 6)` (the base pair is `(5, 7≡1)`: `v+2 = 1 (mod 6)`, and
`v ≡ 1` gives `v+2 ≡ 3 (mod 6)`, dead). Writing `v = 5 + 6u`, the pair
condition is that `u` and `u+1` both have all digits allowed. Adding 1
propagates a carry `c in {0,1}` through the mixed radices, so the count
is a product of two-state transfer matrices, one per layer:

```math
N_m=\#\{u : \text{digits}(u),\text{digits}(u+1)\text{ all allowed}\}
\quad\text{(explicit matrix product)}.
```

Validated against brute force: `N_m = 2, 10, 90` for `m = 1, 2, 3`,
exact matches. Every pair statistic of the model — counts, correlations,
run structure — reduces to the same finite carry-matrix arithmetic.

## Clustering Law

**Law 4 (period-fraction gaps).** At layer `m+1` with new prime `r`, the
digit blocks `j=0` and `j=1` contain **no** valid values (every value
whose top digit is 0 or 1 is killed by the uniform rule). Hence the
cyclic gap spanning from the last valid value of block `r-1` to the first
valid value of block `2` has length at least

```math
2P_m=\frac{2}{r}\,\Pi_{m+1}
```

— a fixed positive fraction of the period, at every layer, forever.
Validated: max gaps `14 >= 2*6`, `74 >= 2*30`, `494 >= 2*210`.

## Anti-Dream Corollary

The model has: the balanced removal counts (`r-2` per interior parent),
a Mertens-scale density, a conserved-ratio analogue, exact global counts,
a fully collapsed description — and gaps of period-fraction length. Any
window whose length is a vanishing fraction of the period (in particular
every safe-style window) is swallowed, at every stage. Therefore:

> **Count laws, balanced removals, and correct density do not imply
> window occupancy — and collapse does not imply the dream.**

This is the deterministic, closed-form witness for the spatial premises
the companion theorems must assume: the [phase-transition article](
../../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
imposes blind placement by hypothesis; the digit-dust sequence shows what
happens when placement is as structured as possible in the opposite
direction — uniform, clustered, collapsed. The real sieve's residue
gating is precisely the anti-clustering mechanism (CRT spread) whose
analysis is the open local problem.

## Related

- [Uniform-digit 2-gap companion model](../model.md)
- [Dream sequence self-propagating invariant](
  ../../../../candidates/dream-sequence-self-propagating-invariant.md) —
  the dream this model refutes-by-construction for uniform gating.
- [Past-span saturation does not determine placement](
  ../../../../properties/sieve-sequence/past-span-saturation-does-not-determine-placement.md)
- [CRT-coupled real-sieve transfer](../../candidates/crt-coupled-real-sieve-transfer.md)
