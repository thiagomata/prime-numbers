# Uniform-Digit 2-Gap Companion (Digit Dust)

**Status:** Constructed companion model. Fully collapsed: every statistic
reduces to finite digit arithmetic. Not a model of the real sieve.

## Definition

Start from the post-3 base: period `P_0=6`, base values `{1,5}`. At layer
`k` with incoming prime `r_k`, each value `v` has its `r_k` lifts
`v+jP_k`. The **uniform-digit rule** removes the same two lifts of every
value:

```math
j\in\{0,1\}\ \text{killed},\qquad j\in\{2,\ldots,r_k-1\}\ \text{kept},
```

independently of `v` — in contrast to the real sieve, which kills the
single lift `-vP_k^{-1} mod r_k` determined by divisibility.

The value set after layers `r_1..r_m` is exactly the mixed-radix
restricted-digit set

```math
S_m=\Bigl\{x_0+\sum_{k=1}^m j_kP_{k-1}\ :\ x_0\in\{1,5\},\ j_k\in\{2,\ldots,r_k-1\}\Bigr\},
\qquad \Pi_m=6\prod_k r_k.
```

The model's 2-gaps are pairs `(v, v+2)` of consecutive values of `S_m`
(consecutivity is automatic: `v+1` is even, never in `S_m`).

## Declared Differences From The Real Sieve

- **Value growth**: each value leaves `r-2` lifts (not `r-1`): the value
  count is `2*prod(r-2)`, not the totient chain.
- **2-gap copy law**: an interior 2-gap parent (both endpoints in one
  digit block) has exactly the two harmful classes `{0,1}` and leaves
  `r-2` copies — the balanced law holds. A block-crossing parent
  (base pair `(5, 7≡1 mod 6)`) has harmful classes `{0,1,-1}` and leaves
  `r-3` copies. The 2-gap count is therefore governed by the transfer
  matrix below, not by a pure `(r-2)`-fold recursion.
- **Creation**: unlike the real sieve (no creation, by the mod-3
  argument), block-crossing 2-gaps are re-created at every layer's digit
  boundaries. This is a genuine behavioral difference, recorded, not
  hidden.

## Design Intent

The model isolates the **gating axis** of the restriction map: it keeps
the layered structure, the periods, the per-parent removal counts, and
the Mertens-scale density — and replaces only the residue gating by
uniform gating. The result [collapses completely and clusters
completely](properties/digit-dust-collapse-and-clustering.md): it is the
deterministic witness that exact count laws, correct global density, and
balanced removals imply **nothing** about window occupancy, and that
collapse and dream are independent properties.
