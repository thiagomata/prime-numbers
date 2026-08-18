# Expanded-Zone Exterior-Capacity Localization

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implications:** Mathematically proved.

**Empirical status:** UNMEASURED — the required exactly countable expansions
and exterior capacities have not yet been constructed for a growing family of
future heads.

## Purpose

Complete lifted copy orbits have exact survivor counts, while the square-safe
prime-certifying target is only a short partial-period interval. This candidate
asks whether one can enlarge that target just enough to recover exact counting,
then prove that the added exterior cannot contain every survivor.

It also records an alternative selection formulation: follow one safe branch
through the copy-index tree and keep its numerical growth below a later square
certification horizon.

## Square-Safe Target and Expanded Zones

For a future prime head `q`, let

```math
W_q=[q,q^2)
```

be the square-safe target window. Count complete 2-gaps by their starts, so
define the square-safe target start interval

```math
W_q^{(2)}=[q,q^2-2).
```

Let `S_q(X)` count 2-gap starts in `X` after every prime filter below `q` has
been installed. Choose an expanded start region

```math
W_q^{(2)}\subseteq\widetilde W_q
```

built from complete lifted fibers, complete copy-index blocks, or another
decomposition on which an exact or rigorous lower count is available.

## Main Candidate: Positive Exterior-Subtracted Surplus

The candidate is that for infinitely many future heads `q`, there exist:

1. an exactly countable expansion `tilde W_q`;
2. a proved lower bound `L_q` with

   ```math
   S_q(\widetilde W_q)\ge L_q;
   ```

3. a proved exterior-capacity bound `U_q` with

   ```math
   S_q(\widetilde W_q\setminus W_q^{(2)})\le U_q;
   ```

such that

```math
L_q>U_q.
```

The expansion may use a seed stage that moves with `q`; a fixed ancient seed
is not required.

## Why It Is Sufficient

The expanded region is the disjoint union of its square-safe-target part and its
exterior part. Therefore

```math
\begin{aligned}
S_q(W_q^{(2)})
&=
S_q(\widetilde W_q)
-
S_q(\widetilde W_q\setminus W_q^{(2)})
\quad\text{[By Definition]},\\
&\ge
L_q-U_q
\quad\text{[By the two bounds]},\\
&>0
\quad\text{[By the candidate inequality]}.
\end{aligned}
```

Thus a complete 2-gap lies in `[q,q^2)`. After all primes below `q` have been
installed, square-safe certification makes its two endpoints prime.

The conditional implication is exact. The unproved content is constructing
`tilde W_q`, `L_q`, and `U_q` with a positive difference for infinitely many
`q`.

## Exterior Capacity

After filter `3`, distinct 2-gap starts are separated by at least `6`.
Therefore a component interval of length `ell` has a simple packing upper
bound of order

```math
\frac{\ell}{6}+1.
```

For a union of exterior components, the component bounds can be summed.
Sharper bounds may use:

- the exact accepted-shot count in each component;
- the fixed shot-spacing profile `sigma_r(k)=rD(k)`;
- forbidden copy-index phases rather than only component length;
- endpoint-disjoint `(2,4,2)` cluster counts;
- overlap information shared by the exterior blocks.

The useful expansion is the one that minimizes exterior capacity relative to
the exact survivor total, not necessarily the one that reaches a complete
primorial period.

## Falsifier for the Naive Complete Lift

Let an old region contain `G` 2-gaps and lift it through all `r` repeated
copies. Exact copy-index filtering leaves

```math
(r-2)G
```

surviving copies. If one component is designated as the square-safe target, the other
`r-1` components can hold as many as

```math
(r-1)G
```

copies of those old gaps. Since

```math
(r-2)G\le(r-1)G,
```

the total count alone cannot force a survivor into the designated component.

For complete `(2,4,2)` clusters, the analogous comparison is

```math
(r-4)C\le(r-1)C.
```

Thus “expand through every copy and use the global count” is not itself the
candidate. A viable proof needs a smaller expansion, a stronger exterior
bound, copy-phase information, or aggregation across many moving seeds.

## Alternative Candidate: A Slow Square-Safe Copy Branch

Let a current 2-gap or `(2,4,2)` cluster begin at `a_i` in a stage of period
`M_i`. At the next prime `r_i`, its copied starts are

```math
a_i+j_iM_i,
\qquad
0\le j_i<r_i.
```

An individual 2-gap has `r_i-2` safe copy indices; a complete cluster has
`r_i-4` safe indices. Choose a safe index and define

```math
a_{i+1}=a_i+j_iM_i.
```

The alternative candidate is that for infinitely many finite future
scenarios, some safe branch and later certification head `q` satisfy

```math
q\le a_i
\qquad\text{and}\qquad
a_i+2<q^2
```

for a surviving 2-gap, or `a_i+8<q^2` for a complete cluster.

This branch condition would place the survivor directly inside a square-safe
window. Its difficulty is scale: primorial periods grow much faster than the
square horizon, so merely having many safe children does not show that one has
a sufficiently small copy index.

The branch and exterior-surplus formulations attack the same selection
problem from opposite directions:

- exterior surplus proves that not all survivors can stay outside;
- a slow branch explicitly selects one survivor that stays inside.

## Perfect Distribution and Its Boundary

For a fixed old position, its `r` lifted copies visit every residue modulo the
new prime exactly once. This is perfect distribution in the copy-index
coordinate.

It is not uniform distribution among short numerical subintervals inside one
old copy. Repetition reproduces an empty relative slice just as exactly as it
reproduces a populated one. The candidate therefore does not assume that a
global density transfers to `[q,q^2)`.

## Incremental Danger-Annulus Alternative

The full-window post-filter argument above remains valid. A separate
pre-filter formulation can target only the newly exposed population defined in
the [incremental danger-annulus decomposition](../properties/sieve-sequence/incremental-danger-annulus-decomposition.md).
For consecutive primes `p<q` with `p>=5`, reuse the phase-compatible coordinate set

```math
X_D(p,q)=
\left\{
x\in\mathbb Z:
p^2+4\le x<q^2-2,
\quad x\equiv5\pmod6
\right\}.
```

Define a distinct pre-filter counting function

```math
S_{<p}(X)
=
\#\{\text{actual 2-gap starts in }X
\text{ after filters below }p\}.
```

This is not the post-filter observable `S_q` used above. In particular,

```math
L_D(p,q)=S_{<p}(X_D(p,q)).
```

Choose an exactly countable expansion with

```math
X_D(p,q)\subseteq\widetilde X_D
```

and prove pre-filter bounds

```math
S_{<p}(\widetilde X_D)\ge B_D,
\qquad
S_{<p}(\widetilde X_D\setminus X_D(p,q))\le U_D.
```

Exterior subtraction would then give

```math
\begin{aligned}
L_D(p,q)
&=
S_{<p}(\widetilde X_D)
-S_{<p}(\widetilde X_D\setminus X_D(p,q)),\\
&\ge B_D-U_D.
\end{aligned}
```

The exact sufficient exterior target is

```math
B_D-U_D>A(p,q)-1.
```

By the incremental form of [local surplus](local-surplus.md), this forces a
newly exposed surviving 2-gap. With `d=q-p`, the simpler raw sufficient target
is

```math
B_D-U_D>
2d+\left\lceil\frac{d^2}{p}\right\rceil-1.
```

The annular formulation has a smaller effective destruction allowance, but it
also counts a smaller pre-filter population. No theorem currently shows that
this tradeoff is easier: a favorable exactly countable `widetilde X_D` and
bounds `B_D,U_D` have not been constructed.

## Relation to Existing Candidates

- [Local surplus](local-surplus.md) gives terminal inequalities in both the
  square-safe target and the incremental annulus. Exterior subtraction is one
  proposed mechanism for proving the required local population.
- [Protected cluster](protected-cluster.md) bounds what one filter can destroy
  after a local cluster is already present.
- [Forbidden-copy covered run](forbidden-copy-covered-run.md) fixes one old
  gap and asks whether its eligible copy-index interval escapes the forbidden
  union. The present candidate allows moving seeds, multiple blocks, and an
  aggregate exterior comparison.
- [Hereditary shot-spacing capacity](hereditary-shot-spacing-capacity.md)
  processes local populations layer by layer. Expanded-zone localization is a
  possible source of the local populations required there.
- [Sharp admissible shot spacing](sharp-admissible-shot-spacing-profile.md)
  supplies exact fixed-`k` shot capacities but does not supply localization.

## Established Inputs

- [Exact global two-gap count](
  ../properties/sieve-sequence/exact-global-two-gap-count.md
  )
- [Exact global `(2,4,2)` cluster count](
  ../properties/sieve-sequence/exact-global-two-gap-cluster-count.md
  )
- [Exact copy-index filter frequency](
  ../properties/sieve-sequence/copy-index-filter-frequency.md
  )
- [Exact batched two-gap survival](
  ../properties/sieve-sequence/exact-batched-two-gap-survival.md
  )
- [2-gap endpoint isolation](
  ../properties/sieve-sequence/two-gap-isolation-after-filter-three.md
  )
- [Square-safe certification](
  ../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md
  )
- [Fixed-k shot spacing](
  ../properties/sieve-sequence/stable-small-k-shot-spacing.md
  )

## Success and Failure Criteria

The main route succeeds when an explicit family of expansions and rigorous
bounds satisfies `L_q>U_q` for infinitely many `q`. A finite positive run is
empirical reinforcement only.

The slow-branch route succeeds when a safe copy-index path is proved to enter
the corresponding square window for infinitely many certification heads.

The naive full-copy lift is already insufficient by the displayed capacity
comparison. Failure of one natural expansion does not refute the general
candidate; it identifies the exterior bound or branch selection that must be
strengthened.
