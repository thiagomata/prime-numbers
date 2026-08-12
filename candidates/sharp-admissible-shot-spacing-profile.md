# Sharp Admissible Shot-Spacing Profile

**Candidate hypothesis:** Beyond the proved range `2\le k\le14`, the sharp
profile admits useful recurrence inequalities, scalable extremal bounds, and
structural classifications of optimal patterns.

**Proved foundation:** Fixed-`k` wheel spacing eventually stabilizes and equals
the minimum diameter of an admissible `k`-point pattern. The exact values
`D(2)..D(14)` are proved.

**Empirical status:** An exact `k=2` application sweep found no interval
failure in 1,837 layers across 53 heads. This finite agreement concerns the
downstream square-window application, not the now-proved profile through
`k=14`.

## Purpose

This candidate makes the intrinsic capacity function the central object.
Instead of beginning with a particular square window or hereditary survival
chain, it asks for the exact stable profile, extremal structure, and useful
recurrences of

```math
s_P(k)
=
\min_i\sum_{t=0}^{k-2}g_{i+t},
\qquad
\sigma_r(k)=r\,s_P(k).
```

Candidate #14 can consume these results later. Its local interval premise is
not part of the central claim here.

## Proved Foundation

For a finite integer set `H`, call `H` admissible when

```math
H\bmod p\ne\mathbb Z/p\mathbb Z
\qquad
\text{for every prime }p.
```

Define the extremal admissible diameter

```math
D(k)
:=
\min\left\{
\max H-\min H:
|H|=k,\ H\text{ is admissible}
\right\}.
```

The fixed-`k` spacing theorem proves that once a primorial wheel contains every
prime `p\le k` and its period exceeds an explicit admissible-pattern bound,

```math
s_P(k)=D(k),
\qquad
\sigma_r(k)=rD(k).
```

Thus eventual stability is a theorem. The open problem is to determine the
sharp profile `D(k)`, not to extrapolate indefinitely from larger wheels.

The same property note proves

```math
\begin{aligned}
D(2)&=2,  &D(3)&=6,  &D(4)&=8,\\
D(5)&=12, &D(6)&=16, &D(7)&=20,\\
D(8)&=26, &D(9)&=30, &D(10)&=32,\\
D(11)&=36, &D(12)&=42, &D(13)&=48,\\
D(14)&=50.
\end{aligned}
```

This result is proved in
[Fixed-k Shot Spacing: Monotonicity and Eventual Stability](
../properties/sieve-sequence/stable-small-k-shot-spacing.md
).

## Proved Exact Profile Through k=14

The proved continuation is

```math
\begin{aligned}
D(11)&=36,\\
D(12)&=42,\\
D(13)&=48,\\
D(14)&=50.
\end{aligned}
```

The following patterns supply the upper bounds:

| `k` | admissible pattern `H` | diameter |
|---:|---|---:|
| 11 | `{0,2,6,8,12,18,20,26,30,32,36}` | 36 |
| 12 | `{0,2,6,8,12,18,20,26,30,32,36,42}` | 42 |
| 13 | `{0,2,6,8,12,18,20,26,30,32,36,42,48}` | 48 |
| 14 | `{0,2,6,8,12,18,20,26,30,32,36,42,48,50}` | 50 |

For a `k`-point pattern, primes greater than `k` cannot be fully covered.
Checking only primes `p\le k` therefore proves admissibility of each listed
pattern. Consequently, the table gives mathematically proved upper
bounds

```math
D(k)\le d_k
\qquad
(11\le k\le14),
```

where `d_k` is the listed diameter.

For the matching lower bounds, normalize a hypothetical shorter pattern to
contain `0`. Admissibility modulo `2` forces all offsets even. If it misses
`a\in\{1,2\}` modulo `3` and `b\in\{1,2,3,4\}` modulo `5`, it must lie in

```math
U_d(a,b)=
\{x\in\{0,2,\ldots,d-2\}:x\not\equiv a\pmod3,\
x\not\equiv b\pmod5\}.
```

For `k=11`, every such ambient set is too small. For `k=12,13,14`, only
fourteen ambient sets are large enough. Thirteen force the entire pattern;
the remaining set has fourteen points for `k=13`. Every forced pattern covers
all residues modulo `7`, while the larger set has multiplicity two in every
modulo-7 class, so deleting one point still leaves full coverage. Every
hypothetical shorter pattern is therefore inadmissible.

The full ambient sets, cardinalities, and residue multiplicities are exposed
in the proved property note linked above. Thus

```math
D(11)=36,\quad D(12)=42,\quad
D(13)=48,\quad D(14)=50.
```

The exhaustive normalized searches were useful discovery evidence before the
compact proof was found:

| `k` | first admissible diameter | normalized patterns tested |
|---:|---:|---:|
| 11 | 36 | 24,037 |
| 12 | 42 | 217,594 |
| 13 | 48 | 1,691,308 |
| 14 | 50 | 3,251,477 |

They are no longer the basis for the equalities.

## Recurrence and Extremal Program

The exact characterization turns recurrence questions about wheel depth into
questions about the extremal sequence `D(k)`.

Already proved or immediate from the definition:

```math
D(k+1)\ge D(k),
```

because deleting one point from an admissible `(k+1)`-point set leaves an
admissible `k`-point set of no larger diameter.

The following remain open research targets:

- sharp upper and lower bounds for `D(k)` beyond the tabulated range;
- recurrence inequalities relating `D(k+1)` to earlier values without falling
  back to the large primorial bound;
- classification of optimal patterns and whether optimal patterns can be
  chosen from a recursively related family;
- finite obstruction certificates that scale better than enumerating every
  subset of an interval.

No recurrence equality or asymptotic formula is asserted by this candidate.

## Empirical Falsification Program

There are two distinct sweeps:

1. **Profile sweep.** For `k>14`, generate an admissible witness and search
   below its diameter. A smaller pattern refutes that proposed next entry;
   absence in a finite search remains evidence until replaced by a transparent
   residue-cover certificate. Searching larger wheels is secondary because
   the characterization has removed wheel depth from the sharp-value question.
2. **Application sweep.** Across many future heads `Q`, test candidate #14's
   interval premise using only proved `D(k)` values. The exact profile through
   `k=14` is currently available; values beyond that range must not be used as
   exact input until proved.

The first expanded application sweep tested every prime head from `17` through
`251`, plus `307,401,503,701,997`: 53 heads and 1,837 defined layers. No exact
`k=2` interval failed, and every nearest-pair enclosure had length at most `8`.
The complete-period pattern `{0,2,6,8}` explains why this cluster exists
somewhere in each sufficiently deep wheel; its repeated placement inside the
absolute square windows remains empirical.

The existing finite evidence is collected in
[Empirical Evidence for Hereditary Shot Spacing](
../empirical/sieve-sequence/hereditary-shot-spacing.md
).

## Copy-Index Clustering Application

The stable capacity theorem controls how tightly destructive shots can occur.
It does not force useful 2-gap starts to cluster in a particular numerical
window. A separate local theorem would need to connect repeated-copy indices
and their forbidden classes to an interval `J` satisfying

```math
G_r(J)\ge k,
\qquad
\text{len}(J)<rD(k).
```

Finding such a copy-index-to-cluster theorem is a downstream application of
the capacity profile. It is not assumed in the exact `D(k)` candidate.

## Relation to Candidate #14

[Hereditary Shot-Spacing Capacity](
hereditary-shot-spacing-capacity.md
) asks whether a suitable local interval exists at every conditioned layer.
The present candidate supplies the exact global capacity constant once `D(k)`
is proved. It does not claim the local interval exists.

The separation is deliberate:

- candidate #15 studies the intrinsic wheel invariant `D(k)`;
- candidate #14 studies whether conditioned local 2-gap populations beat that
  capacity in square windows.

## Success and Failure Criteria

For each proposed value beyond `k=14`, the next-profile candidate succeeds
when both an admissible witness of diameter `d_k` and a complete lower-bound
certificate below `d_k` are available.

It fails entry by entry if a smaller admissible `k`-point pattern is found.
Failure of one proposed value does not affect the proved stabilization theorem;
it replaces that entry with a smaller proof target.
