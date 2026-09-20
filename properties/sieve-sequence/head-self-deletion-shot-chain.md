# Head Self-Deletion Shot Chain

**Status:** Mathematically proved (elementary structural chain). Stainless
verification is not claimed here.

## Meaning

Several established facts are recorded separately in this catalog: the head is
the smallest accepted value above `1`, the accepted multipliers of an incoming
prime start at that prime itself, the first accepted multiple is `p^2`, and
the square window below `p^2` carries no filter strikes. This note derives all
of them from one root mechanism, **head self-deletion**: when a head becomes a
filter, its first shot lands on itself. The chain also yields a corollary that
explains the whole-window worst cases observed at small prime gaps — in
particular at twin transitions — as forced degeneracy rather than adversarial
alignment.

## Setup

Let a stage have head `h` (prime), installed filters = all primes below `h`,
modulus `M` = their product, and next head `h'` = the next prime after `h`.
The accepted set is the set of integers coprime to every filter.

## Step 1 — Self-Deletion

The head `h` is accepted at its own stage, because `h` is prime and shares no
factor with any smaller prime. Installing `h` as a filter removes every
accepted multiple of `h`. The multiple `h = h * 1` is accepted, so it is
removed: **the transition's first deletion is the old head itself.** The
multiplier `1` is the only accepted multiplier below `h`, so this shot cannot
be redirected and lands below the new head, outside any later window.

## Step 2 — The Graveyard and the Always-Merged Closing Gap

Every integer `v` with `1 < v < h` has a prime factor below `h`: if `v` is
prime it is itself a filter, and if `v` is composite its smallest prime factor
is below `v < h`. Hence no value strictly between `1` and `h` is accepted, and
by induction over transitions the accepted values in `[1, h')` at the old
stage are exactly `{1, h}`.

Two consequences:

- The closing gap of the head-anchored cycle (the gap arriving at `h'` from
  below) is always `h' - 1`.
- That closing gap is **always a merged gap**. Deleting `h` merges the two old
  gaps `1 -> h` and `h -> h'`, so the closing gap grows by exactly the prime
  gap `h' - h` at every transition, and its value is the running sum of all
  prime gaps so far. A copy is structurally impossible: the old head always
  sits between `1` and `h'`, so those endpoints are never previously adjacent.

The stretch `(1, h)` is a graveyard of past heads: every prime below `h` was
once a head, was accepted at its own stage, and was deleted by itself at its
own transition. The closing gap `h - 1` is the merged remains of that chain.

## Step 3 — The Scaled Graveyard Is the Shot Desert

The accepted multiples of `h` are exactly `h * k` for multipliers `k` coprime
to `M`. The multipliers below `h` are only `k = 1` (Step 2), and the next
coprime multiplier is `h` itself. Therefore there is **no accepted multiple of
`h` in `(h, h^2)`**: the shot train skips from the self-shot at `h` to the
square shot at `h^2`. This re-derives the established multiplier theorem
(exact accepted local filter strikes) as the graveyard scaled by `h`.

## Step 4 — Window Confinement

For the safe window `[h', h'^2)`, the sub-interval `[h', h^2)` lies inside the
shot desert, so it carries no strikes from filter `h`; every window shot lies
in `[h^2, h'^2)`. This is the window-geometry form of Step 3: the window is
shot-free below the square of the incoming filter.

## Step 5 — The Compulsory Opening

The shot train opens at three forced positions with two forced deserts:

```text
h        (self-shot, below the window)
   desert (h, h^2)          length h^2 - h
h^2       (square shot, inside every relevant window)
   desert (h^2, h*h')       length h*(h'-h) >= 2h
h*h'      (third shot)
```

No choice is involved in these positions; they follow from Steps 1-3 alone.

## Corollary — Small-Gap Degeneracy and the Observed Worst Cases

Suppose `h' = h + 2` (a twin transition, `h >= 5`). Then `h ≡ 2 (mod 3)`,
because one of `h, h+2, h+4` is divisible by `3` and `h, h+2 > 3` are prime.
Hence `h + 4` is composite, the multiplier range `[h, floor((h'^2-1)/h)]` ends
at `h + 4`, and its only primes are `h` and `h+2`. Therefore

```text
A(h, h') = 2, and the entire window budget is the compulsory pair
{h^2, h*h'}, spaced exactly 2h.
```

The same two-shot budget can occur at other small prime gaps whenever no prime
lies in `(h', floor((h'^2-1)/h)]`.

This explains the whole-window worst cases recorded in candidate #14's
empirical status: every measured transition with `destroyed = A(p,q)` had
`A(p,q) = 2` — including the twin transitions `(239,241)`, `(313,317)`,
`(569,571)` and the small-gap cases `(5,7)`, `(19,23)`, `(11681,11689)`. At
such transitions the filter fires exactly two shots, both at compulsory
positions, and `destroyed = A` records that both landed on 2-gap endpoints.
The outcome is decided by arithmetic at two fixed positions; the
random-versus-adversarial distinction is vacuous there, and the clustering of
worst cases at twin transitions is forced degeneracy, not evidence of
adversarial alignment.

## Verification

Steps 1, 2, and 5 were verified by exact computation for every transition with
heads `3` through `23` (self-deletion present; closing-gap increments equal to
the prime gaps `2, 2, 4, 2, 4, 2, 4`), and the compulsory openings for
`p ∈ {11, 13, 239, 569}`. Each step of the chain is elementary and general.

## Limitation

The chain is explanatory. It fixes where shots can and cannot land and
identifies the forced opening, but it provides no bound on the placement of
2-gap starts relative to the shots after `h*h'`, and it does not advance the
open hereditary placement obligation of candidate #14 or any short-window
discrepancy estimate.

## Related

- [Exact accepted local filter strikes](exact-accepted-local-filter-strikes.md)
  — the `k >= p` multiplier theorem, derived here as the scaled graveyard.
- [Copy-or-merge gap dynamics](../../articles/chapter6/sieve-sequence.md) —
  the transition rule whose only compulsory merge at every stage is the
  closing-gap merge of Step 2.
- [Hereditary shot-spacing capacity](../../candidates/hereditary-shot-spacing-capacity.md)
  — candidate #14, whose observed whole-window worst cases are explained by
  the corollary.
- [Fixed-k shot spacing](stable-small-k-shot-spacing.md) — the twin units
  `M-1, 1` supplying `sigma_r(2) = 2r`.
