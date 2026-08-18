# Bounded Pair Separation Gives the k=2 Interval Premise

**Status:** Mathematically proved (conditional lemma). Stainless verification
is not claimed here.

## Meaning

For candidate #14 (hereditary shot-spacing), two nearby 2-gaps are enough to
satisfy the per-layer interval premise with `k_r=2`. The necessary condition
is not merely that two starts exist: the interval enclosing both complete
2-gaps must be shorter than the minimum separation `sigma_r(2)=2r` between
two destructive shots.

This is a conditional geometric implication. It neither proves that such a
nearby pair occurs in every layer nor turns finite observations into an
all-stage theorem.

## Setup

Fix a layer `r` of a fixed-future-window chain on `W_Q = [Q, Q^2)`, with
`r >= 5` (post-filter-3). Recall
([stable-small-k-shot-spacing](stable-small-k-shot-spacing.md)) that
the cofactor minimum span is `s(2)=2`, so the corresponding shot separation is
`sigma_r(2)=r s(2)=2r`.

## Lemma (k=2 interval premise from bounded pair separation)

Suppose `x_1<x_2` are starts of two complete 2-gaps contained in `W_Q` and

```math
x_2+2-x_1<2r.
```

Then there is a half-open interval `J_r\subseteq W_Q` with
`G_r(J_r)\ge2` and `\operatorname{len}(J_r)<\sigma_r(2)`.

## Proof

Set `J_r=[x_1,x_2+2)`. Because both complete gaps are contained in `W_Q`,
this interval is a subset of `W_Q`. Both starts lie in `J_r`, and therefore

```math
G_r(J_r)\ge2.
```

Its length satisfies

```math
\begin{aligned}
\operatorname{len}(J_r)
&=x_2+2-x_1
\quad\text{[By Definition]}\\
&<2r
\quad\text{[By Hypothesis]}\\
&=\sigma_r(2)
\quad\text{[Substitution].}
\end{aligned}
```

Thus `J_r` satisfies the candidate’s interval premise with `k_r=2`.
`[Q.E.D.]`

## Consequence

Combined with candidate #14's capacity implication, this gives:

> If a layer contains two complete 2-gaps whose enclosing interval has length
> less than `2r`, then at least one of those 2-gaps survives filter `r`.

Indeed, an interval shorter than the minimum separation between two shots
contains at most one shot, so at most one of the two isolated 2-gaps can be
destroyed there.

## Why pair existence alone is insufficient

Post-filter-3 starts lie in one residue class modulo `6`, so two distinct
starts are separated by at least `6`. This is a lower bound, not an upper
bound. Pair existence supplies no deduction that their separation is less
than `2r`: two starts may be arbitrarily far apart while retaining the same
residue class.

Consequently, neither `G_r(W_Q)\ge2` nor the congruence structure alone proves
the bounded-separation hypothesis. Establishing a sufficiently close pair in
every required layer remains part of candidate #14. Finite instances belong
in [the empirical #14 note](
../../empirical/sieve-sequence/hereditary-shot-spacing.md
).

## Related

- [stable-small-k-shot-spacing](stable-small-k-shot-spacing.md) — supplies
  `sigma_r(2) = 2r`, the capacity side.
- [two-gap-isolation-after-filter-three](two-gap-isolation-after-filter-three.md)
  — supplies the `5 mod 6` structure, which gives a lower separation bound but
  not the upper bound needed here.
- [copy-index-filter-frequency](copy-index-filter-frequency.md) — the strike
  rule that makes "at most 1 shot in `J_r`" the right bound.
- [hereditary-shot-spacing-capacity](
  ../../candidates/hereditary-shot-spacing-capacity.md
  ) — the candidate whose bounded-separation premise this lemma uses.
