# Exact-Quota Head Recurrence

**Status:** Mathematically proved conditional on a bounded-below head
availability premise (`b_0 > 0`, uniform over sufficiently large prime
heads) compatible with the quota-survival experiment, and, for the
divergent direction, independence or an adequate cross-layer mixing
condition. For the exact-quota random-location companion. Not a claim about
the real modular filter.

## Meaning

Under exact-quota, uniform-without-replacement strike placement, and with
persistent-enough head availability, the distinguished head lands on a
2-gap infinitely often almost surely -- the same head-recurrence conclusion
the balanced-random companion reaches, by way of the exact-quota survival
factor instead of independent per-parent deletion.

## Setup

Let `P_quota(Q) \asymp C/(\log Q)^2` be
[the exact-quota survival factor](exact-quota-survival-factor.md), and
suppose the distinguished head candidate is eligible with conditional
probability at least `b_0>0`, uniformly for all sufficiently large prime
heads, compatibly with the quota-survival experiment. Let `H_Q` be the
event that the head is a 2-gap at stage `Q`.

## Property

```math
\begin{aligned}
b_0P_{\mathrm{quota}}(Q)
&\le\Pr(H_Q)\le P_{\mathrm{quota}}(Q),
&&[\text{Uniform Availability Bounds}]\\
\Pr(H_Q)
&\asymp\frac{1}{(\log Q)^2}.
&&[\text{Quota Survival Asymptotic}]
\end{aligned}
```

Consequently,

```math
\begin{aligned}
\sum_{Q\text{ prime}}\Pr(H_Q)
&\asymp
\sum_{Q\text{ prime}}\frac{1}{(\log Q)^2}\\
&=\infty.
&&[\text{Prime Number Theorem}]
\end{aligned}
```

Under independence or an adequate cross-layer mixing condition, the second
Borel-Cantelli lemma yields

```math
\Pr(H_Q\text{ occurs infinitely often})=1.
\qquad[\text{Q.E.D.}]
```

This is an almost-sure theorem, not a guarantee for every random
realization: the set of realizations with only finitely many head hits has
probability zero, but it is not logically empty.

## Related

- [Exact-quota random-location companion process](../model.md)
- [Exact-Quota Survival Factor](exact-quota-survival-factor.md) -- supplies
  `P_quota(Q)` used here.
- [Exact-Quota Square-Window Persistence](
  exact-quota-square-window-persistence.md)
- [Head Recurrence Under Adversarial/Protective Parent Mixing](
  ../../balanced-good-2-gap/properties/head-recurrence-adversarial-protective-mixing.md)
  -- the balanced-good companion's analogous head result, for comparison.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §7.1](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
