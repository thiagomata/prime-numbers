# Exact-Quota Random-Location Companion Process

**Candidate hypothesis:** N/A -- this file states and proves facts about a
constructed companion process, not an open hypothesis about the real sieve.

**Conditional implication:** Mathematically proved (see the properties
below); the premises each theorem needs are stated explicitly in that
theorem's Status line, not assumed silently.

**Empirical status:** Not yet measured (no simulation run).

## Purpose

[The balanced randomized 2-gap companion](../balanced-randomized-2-gap/model.md)
fixes exactly two harmful copy indices per parent. This companion instead
starts from a different real-sieve invariant: the *exact number* of accepted
strikes a filter supplies against a real CRT population, and randomizes only
*where* those strikes land, not how many there are. It preserves the real
count while removing the arithmetic targeting information -- a closer
statistical companion to the real filter's exact accepted-strike law than a
model that only fixes the per-parent casualty count.

Exact quotas create dependence within one layer (the strikes are drawn
without replacement from a shared population), but that dependence does not,
by itself, change the one-position survival scale when the quota is
allocated uniformly -- the properties below prove the same leading order as
the balanced-random companion, with sharper or different lower-order terms.

## Definition

At filter `r`, let `U_r` contain `N_r` eligible values and let the CRT quota
be `J_r`, with `0 \le J_r \le N_r-2`. The exact-quota random-location model
chooses one uniformly random size-`J_r` subset of `U_r` as its strike set.

For a specified 2-gap whose two endpoints both belong to `U_r`, both
endpoints survive precisely when every strike is selected from the other
`N_r-2` values:

```math
\begin{aligned}
s_r
&=\frac{\binom{N_r-2}{J_r}}{\binom{N_r}{J_r}}
&&[\text{Uniform Exact-Quota Choice}]\\
&=\frac{(N_r-J_r)(N_r-J_r-1)}{N_r(N_r-1)}.
&&[\text{Factorial Simplification}]
\end{aligned}
```

This is not an independent Bernoulli filter inside one layer -- it is a
uniform shuffle conditioned on the exact CRT strike count `J_r`, which
introduces the without-replacement correction visible in the exact factorial
form.

## Real-Sieve Correspondence

The real accepted-strike count in the next safe window, for consecutive
primes `p<q`, is proved in [Gap Dynamics §9.1](
../../articles/chapter6/gap-dynamics.md#91-exact-accepted-strikes):

```math
A(p,q)
=
\pi\left(\left\lfloor\frac{q^2-1}{p}\right\rfloor\right)
-\pi(p-1).
```

Using this local quota as `J_r=A(p,q)` in this companion is well defined,
but its resulting strike fraction `u_r=J_r/N_r` must still satisfy the
cumulative conditions used by the properties below -- preserving a numerical
strike count alone does not make either conclusion automatic. Neither this
companion's exact count nor the real sieve's
[complete-period count](../../articles/chapter6/gap-dynamics.md#52-exact-non-recursive-global-count)
determines local placement in the real sieve; that is a separate, open
transfer obligation.

## Related

- [Exact-Quota Survival Factor](properties/exact-quota-survival-factor.md)
- [Exact-Quota Head Recurrence](properties/exact-quota-head-recurrence.md)
- [Exact-Quota Square-Window Persistence](
  properties/exact-quota-square-window-persistence.md)
- [Balanced randomized 2-gap companion process](../balanced-randomized-2-gap/model.md)
  -- the fixed-casualty-count companion this model is compared against.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §7.1](
  ../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
  -- the source article section defining this model.
