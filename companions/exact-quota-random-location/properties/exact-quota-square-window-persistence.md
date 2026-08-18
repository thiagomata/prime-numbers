# Exact-Quota Square-Window Persistence

**Status:** Mathematically proved conditional on a quadratic eligible-supply
premise (`B(Q) \asymp C_0 Q^2`) and a blind-placement empty-window premise,
for the exact-quota random-location companion. Not a claim about the real
modular filter.

## Meaning

Under exact-quota, uniform-without-replacement strike placement, a growing
square-safe window is nonempty for all sufficiently large heads almost
surely -- a stronger, eventual-persistence conclusion, proved with no
independence premise beyond the empty-window bound itself.

## Setup

Let `B(Q) \asymp C_0 Q^2` be the number of eligible starts in the square
window, with the same blind-placement empty-window premise used by
[the balanced-random companion](
../../balanced-randomized-2-gap/properties/bad-random-square-window-boundary.md),
and let `P_quota(Q) \asymp C/(\log Q)^2` be
[the exact-quota survival factor](exact-quota-survival-factor.md).

## Property

```math
\begin{aligned}
\lambda_{\mathrm{quota}}(Q)
&=B(Q)P_{\mathrm{quota}}(Q)
&&[\text{Expected Surviving Starts}]\\
&\asymp
C_0\frac{Q^2}{(\log Q)^2}
\longrightarrow\infty.
&&[\text{Quadratic Supply Dominates}]
\end{aligned}
```

If

```math
\Pr(W_Q\text{ is empty})
\le e^{-\lambda_{\mathrm{quota}}(Q)},
```

the empty probabilities are summable over prime `Q`. The first
Borel-Cantelli lemma then gives only finitely many empty square windows
almost surely -- with no independence premise needed for this direction.
$\blacksquare$

This eventual-window statement is stronger than the twin-prime-style target:
an unbounded sequence of successful windows, or infinitely many head hits
(see [Exact-Quota Head Recurrence](exact-quota-head-recurrence.md)), is
already sufficient for infinitely many distinct certificates.

## Real-Sieve Local Quota

For consecutive primes `p<q`, the real accepted-strike count in the next
safe window is proved in [Gap Dynamics §9.1](
../../../articles/chapter6/gap-dynamics.md#91-exact-accepted-strikes):

```math
A(p,q)
=
\pi\left(\left\lfloor\frac{q^2-1}{p}\right\rfloor\right)
-\pi(p-1).
```

Using this local quota as `J_r=A(p,q)` in this companion is well defined,
but its fractions `u_r=J_r/N_r` must still satisfy the cumulative
conditions in [Exact-Quota Survival Factor](exact-quota-survival-factor.md)
for this property (and the head-recurrence property) to apply. The
[complete-period count](
../../../articles/chapter6/gap-dynamics.md#52-exact-non-recursive-global-count)
supplies the global density; neither exact count determines local placement
in the real sieve.

## Related

- [Exact-quota random-location companion process](../model.md)
- [Exact-Quota Survival Factor](exact-quota-survival-factor.md)
- [Exact-Quota Head Recurrence](exact-quota-head-recurrence.md)
- [Growing Square Windows Under Adversarial/Protective Parent Mixing](
  ../../balanced-good-2-gap/properties/growing-square-window-adversarial-protective-mixing.md)
  -- the balanced-good companion's analogous square-window result, for
  comparison.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §7.1](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
