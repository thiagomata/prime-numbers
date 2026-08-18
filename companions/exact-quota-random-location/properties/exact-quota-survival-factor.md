# Exact-Quota Survival Factor

**Status:** Mathematically proved for the exact-quota random-location
companion, conditional on the stated cumulative-quota and summable-error
premises along the conditioned chain. Not a claim about the real modular
filter.

## Meaning

The per-layer survival probability of one specified 2-gap under exact-quota,
uniform-without-replacement strike placement reduces, to leading order, to a
simple exponential in the strike fraction. Multiplying this factor across
every filter below a prime head `Q` reproduces the same `(\log Q)^{-2}`
order that the balanced-random companion gets from its per-parent
`1-2/r` factor -- but from a structurally different mechanism (a shared,
without-replacement draw rather than independent per-parent coin flips).

## Setup

Let `s_r` be the exact-quota survival factor from
[the model definition](../model.md), and write the strike fraction as
`u_r:=J_r/N_r`. Assume that along the conditioned chain to head `Q`,

```math
\begin{aligned}
\sum_{r < Q}u_r
&=\log\log Q+O(1),
&&[\text{CRT-Rate Cumulative Quota}]\\
\sum_{r < Q}
\left(u_r^2+\frac{u_r}{N_r}\right)
&=O(1).
&&[\text{Summable Finite-Population Error}]
\end{aligned}
```

The complete-period CRT benchmark `u_r=1/r` satisfies both conditions. A
different local CRT quota must be checked against them individually;
preserving a numerical strike count alone does not guarantee they hold.

## Property

From the exact factorial form of `s_r`,

```math
\log s_r
=-2u_r+O\left(u_r^2+\frac{u_r}{N_r}\right).
```

Multiplying the exact without-replacement factors across the chain gives

```math
\begin{aligned}
P_{\mathrm{quota}}(Q)
&=\prod_{r < Q}s_r
&&[\text{Survive Every Filter}]\\
&=\exp\left(\sum_{r < Q}\log s_r\right)
&&[\text{Product To Sum}]\\
&=\exp\left(-2\sum_{r < Q}u_r+O(1)\right)
&&[\text{Summable Error}]\\
&\asymp\frac{C}{(\log Q)^2}.
&&[\text{Cumulative Quota Condition}]
\end{aligned}
\qquad[\text{Q.E.D.}]
```

Thus the exact-quota companion has the same one-head survival order as the
balanced-random companion, even though its per-layer mechanism (a shared
without-replacement draw within one filter's eligible population) is
structurally different from independent per-parent coin flips.

## Related

- [Exact-quota random-location companion process](../model.md)
- [Exact-Quota Head Recurrence](exact-quota-head-recurrence.md) -- applies
  `P_quota(Q)` to the distinguished head.
- [Exact-Quota Square-Window Persistence](
  exact-quota-square-window-persistence.md) -- applies `P_quota(Q)` to a
  growing square window.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §7.1](
  ../../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
