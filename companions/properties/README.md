# Shared Companion Theorems

Model-agnostic companion properties used by every specialization in
[`../`](../README.md). These results do not belong to any single companion
model: they hold for any process that preserves the exact `r-2` descendant law
(common) and reports a realized destruction fraction `f_r` (hazard law), or
that assigns a size-`K` harmful set against a size-`L` relevant set
(allocation bounds).

The four named companion models specialize these theorems:

- [Balanced random](../balanced-randomized-2-gap/README.md) sets `f_r` from
  uniform harmful-index selection, with or without an adversarial mixture.
- [Balanced adversarial](../balanced-adversarial-2-gap/README.md) takes the
  targeted endpoint of the allocation range.
- [Balanced good](../balanced-good-2-gap/README.md) takes the optimistic
  endpoint.
- [Exact-quota random location](../exact-quota-random-location/README.md)
  replaces per-parent Bernoulli selection with uniform sampling without
  replacement at a fixed quota.

## Short-Name Registry

| Short Name | File |
|---|---|
| Global Persistence Independence | [global-persistence-independence.md](global-persistence-independence.md) |
| Cumulative Local Hazard Law | [cumulative-local-hazard-law.md](cumulative-local-hazard-law.md) |
| Fixed-Factor Survival | [fixed-factor-survival.md](fixed-factor-survival.md) |
| Logarithmic-Worsening Thresholds | [logarithmic-worsening-thresholds.md](logarithmic-worsening-thresholds.md) |
| Local Survivor Allocation Range | [local-survivor-allocation-range.md](local-survivor-allocation-range.md) |

## Scope Reminder

These are theorems about constructed companion processes, not about the real
modular filter. Spatial-uniformity, optimistic quadratic supply, head
availability, and cross-layer mixing are premises where a theorem needs them,
not facts about the real sieve. See the
[parent README](../README.md#scope-contract).
