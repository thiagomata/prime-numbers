# Balanced Randomized 2-Gap Companion

The balanced randomized companion keeps the real sieve's exact `r-2` descendant
law but replaces the modular selection of the two destroyed descendants with
uniform selection without replacement. Its full definition, what it
preserves and does not preserve, and its role as a null model are in
[`model.md`](model.md).

Proved properties of the bad/random specialization live in
[`properties/`](properties/); model-specific open claims would live in a
local `candidates/` directory (none filed yet). The specialization is a position-blind mixture
in which each parent (or each filter) draws an adversarial harmful-pair
selection with share `alpha_r`, otherwise the uniform random selection. Its
phase thresholds are the absolute-share specializations of the shared
[Logarithmic-Worsening Thresholds](../properties/logarithmic-worsening-thresholds.md).

## Short-Name Registry

| Short Name | File |
|---|---|
| Bad/Random Square-Window Boundary | [properties/bad-random-square-window-boundary.md](properties/bad-random-square-window-boundary.md) |
| Constant-Share Trivial Fatality | [properties/constant-share-trivial-fatality.md](properties/constant-share-trivial-fatality.md) |
| Reciprocal-Decay Specialization | [properties/reciprocal-decay-specialization.md](properties/reciprocal-decay-specialization.md) |
| Log-Over-Linear Decay Specialization | [properties/log-over-linear-decay-specialization.md](properties/log-over-linear-decay-specialization.md) |
| Bad/Random Head Boundary | [properties/bad-random-head-boundary.md](properties/bad-random-head-boundary.md) |

## Shared Premises

Every proved property registered above assumes the mixed surviving starts obey the
spatial-uniformity model used by the balanced random companion. Head
recurrence additionally assumes independence or adequate cross-layer mixing.
These are premises about a constructed model, not facts about the real sieve;
see the [parent README](../README.md#scope-contract).
