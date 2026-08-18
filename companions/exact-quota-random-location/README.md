# Exact-Quota Random-Location Companion

The exact-quota random-location companion keeps the real sieve's exact CRT
accepted-strike count at each filter but randomizes only the locations of
those strikes, drawn uniformly without replacement from the eligible
population. It preserves the real count while removing the arithmetic
targeting information -- a closer statistical companion to the real filter's
exact accepted-strike law than a model that only fixes the per-parent
casualty count. Its full definition and real-sieve correspondence are in
[`model.md`](model.md).

## Short-Name Registry

| Short Name | File |
|---|---|
| Exact-Quota Survival Factor | [properties/exact-quota-survival-factor.md](properties/exact-quota-survival-factor.md) |
| Exact-Quota Head Recurrence | [properties/exact-quota-head-recurrence.md](properties/exact-quota-head-recurrence.md) |
| Exact-Quota Square-Window Persistence | [properties/exact-quota-square-window-persistence.md](properties/exact-quota-square-window-persistence.md) |

## Shared Premises

The survival-factor result assumes the stated cumulative-quota and
summable-error conditions along the conditioned chain (satisfied by the
complete-period CRT benchmark `u_r=1/r`). Head recurrence additionally
assumes bounded-below head availability compatible with the quota-survival
experiment, and, for the divergent direction, independence or adequate
cross-layer mixing. Square-window persistence additionally assumes a
quadratic eligible-supply premise and a blind-placement empty-window bound.
These are premises about a constructed model, not facts about the real
sieve; see the [parent README](../README.md#scope-contract).
