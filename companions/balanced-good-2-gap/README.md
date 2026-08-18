# Balanced Good (Protective Parent) 2-Gap Companion

The balanced good companion keeps the real sieve's exact `r-2` descendant
law but, wherever the exact-two-deletion rule allows it, spends both
deletions away from a chosen target region instead of at it. It is the
optimistic mirror of
[the balanced adversarial companion](../balanced-adversarial-2-gap/README.md):
where that companion destroys the target child whenever possible, this one
preserves it whenever possible. Its full definition and role as the
optimistic endpoint of the balanced family are in [`model.md`](model.md).

Proved properties study a *mixture*: at each filter, a locally relevant
lineage independently becomes an adversarial parent (destroys its target
child) or a protective parent (preserves it), isolating how much of the
balanced-random companion's local loss comes from the random-placement
penalty itself, as opposed to genuine adversarial pressure.

## Short-Name Registry

| Short Name | File |
|---|---|
| Fixed-Cohort Survival Under Adversarial/Protective Parent Mixing | [properties/fixed-cohort-survival-adversarial-protective-mixing.md](properties/fixed-cohort-survival-adversarial-protective-mixing.md) |
| Growing Square Windows Under Adversarial/Protective Parent Mixing | [properties/growing-square-window-adversarial-protective-mixing.md](properties/growing-square-window-adversarial-protective-mixing.md) |
| Head Recurrence Under Adversarial/Protective Parent Mixing | [properties/head-recurrence-adversarial-protective-mixing.md](properties/head-recurrence-adversarial-protective-mixing.md) |

## Shared Premises

The square-window property assumes a quadratic eligible-supply premise
(`B(Q) \asymp C_0 Q^2`) and position-blind, independent adversarial-label
assignment. The head-recurrence property additionally assumes bounded-below
head availability, and, for the divergent (infinitely-often) direction,
independence or adequate weak cross-layer mixing between head events. These
are premises about a constructed model, not facts about the real sieve; see
the [parent README](../README.md#scope-contract).
