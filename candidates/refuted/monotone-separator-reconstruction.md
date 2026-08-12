# Monotone Separator Reconstruction

**Status:** REFUTED
**Scope:** stronger transition laws proposed while studying candidate #18

## Statement

Let `P(Q,r)` be the number of qualifying adjacent 2-gap-start pairs in the
fixed square-safe window `W_Q`, and let `D(Q,r)` be the size of a maximum
disjoint matching on those qualifying pairs. Let `H(Q,r)` be the number of
destroyed starts when the next filter is installed.

The following universal transition statements are false:

```text
P(Q,next(r)) >= P(Q,r)
D(Q,next(r)) >= D(Q,r)
P(Q,next(r)) >= P(Q,r) - H(Q,r)
```

These were natural monotone-reconstruction guesses: surviving old edges stay,
deleted starts may reconnect neighbors, and the next threshold is no smaller.
But the losses can exceed those naive expectations.

## First Counterexample

The first measured failure is:

```text
Q = 17
r = 5 -> 7
P: 44 -> 8
D: 22 -> 8
H = 18
```

Therefore:

```text
8 < 44
8 < 22
8 < 44 - 18 = 26
```

So all three universal statements above are refuted.

## What Remains True

This refutation does **not** refute candidate #18 itself.

What survives is the weaker sharp attrition theory already promoted into the
property catalog:

```text
P_new >= P_old - 2H
D_new >= D_old - H
```

For the same counterexample,

```text
8 = 44 - 2*18
8 >= 22 - 18
```

so the proved coefficient-2 raw bound and coefficient-1 matching bound remain
consistent, and the first one is sharp here.

## Reproduction Source

This counterexample family is documented in:

- [candidate #18](../redundant-close-pair-capacity.md)
- [candidate catalog](../README.md)
- [separator-dynamics ticket](../../tickets/done/evaluate-conditioned-separator-dynamics-2026-07-27.md)

The finite sweep that found it covered 53 heads, 1,837 layers, and 1,784
consecutive-layer transitions.

## Reconsideration Condition

Do not retry these exact monotone universal forms.

A new note would be justified only if the statement changes in a material way,
for example:

- an explicit attrition term stronger than the false versions but independent
  of the observed output;
- an eventual-only formulation;
- a density or lower-envelope statement instead of transition monotonicity.
