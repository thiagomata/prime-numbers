# Bounded Cyclic Destruction Run Two

**Status:** Refuted exact auxiliary statement around candidate #4.

## Refuted Statement

At every transition after filter `3`, the longest cyclic run of consecutive
pre-filter 2-gap starts destroyed by the new prime filter has length at most
two:

```math
R_r\le 2.
```

This proposed constant bound is false.

## Exact Counterexample

Take future head `Q=101` and install filter

```math
r=23.
```

Before that filter, the installed primes are

```math
2,3,5,7,11,13,17,19,
```

with exact period

```math
M=2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17\cdot19
=9699690.
```

The period contains `378675` cyclic 2-gap starts. In their cyclic order, three
consecutive starts are

```math
3315701,qquad3315749,qquad3315839.
```

Their start residues modulo `23` are respectively

```math
21,qquad0,qquad21.
```

A 2-gap start `x` is destroyed by filter `23` exactly when

```math
x\equiv0\pmod {23}
\qquad\text{or}\qquad
x+2\equiv0\pmod {23}.
```

Thus all three consecutive starts are destroyed: the middle start is `0`
modulo `23`, while the first and third are `-2` modulo `23`. The two preceding
starts `3315659,3315677` and the two following starts `3315857,3315881` are
not destroyed, so this is an exact run of length three. Therefore

```math
R_{23}\ge3,
```

which refutes the universal bound `R_r<=2`.

## Scope

This counterexample does not refute candidate #4's main hypothesis. That
hypothesis permits a stage-dependent bound `R_r` and asks that a square-safe
window contain at least `R_r+1` consecutive starts at infinitely many stages.
It refutes only the proposed constant shortcut `R_r<=2`.

The variable `R_r` is always finite on a finite period, so a useful replacement
must give an independent upper bound small enough to combine with the local
window population. Merely defining `R_r` as the observed maximum supplies no
mechanism.

## Reproduction Source

- `data/candidates/lineage-Q101.csv`, row `Q=101`, `r=23`, records
  `cyclic_run_full_period=3`.
- `python/src/sieve_sequence/lineage.py::cyclic_destroyed_run_full_period`
  defines the exact full-period cyclic quantity.

## Reconsideration Condition

Do not retry the universal constant `R_r<=2`.

A materially different route may seek:

- a larger proved universal constant;
- a stage-dependent bound with growth controlled relative to the number of
  local consecutive starts; or
- an eventual or infinitely-often bound paired with an independently proved
  local-block lower bound.
