# Controlled Merge Run

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved under the stated projection.

**Empirical status:** DEFERRED (UNMEASURED) — composite; one ingredient (#4 window-linear) measured, the other (#5 `D_max,old`) is whole-period. See "Empirical status: not measured this pass".

## Candidate Hypothesis

Project the expanded old stage to its cyclic 2-gap starts. Assume:

- later filtering creates no new 2-gaps, so post-filter starts form a nonempty
  subset of the lifted old starts;
- every cyclic run of consecutively deleted old starts has length at most `R_p`;
- the largest old spacer is `D_max_old`;
- for infinitely many transitions,

```math
(R_p+1)D_{max,old}<q^2-q-2.
```

## Why It Is Sufficient

Deleting a run of `r` consecutive starts merges exactly `r+1` adjacent old
spacers. With `r<=R_p`, every post-filter spacer satisfies

```math
D_{max,new}\le(R_p+1)D_{max,old}.
```

The candidate inequality therefore implies the bounded post-merge spacer
condition, forcing a surviving start inside the square-safe window.

## Established Inputs

- [Stable absence/no new 2-gaps](../properties/sieve-sequence/absence-of-two-gaps-is-stable.md)
- [Exact copy-index filtering](../properties/sieve-sequence/copy-index-filter-frequency.md)

## Limitation

Both quantitative inputs are open: old spacers may already be large, and the
modular filter may delete long consecutive runs in the 2-gap-start ordering.
Bounding ordinary gap-merge arity is not automatically the same as bounding
these deleted-start runs.

## Empirical status: not measured this pass

This candidate composes the bounded-deletion-run bound (#4) with the
old-spacer bound (#5). The first ingredient (#4's `max_cons_destroyed_run`) was
measured (flat, max 2 — see `bounded-consecutive-destruction.md`); the second
(#5's `D_max,old`) is whole-period and was not. So the composite quantity
`(R_p+1) D_max,old` cannot be evaluated from window data alone. Deferred to a
deeper (whole-period) pass.

## Strategic assessment after empirical review

This candidate is a clean deterministic composition, but it inherits two
different proof burdens. The favorable window-linear data for #4 does not
establish its cyclic deletion-run premise, while the global old-spacer factor
from #5 is entirely unmeasured and may dominate the inequality.

Proof work on #6 should therefore be deferred until at least one component is
understood independently. If a small cyclic run bound can be proved, the more
promising refinement is to multiply it by a **local** old-spacer bound near the
future head rather than by the worst spacer in the entire period.
