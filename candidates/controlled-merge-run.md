# Controlled Merge Run

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved under the stated projection.

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
