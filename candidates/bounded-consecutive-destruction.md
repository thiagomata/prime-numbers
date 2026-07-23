# Bounded Consecutive Destruction

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved from the stated ordering.

## Candidate Hypothesis

Order the pre-filter 2-gap starts cyclically. Suppose the transition destroys
at most `R_p` consecutive starts in that ordering, and `W_q` contains at least
`R_p+1` consecutive ordered starts whose two endpoints all lie in `W_q`.

Assume this combined condition holds at infinitely many stages.

## Why It Is Sufficient

If every one of the `R_p+1` local starts were destroyed, they would form a run
of more than `R_p` consecutive destroyed 2-gap starts, contradicting the run
bound. Hence at least one remains in `W_q` after filtering.

The run is a run of destroyed 2-gap starts, not a run of arbitrary removed
accepted values. Those are different orderings and cannot be substituted.

## Established Inputs

- [2-gap isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
- [Copy-index filter frequency](../properties/sieve-sequence/copy-index-filter-frequency.md)

## Limitation

Neither the destruction-run bound nor the required local block is currently
proved. A global bound on the number of deletions does not bound their longest
consecutive run among 2-gap starts.
