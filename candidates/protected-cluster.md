# Protected Cluster

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Candidate Hypothesis

For infinitely many transitions installing `p`, there is an integer-coordinate
interval `I` contained in `[q,q^2)` and at least two endpoint-disjoint
pre-filter 2-gaps whose four endpoints all lie in `I`, with

```math
\operatorname{width}(I)<p.
```

## Why It Is Sufficient

Two different multiples of `p` are at least `p` apart. An interval of width
strictly below `p` therefore contains at most one filter hit. Post-3 endpoint
isolation means that hit can destroy at most one of the two 2-gaps. At least
one complete pair survives inside `W_q` and is square-safe.

More generally, a cluster containing `C` endpoint-disjoint 2-gaps survives if
the interval contains fewer than `C` accepted filter hits.

## Established Inputs

- [2-gap isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

The real open condition is recurring local cluster existence. Global 2-gap
counts and minimum separation do not place two gaps close together inside the
safe window, and a cluster reduced to one survivor may need reconstruction at
the next stage.
