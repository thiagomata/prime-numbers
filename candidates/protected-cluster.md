# Protected Cluster

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Empirical status:** COUNTEREXAMPLE TO THE ALL-TRANSITIONS STRENGTHENING —
the condition fails at `(5,7)` in 1 of 186 measured transitions. The stated
infinitely-many hypothesis remains open; measured clusters later grow to
`248`. See “Empirical Counterexample.”

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

## Empirical Counterexample (window scale, measured)

The candidate stress-test (`candidates/analysis/measure_candidates.py`,
186 transitions: dense p<=991 + sparse every-100th-prime to p~19000, full window
`[q,q^2)`) found one transition where the sufficient condition does not hold:

- **(p,q) = (5,7):** the window is `[7,49)`. The pre-filter 2-gap starts
  (coprime to `{2,3}`) are `11,17,23,29,35,41`. Consecutive differences are all
  `6`, so no two starts lie within a sub-window of width `< p = 5`. Thus
  `max_cluster_in_width_p = 1`: there is no protected cluster of two
  endpoint-disjoint 2-gaps in any width-`<5` interval.

This refutes the stronger claim that candidate #3's condition holds at every
transition. It does not refute the stated main hypothesis, which asks only for
success at infinitely many transitions. It also does not imply that survival
fails at `(5,7)`: survival still holds (`surviving = 4`) via the local-surplus
condition (#2, `surplus = 4 > 0`). The smallest clean transition is exactly
the regime where evenly spaced 2-gaps (all differences `6`, forced by filter
`3`) defeat the width-`<p` cluster requirement.

### Across the full measured range (p to ~19000)

The condition `max_cluster_in_width_p >= 2` holds in **185/186** transitions;
`(5,7)` is the sole failure. At large p the cluster size grows large — the max
observed `max_cluster_in_width_p` is **248** — so tight clusters of many 2-gaps
are abundant once the window is non-trivial. The single small-window failure
does not recur at scale.

### What this does and does not establish

- **Does:** show that protected clusters of two or more endpoint-disjoint
  2-gaps within width-`<p` occur in 185/186 measured transitions and become
  large in the sampled range. This supports, but does not establish, an
  eventual cluster-existence conjecture.
- **Does not:** remove the `(5,7)` counterexample—the all-transitions
  strengthening is false. Handling that transition by candidate #2 proves
  survival there but does not prove candidate #3. The finite window-scale run
  also does not prove that protected clusters occur infinitely often, which
  is candidate #3's actual main hypothesis.

## Strategic assessment after empirical review

This is a genuine one-layer mechanism rather than a restatement of survival:
it converts geometric separation of filter shots into spare local capacity.
The sole small-stage failure is harmless for any “all sufficiently large
stages” version, but the data does not prove that eventual statement.

Proof priority is medium. A useful next lemma would generalize the two-gap
cluster argument to `C` endpoint-disjoint starts and compare `C` with the exact
number of accepted shots in the same interval. That formulation connects
directly to the stronger shot-spacing candidate while avoiding a special
dependence on 2-gaps in the statement of the filter-distribution bound.
