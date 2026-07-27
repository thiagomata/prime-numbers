# Sieve-Sequence Mathematical Properties

This directory collects strong sieve-sequence properties as independent
mathematical reference notes. Each file states one claim, proves or derives it,
explains what it enables, and marks the exact boundary of the result.

These notes are not publication articles and do not claim Stainless
verification unless a file explicitly says otherwise.

## Recommended Reading Order

1. [Exact Global 2-Gap Count](exact-global-two-gap-count.md)
   - Direct non-recursive product for the complete cyclic count.
2. [Exact Global `(2,4,2)` Two-Gap Cluster Count](exact-global-two-gap-cluster-count.md)
   - Proves the complete-cycle recurrence `C_next=(r-4)C` and its closed
     product while keeping short-window placement explicitly open.
3. [Exact Batched 2-Gap Survival](exact-batched-two-gap-survival.md)
   - Applies any finite range of new prime filters in one CRT calculation.
4. [Exact Filter Frequency Across Repeated Copies](copy-index-filter-frequency.md)
   - Locates the two forbidden copy-index classes for every new filter.
5. [Isolation of 2-Gaps After Filtering by 3](two-gap-isolation-after-filter-three.md)
   - Proves that one removed value destroys at most one 2-gap.
6. [Exact Accepted Local Filter Strikes](exact-accepted-local-filter-strikes.md)
   - Counts only multiples that survived the previous filters.
7. [Sharp Local 2-Gap Survival Threshold](sharp-local-two-gap-survival-threshold.md)
   - Gives the one-transition condition `G_local>A(p,q)`.
8. [Safe-Window 2-Gaps Certify Twin Primes](safe-window-two-gaps-certify-twin-primes.md)
   - Explains the strict square-bound certification.
9. [Reverse-Engineered Initial Scenario for an Eventual Head 2-Gap](reverse-engineered-eventual-head-scenario.md)
   - Works backward from a head 2-gap to one finite batch-compatible copy.
10. [Candidate Property: Infinitely Many Perfect Sieve Scenarios](infinite-perfect-scenario-property.md)
   - Self-contained statement and expert checklist for the proposed infinitude property.
11. [Global Count Threshold That Forces Local Survival](global-count-forcing-local-survival.md)
    - Gives a rigorous but generally impractical count-only bridge.
12. [Rotation Preserves Cyclic Gap Counts](rotation-preserves-cyclic-gap-counts.md)
    - Separates cyclic invariance from absolute-window placement.
13. [Absence of 2-Gaps Is Stable](absence-of-two-gaps-is-stable.md)
    - Shows that copy-or-merge filtering cannot recreate a missing 2-gap.
14. [Batched Short-Window Discrepancy Boundary](batched-short-window-discrepancy-boundary.md)
    - States exactly what batching proves and what local positivity still needs.
15. [Fixed-k Shot Spacing: Monotonicity and Eventual Stability](stable-small-k-shot-spacing.md)
    - Proves that deleting accepted values cannot decrease the minimum
      `k`-span, and that for every fixed `k` the span eventually stabilizes at
      `D(k)`, the minimum diameter of an admissible `k`-point pattern. It also
      proves the exact profile
      `D(2..14)=(2,6,8,12,16,20,26,30,32,36,42,48,50)` and a
      complete-period two-gap cluster of enclosing length `8`.
16. [Bounded Pair Separation Gives the k=2 Interval Premise](interval-premise-from-pair-existence.md)
    - Proves that two complete 2-gaps enclosed by an interval shorter than
      `2r` satisfy candidate #14's `k=2` interval premise. Pair existence alone
      does not imply the required upper bound on their separation.
17. [A Local Count Forces the k=2 Shot-Capacity Premise](local-count-forces-k2-shot-capacity.md)
    - Gives the exact ordered-point threshold
      `G_r(W_Q) >= floor((Q^2-Q-3)/(2r-2))+2` that forces a sufficiently close
      pair, while leaving the required conditioned local-count bound open.
18. [Exact Seven-Layer Capacity Floor](exact-seven-layer-capacity-floor.md)
    - Uses the three 2-gap-start classes modulo `30` to prove
      `rho(Q,7)>1` for every integer `Q>=17`, while leaving the later-layer
      lower-envelope theorem open.
19. [Local Density Forces a Close-Pair Matching Bound](local-density-forces-close-pair-matching.md)
    - Converts post-filter-3 local population surplus into explicit lower
      bounds on qualifying consecutive pairs and pairwise disjoint `k=2`
      survivor certificates.
20. [Filtering Attrition Bound for Raw Close Pairs](filtering-attrition-bound-raw-close-pairs.md)
    - Proves the sharp transition bound `P_new>=P_old-2H`: deleting one
      2-gap start can remove at most its two incident qualifying path edges.
21. [Filtering Attrition Bound for Close-Pair Matchings](filtering-attrition-bound-close-pair-matching.md)
    - Proves the sharp transition bound `D_new>=D_old-H`: deleting one start
      can destroy at most one edge of a fixed disjoint matching.
22. [Harmful Residue Capacity After Filter Three](harmful-residue-capacity-after-filter-three.md)
    - Uses the common `5 modulo 6` phase of post-3 2-gap starts to bound each
      harmful class modulo `r` by `floor((Q^2-Q-3)/(6r))+1`, yielding a direct
      one-layer survival threshold asymptotic to `Q^2/(3r)`.
23. [Two-Class Survival From Residue Collision Energy](two-class-survival-from-collision-energy.md)
    - Bounds the two harmful classes by the residue-histogram second moment,
      identifies that moment with same-residue ordered pairs, and rewrites its
      off-diagonal part as four-point autocorrelations at shifts `6rh`.
24. [Weighted Collision-Energy Chain Survival](weighted-collision-energy-chain-survival.md)
    - Unrolls the one-layer energy loss through a complete conditioned chain,
      embeds changing populations as nested weights on one initial set, and
      reduces cumulative energy to stopped centered prime-divisor sums.

## Research Notes

- [Recent Prime-Producing Sieves: A Deep-Dive For The Perfect-Scenario Problem](research/recent-prime-producing-sieves-deep-dive.md)
  - Maps recent Type I/Type II and structured-prime results to the exact
    perfect-scenario proof obligations, including a fixed-seed scale conflict
    and explicit go/no-go criteria.

## Suggested Next Steps

- [A Finite Perfect-Scenario Generator](suggested-next-step-finite-perfect-scenario-generator.md)
  - Defines a sound finite search and certificate format while keeping
    unbounded success explicitly open.

## Status Vocabulary

- **Mathematically proved:** the file contains a complete mathematical proof.
- **Proved conditional implication:** the implication is proved, but its
  antecedent is a separate unresolved requirement.
- **Problem boundary:** proved facts are separated from a specifically stated
  missing theorem; no solution to that missing theorem is claimed.

## Central Dependency Chain

```text
complete-period CRT count
    -> exact batch survival
    -> deterministic allowed copy indices
    -> one finite batch-compatible copy
    -> safe-window prime certification
    -> eventual head 2-gap
```

The unresolved bridge is not global survival or eventual head mechanics. It is
proving that the allowed copy-index set intersects the safe-window copy-index
interval for an unbounded family of scenarios.

## Related Articles

- [Formal Verification of the Sieve Sequence](../../articles/chapter6/sieve-sequence.md)
- [Sieve Gap Survival: Math-Only Follow-Up](../../articles/draft/draft-sieve-gap-survival-math.md)
- [Local Strike Capacity Exercise](../../articles/draft/exercise-local-safe-window-capacity.md)
