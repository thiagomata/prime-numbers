# Sieve-Sequence Mathematical Properties

This directory collects strong sieve-sequence properties as independent
mathematical reference notes. Each file states one claim, proves or derives it,
explains what it enables, and marks the exact boundary of the result.

These notes are not publication articles and do not claim Stainless
verification unless a file explicitly says otherwise.

## Recommended Reading Order

1. [Exact Global 2-Gap Count](exact-global-two-gap-count.md)
   - Direct non-recursive product for the complete cyclic count.
2. [Exact Batched 2-Gap Survival](exact-batched-two-gap-survival.md)
   - Applies any finite range of new prime filters in one CRT calculation.
3. [Exact Filter Frequency Across Repeated Copies](copy-index-filter-frequency.md)
   - Locates the two forbidden copy-index classes for every new filter.
4. [Isolation of 2-Gaps After Filtering by 3](two-gap-isolation-after-filter-three.md)
   - Proves that one removed value destroys at most one 2-gap.
5. [Exact Accepted Local Filter Strikes](exact-accepted-local-filter-strikes.md)
   - Counts only multiples that survived the previous filters.
6. [Sharp Local 2-Gap Survival Threshold](sharp-local-two-gap-survival-threshold.md)
   - Gives the one-transition condition `G_local>A(p,q)`.
7. [Safe-Window 2-Gaps Certify Twin Primes](safe-window-two-gaps-certify-twin-primes.md)
   - Explains the strict square-bound certification.
8. [Reverse-Engineered Initial Scenario for an Eventual Head 2-Gap](reverse-engineered-eventual-head-scenario.md)
   - Works backward from a head 2-gap to one finite batch-compatible copy.
9. [Candidate Property: Infinitely Many Perfect Sieve Scenarios](infinite-perfect-scenario-property.md)
   - Self-contained statement and expert checklist for the proposed infinitude property.
10. [Global Count Threshold That Forces Local Survival](global-count-forcing-local-survival.md)
   - Gives a rigorous but generally impractical count-only bridge.
11. [Rotation Preserves Cyclic Gap Counts](rotation-preserves-cyclic-gap-counts.md)
   - Separates cyclic invariance from absolute-window placement.
12. [Absence of 2-Gaps Is Stable](absence-of-two-gaps-is-stable.md)
   - Shows that copy-or-merge filtering cannot recreate a missing 2-gap.
13. [Batched Short-Window Discrepancy Boundary](batched-short-window-discrepancy-boundary.md)
    - States exactly what batching proves and what local positivity still needs.

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
