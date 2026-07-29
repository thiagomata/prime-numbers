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
25. [Weighted Deletion Conservation Law](weighted-deletion-conservation-law.md)
    - Proves that weighted signed harmful excess is exactly the multiplicative
      main term minus the final survivor count, so using it alone is circular.
26. [Two-Gap Pair Local Factor By Separation](two-gap-pair-local-factor-by-separation.md)
    - Classifies the four endpoint residues for two separated 2-gaps and gives
      the exact CRT factor according as a prime divides `d`, `d-2`, or `d+2`.
27. [Complete-Period Two-Gap Pair-Correlation Average](complete-period-two-gap-pair-correlation-average.md)
    - Proves exact uniformity after averaging correlation over one complete
      quotient difference period and records the short-prefix boundary.
28. [Fourier Bound For Two-Gap Correlation Prefixes](fourier-two-gap-correlation-prefix-bound.md)
    - Factors the complete CRT spectrum, computes exact conductor moments, and
      bounds complete-origin correlation prefixes.
29. [Localized Two-Gap Correlation: Fourier Boundary](localized-two-gap-correlation-fourier-boundary.md)
    - Derives the square-window rectangle formula and proves that generic Young
      convolution bounds retain the unusable complete-period population.
30. [Short-Interval Localization Destroys Prime Conductor Decay](short-interval-localization-destroys-prime-conductor-decay.md)
    - Shows that a sufficiently short interval moves exactly the fraction
      `1-1/p` of localized energy into characters nontrivial at `p`, rather
      than preserving the complete-set fraction `2/p`.
31. [Black-Box Large Sieve Does Not Fit The Weighted Collision Budget](black-box-large-sieve-does-not-fit-weighted-collision-budget.md)
    - Proves that even the optimistic fixed-set large-sieve scale is too large
      to certify candidate #21 after inserting the exact survival weights.
32. [First-Deletion Pair Terminal Energy](first-deletion-pair-terminal-energy.md)
    - Splits weighted collision energy by first deletion, isolates a negative
      balanced terminal term, and solves the sharp harmless-class variance
      envelope while recording the symmetric-capacity loop.
33. [Two Endpoint Observables Separate Harmful Excess And Imbalance](two-endpoint-observables-separate-harmful-excess-and-imbalance.md)
    - Uses unsigned and signed endpoint observables to separate total harmful
      excess from left/right imbalance; candidate #13 controls endpoint
      sampling, while candidate #23 supplies the separate accepted-strike
      density target needed by #21.
34. [Orthogonal Residue-Energy Decomposition After A Two-Class Filter](orthogonal-residue-energy-decomposition-after-two-class-filter.md)
    - Splits full collision energy exactly into harmless-class dispersion,
      squared total harmful excess, and squared left/right imbalance, with no
      linear cross terms, isolating candidate #22's role.
35. [Accepted-Strike Density As A Möbius Boundary Sum](accepted-strike-density-boundary-decomposition.md)
    - Maps accepted strikes to a scaled coprime interval and decomposes their
      centered density exactly into two signed boundary sums. The
      triangle-inequality bound grows like `2^omega(P)`, isolating weighted
      boundary cancellation as candidate #23's missing theorem.
36. [Endpoint Density Contracts Accepted-Strike Discrepancy](endpoint-density-contracts-strike-discrepancy.md)
    - Uses post-3 endpoint isolation to prove `2N<=A`, removes the
      endpoint-to-anchor ratio from candidate #23, and separates the #13 and
      #23 harmful-excess errors through Young's inequality.
37. [Weighted Composition Of Endpoint And Strike-Density Errors](weighted-scalar-error-composition.md)
    - Uses weighted Minkowski to combine #13 and #23 into the sharp aggregate
      scalar budget `(sqrt(E_beta)+sqrt(E_D))^2+E_Delta`, leaving candidate
      #22 the exact remaining allowance required by #21.
38. [Accepted-Strike Error Is A Positive Quadratic Variation](accepted-strike-quadratic-variation.md)
    - Expands candidate #23's weighted squared boundary recurrence into
      adjacent variation, terminal mass, and strictly positive interior mass,
      proving that the linear strike telescope cannot supply the needed upper
      bound after squaring.
39. [Prime-Square Window Boundary Residue Formula](prime-square-window-boundary-residue-formula.md)
    - Rewrites each boundary summand as
      `mu(d)([Q]_d-[Q^2]_d)/d`, identifies the terms killed by `d|(Q-1)`, and
      gives an exact `Q=19` sign-change counterexample to universal sign or
      sign preservation under later filters.
40. [Harmless Energy As A Fixed-Set Pair Correlation](harmless-energy-fixed-set-pair-form.md)
    - Rewrites candidate #22 as a post-deletion ordered-pair kernel on `S_0`,
      proves `U_i=V_{r_i}(S_{i+1})-2M_i^2/(r_i(r_i-2))`, and exposes the
      additional negative centering beyond candidate #21's existing
      telescope.
41. [Complete-Period Uniformity Of Harmless 2-Gap Classes](complete-period-harmless-class-uniformity.md)
    - Proves that every harmless class has the same CRT count and hence
      complete-period harmless energy is zero; complete blocks cancel exactly,
      leaving candidate #22 entirely as a short-prefix localization problem.
42. [Harmless Energy As Spectral Excess Above The Two-Class Floor](harmless-energy-spectral-excess.md)
    - Expresses `U_i` as nontrivial Fourier mass minus the sharp floor forced
      by the two empty harmful classes, and shows why subtracting that local
      floor does not repair the known generic Fourier localization scale.
43. [Harmless-Class Counts As Translated CRT Fibers](harmless-class-crt-translated-fibers.md)
    - Expresses every harmless residue count as an interval sum of one common
      prior-filter CRT word at an inverse-modulus phase, proves those phases
      are spaced on the order of `P/r`, and isolates why generic Parseval or
      large-sieve sampling still retains the complete-period scale.
44. [Centered Inverse-Phase Gram Matrix](centered-inverse-phase-gram-matrix.md)
    - Evaluates the harmless-class mean projection on every inverse-phase
      Fourier mode, gives a closed geometric formula for its phase sum, and
      exposes the exact cross-frequency Gram kernel that a centered spectral
      proof of candidate #22 must control.
45. [Centered Phase Operator Norm Boundary](centered-phase-operator-norm-boundary.md)
    - Proves the inverse phases have orthogonal full-Fourier rows and that
      harmless-class centering leaves sharp operator norm `sqrt(P)`, so a
      black-box norm estimate returns exactly to full-shift Parseval scale.
46. [Exact-Conductor Phase-Block Operator Bound](exact-conductor-phase-block-operator-bound.md)
    - Replaces the full period norm inside conductor `q` by the phase
      multiplicity bound `q mu_q<r+2q`, then shows that triangle recombination
      loses this gain through an oversized square-root divisor sum.
47. [Centered Ramanujan Cross-Conductor Geometry](centered-ramanujan-cross-conductor-geometry.md)
    - Expresses primitive conductor blocks through Ramanujan row kernels and
      gives their exact centered cross-block trace; an exact `P=30,r=7`
      example refutes orthogonality and uniformly small unweighted coherence.
48. [Accepted-Strike Divisor Activation Kernel](accepted-strike-divisor-activation-kernel.md)
    - Collapses candidate #23's exponential divisor-pair quadratic form to
      `m+1` signed activation-shell sums and gives the exact nonnegative
      positive-semidefinite kernel induced by the chain weights.
49. [Accepted-Strike CRT Lift-Index Transform](accepted-strike-crt-lift-index-transform.md)
    - Splits each newly activated residue by its bounded CRT lift index,
      cancels the complete old boundary error, and rewrites candidate #23's
      budget as a weighted mean square of explicit Möbius transforms.
50. [Accepted-Strike Summatory Coprime Remainder](accepted-strike-summatory-coprime-remainder.md)
    - Identifies the lift-index transform exactly as a dilation remainder of
      the finite-sieve summatory coprime count, classifying the remaining #23
      estimate as new weighted analytic distribution input.
51. [Accepted-Strike Cross-Layer CRT Orthogonality](accepted-strike-cross-layer-crt-orthogonality.md)
    - Proves exact complete-period orthogonality and norms for the centered
      layer strike observables, then shows that their Bessel bound retains the
      full final-period normalization rather than the local-window scale.
52. [Accepted-Strike Localized Layer Gram Matrix](accepted-strike-localized-layer-gram-matrix.md)
    - Computes every local Gram entry from accepted counts and strike
      discrepancies, reducing #23 to a finite spectral problem and showing
      that the generic trace bound is only per-layer Cauchy in matrix form.
53. [Accepted-Strike First-Deletion Variance Identity](accepted-strike-first-deletion-variance-identity.md)
    - Factors the local Gram matrix by first-deletion class and identifies the
      exact negative weighted variance lost by generic population and trace
      bounds.
54. [Accepted-Strike Active Two-Class Variance Identity](accepted-strike-active-two-class-variance-identity.md)
    - Proves `D_i^2=A_i G_(ii)-H_i A_(i+1)` and shows that retaining only the
      compulsory first-deletion separation rearranges the strike energy
      instead of upper-bounding it.
55. [Accepted-Strike First-Deletion Coordinate Reindexing](accepted-strike-first-deletion-coordinate-reindexing.md)
    - Reindexes the complete deletion-vector variance by layer and proves that
      the entire first-deletion spectral identity collapses exactly to the
      original weighted strike energy without new arithmetic input.
56. [Endpoint-Observable Joint Capacity Envelope](endpoint-observable-joint-capacity-envelope.md)
    - Solves the exact finite-population maximum for candidate #13's unsigned
      endpoint bias and signed imbalance, showing that capacity alone permits
      extremal concentration in one endpoint orientation.
57. [Endpoint Capacity Cannot Certify The Collision Budget](endpoint-capacity-cannot-certify-collision-budget.md)
    - Gives a one-layer capacity-admissible configuration whose signed
      endpoint imbalance alone exceeds candidate #21's complete one-layer
      allowance,
      proving that representative residue sampling is essential.
58. [Endpoint Sampling And Strike Density Recombine Into Harmful Residues](endpoint-sampling-strike-density-harmful-residue-bridge.md)
    - Proves that #13's endpoint bias and #23's strike-density error recombine
      exactly into the sum and difference of the two harmful start-residue
      deviations, exposing restricted candidate #12 as the direct scalar
      target.
59. [Pointwise Two-Class Margin Does Not Imply The Collision Budget](pointwise-two-class-margin-does-not-imply-collision-budget.md)
    - Constructs integral residue histograms satisfying candidate #12's full
      pointwise survival margin while violating #21's one-layer scalar
      ellipse, proving that the required local joint quadratic theorem is
      strictly stronger.
60. [Sharp Harmful-Residue Box Inside The Collision Ellipse](sharp-harmful-residue-box-inside-collision-ellipse.md)
    - Proves that the harmful scalar energy is at most
      `2r E^2/(r-2)` under coordinate bounds `|delta_0|,|delta_(-2)|<=E`,
      yielding the sharp stricter one-layer threshold.
61. [Sharp Sixfold-Capacity Harmful-Energy Envelope](sharp-sixfold-capacity-harmful-energy-envelope.md)
    - Combines the exact `6r` one-class capacity with the total local
      population and reduces the sharp harmful scalar maximum to at most three
      feasible endpoint totals.
62. [Sharp Sixfold-Capacity Population-Ratio Threshold](sharp-sixfold-capacity-population-ratio-threshold.md)
    - Solves the capacity envelope exactly: it fits the one-layer harmful
      scalar budget precisely when `G/B > rho_*(r)`, where
      `2 < rho_*(r) < 3` and `rho_*(r)` tends to `2`.
63. [Capacity Population-Threshold Hierarchy](capacity-population-threshold-hierarchy.md)
    - Places the one-layer harmful scalar threshold strictly between #19's
      ordinary capacity level and #14's close-pair count level, and gives the
      exact range `B < 1/(rho_*(r)-2)` where #19's floor is locally sufficient.
64. [Late-Layer Sixfold Floor Controls Harmful Energy](late-layer-sixfold-floor-controls-harmful-energy.md)
    - Proves that #19's ordinary floor already clears the one-layer harmful
      scalar threshold when `Q^2-Q-3 < 3r(r-1)`, in particular throughout
      the explicit range `r >= Q/sqrt(3)+1`.
65. [One-Layer Harmful Ellipses Do Not Compose](one-layer-harmful-ellipses-do-not-compose.md)
    - Proves that strict success against every one-layer scalar allowance does
      not imply #21's smaller global weighted allowance, isolating a genuinely
      aggregate harmful-energy theorem as the missing input.
66. [Weighted Harmful-Excess Energy Is Already Terminal](weighted-harmful-excess-energy-is-terminal.md)
    - Proves the conditioned-chain lower bound
      `E_b >= (T-N_m)^2/(2W_-)` with `W_-<W`, so the harmful-excess component
      alone being below candidate #21's global allowance already forces
      `N_m>0`. It also identifies `E_b` exactly as a weighted quadratic
      variation of the normalized realized population.
67. [Integral Population Profiles Attain the Harmful-Energy Threshold](integral-population-profiles-attain-harmful-energy-threshold.md)
    - Constructs, for every fixed prime chain, arbitrarily scaled integral
      strictly decreasing extinction profiles attaining
      `E_b=T^2/(2W_-)`. Therefore integrality, monotonicity, and the exact
      population recurrence cannot improve candidate #24 without genuine CRT
      deletion geometry.
68. [Harmful-Excess Energy Has an Exact Stability Decomposition](harmful-excess-energy-exact-stability-decomposition.md)
    - Completes the weighted square around the unique endpoint-constrained
      minimizer. The excess above `(T-N_m)^2/(2W_-)` is exactly a positive
      weighted distance from that profile, isolating the possible CRT
      stability-gap interface without claiming an upper bound for `E_b`.
69. [Harmful Capacity Separates the Energy Minimizer](harmful-capacity-separates-energy-minimizer.md)
    - Computes the Cauchy minimizer's exact deletion masses and converts every
      violated proved harmful-class capacity into the explicit extinction gap
      `(K_i^star-C_i)_+^2/D_i`. This enlarges the possible #24 certificate but
      remains a lower bound, not an upper estimate for actual `E_b`.
70. [Sharp Harmful-Capacity Excess Envelope](sharp-harmful-capacity-excess-envelope.md)
    - Projects property #61's exact capacity interval onto `b_i^2`, giving the
      sharp one-layer endpoint maximum and the valid aggregate upper bound
      `E_b<=U_cap`. Combined with #69, `U_cap<T^2/(2W_-)+Gamma_cap` forces
      survival, but proving that terminal inequality remains open. Its local
      threshold is still `N_i/B_i>rho_*(r_i)>2`, so improvement over #19 must
      be genuinely cross-layer.
71. [Paired Harmful-Excess CRT Orthogonality Has Primorial Scale](paired-harmful-excess-crt-orthogonality-has-primorial-scale.md)
    - Proves exact complete-block cancellation, pairwise cross-layer
      orthogonality, and norm `Rd_i(2/r_i)(1-2/r_i)` for candidate #24's
      paired harmful-excess observables. Direct Bessel gives
      `E_b<=LRd_m/(r_0-2)`, retaining the primorial-scale final class count;
      progress therefore requires localized interval correlations or
      coefficient-sensitive cancellation.
72. [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
    - Applies Bessel to a prefix over its intermediate native CRT period and
      intersects that joint budget sharply with property #70's coordinate
      capacities by an explicit greedy linear program. The optimized envelope
      always improves or matches `U_cap`, with an exact normalized-capacity
      criterion for strict gain, but universal clearance of the extinction
      threshold remains open.
73. [Native-Period Capacity Overflow Quantifies the Hybrid Gain](native-period-capacity-overflow-quantifies-hybrid-gain.md)
    - Defines the normalized prefix-capacity overflow `e_k`, proves it is the
      exact mass rejected by native-period Bessel, and bounds the resulting
      gain between the smallest and largest prefix energy coefficients times
      `e_k`. This gives a simpler sufficient survival comparison while leaving
      a lower bound for the overflow at the required scale open.

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

The complete cross-repository taxonomy is defined in the
[Research Vocabulary](../../VOCABULARY.md). The labels below are the subset
used most often by this property catalog.

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
