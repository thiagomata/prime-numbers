# Sieve-Sequence Mathematical Properties

This directory collects strong sieve-sequence properties as independent
mathematical reference notes. Each file states one claim, proves or derives it,
explains what it enables, and marks the exact boundary of the result.

These notes are not publication articles and do not claim Stainless
verification unless a file explicitly says otherwise.

## Short-Name Registry

Every property has a short, distinctive name used whenever it is cited from
outside its own file (headers, prose, tables) — never a bare number. The full
title lives only in the property's own file `# H1`; the short name below is
what every other document should use. This table is the canonical registry;
nothing else in the repo should be treated as authoritative for the mapping.

| Short Name | Full Title | File |
|---|---|---|
| Global 2-Gap Count | Exact Global 2-Gap Count | [exact-global-two-gap-count.md](exact-global-two-gap-count.md) |
| Global 2-Gap Cluster Count | Exact Global `(2,4,2)` Two-Gap Cluster Count | [exact-global-two-gap-cluster-count.md](exact-global-two-gap-cluster-count.md) |
| Batched 2-Gap Survival | Exact Batched 2-Gap Survival | [exact-batched-two-gap-survival.md](exact-batched-two-gap-survival.md) |
| Copy-Index Filter Frequency | Exact Filter Frequency Across Repeated Copies | [copy-index-filter-frequency.md](copy-index-filter-frequency.md) |
| 2-Gap Isolation | Isolation of 2-Gaps After Filtering by 3 | [two-gap-isolation-after-filter-three.md](two-gap-isolation-after-filter-three.md) |
| Accepted Local Strikes | Exact Accepted Local Filter Strikes | [exact-accepted-local-filter-strikes.md](exact-accepted-local-filter-strikes.md) |
| Local Survival Threshold | Sharp Local 2-Gap Survival Threshold | [sharp-local-two-gap-survival-threshold.md](sharp-local-two-gap-survival-threshold.md) |
| Safe-Window Certification | Safe-Window 2-Gaps Certify Twin Primes | [safe-window-two-gaps-certify-twin-primes.md](safe-window-two-gaps-certify-twin-primes.md) |
| Reverse-Engineered Head Scenario | Reverse-Engineered Initial Scenario for an Eventual Head 2-Gap | [reverse-engineered-eventual-head-scenario.md](reverse-engineered-eventual-head-scenario.md) |
| Count-Forces-Survival Threshold | Global Count Threshold That Forces Local Survival | [global-count-forcing-local-survival.md](global-count-forcing-local-survival.md) |
| Rotation Invariance | Rotation Preserves Cyclic Gap Counts | [rotation-preserves-cyclic-gap-counts.md](rotation-preserves-cyclic-gap-counts.md) |
| Absence Stability | Absence of 2-Gaps Is Stable | [absence-of-two-gaps-is-stable.md](absence-of-two-gaps-is-stable.md) |
| Batched Discrepancy Boundary | Batched Short-Window Discrepancy Boundary | [batched-short-window-discrepancy-boundary.md](batched-short-window-discrepancy-boundary.md) |
| Fixed-k Shot Spacing | Fixed-k Shot Spacing: Monotonicity and Eventual Stability | [stable-small-k-shot-spacing.md](stable-small-k-shot-spacing.md) |
| Pair Separation Premise | Bounded Pair Separation Gives the k=2 Interval Premise | [interval-premise-from-pair-existence.md](interval-premise-from-pair-existence.md) |
| Local Count Shot-Capacity Premise | A Local Count Forces the k=2 Shot-Capacity Premise | [local-count-forces-k2-shot-capacity.md](local-count-forces-k2-shot-capacity.md) |
| Seven-Layer Capacity Floor | Exact Seven-Layer Capacity Floor | [exact-seven-layer-capacity-floor.md](exact-seven-layer-capacity-floor.md) |
| Close-Pair Matching Bound | Local Density Forces a Close-Pair Matching Bound | [local-density-forces-close-pair-matching.md](local-density-forces-close-pair-matching.md) |
| Raw Close-Pair Attrition | Filtering Attrition Bound for Raw Close Pairs | [filtering-attrition-bound-raw-close-pairs.md](filtering-attrition-bound-raw-close-pairs.md) |
| Matching Attrition Bound | Filtering Attrition Bound for Close-Pair Matchings | [filtering-attrition-bound-close-pair-matching.md](filtering-attrition-bound-close-pair-matching.md) |
| Post-Filter-3 Harmful Capacity | Harmful Residue Capacity After Filter Three | [harmful-residue-capacity-after-filter-three.md](harmful-residue-capacity-after-filter-three.md) |
| Two-Class Collision Survival | Two-Class Survival From Residue Collision Energy | [two-class-survival-from-collision-energy.md](two-class-survival-from-collision-energy.md) |
| Weighted Chain Survival | Weighted Collision-Energy Chain Survival | [weighted-collision-energy-chain-survival.md](weighted-collision-energy-chain-survival.md) |
| Weighted Deletion Conservation | Weighted Deletion Conservation Law | [weighted-deletion-conservation-law.md](weighted-deletion-conservation-law.md) |
| Pair Local Factor | Two-Gap Pair Local Factor By Separation | [two-gap-pair-local-factor-by-separation.md](two-gap-pair-local-factor-by-separation.md) |
| Pair-Correlation Average | Complete-Period Two-Gap Pair-Correlation Average | [complete-period-two-gap-pair-correlation-average.md](complete-period-two-gap-pair-correlation-average.md) |
| Fourier Correlation Bound | Fourier Bound For Two-Gap Correlation Prefixes | [fourier-two-gap-correlation-prefix-bound.md](fourier-two-gap-correlation-prefix-bound.md) |
| Localized Fourier Boundary | Localized Two-Gap Correlation: Fourier Boundary | [localized-two-gap-correlation-fourier-boundary.md](localized-two-gap-correlation-fourier-boundary.md) |
| Conductor-Decay Destruction | Short-Interval Localization Destroys Prime Conductor Decay | [short-interval-localization-destroys-prime-conductor-decay.md](short-interval-localization-destroys-prime-conductor-decay.md) |
| Large-Sieve Budget Mismatch | Black-Box Large Sieve Does Not Fit The Weighted Collision Budget | [black-box-large-sieve-does-not-fit-weighted-collision-budget.md](black-box-large-sieve-does-not-fit-weighted-collision-budget.md) |
| First-Deletion Terminal Energy | First-Deletion Pair Terminal Energy | [first-deletion-pair-terminal-energy.md](first-deletion-pair-terminal-energy.md) |
| Endpoint Excess-Imbalance Split | Two Endpoint Observables Separate Harmful Excess And Imbalance | [two-endpoint-observables-separate-harmful-excess-and-imbalance.md](two-endpoint-observables-separate-harmful-excess-and-imbalance.md) |
| Orthogonal Residue-Energy Split | Orthogonal Residue-Energy Decomposition After A Two-Class Filter | [orthogonal-residue-energy-decomposition-after-two-class-filter.md](orthogonal-residue-energy-decomposition-after-two-class-filter.md) |
| Möbius Strike-Density Sum | Accepted-Strike Density As A Möbius Boundary Sum | [accepted-strike-density-boundary-decomposition.md](accepted-strike-density-boundary-decomposition.md) |
| Endpoint Discrepancy Contraction | Endpoint Density Contracts Accepted-Strike Discrepancy | [endpoint-density-contracts-strike-discrepancy.md](endpoint-density-contracts-strike-discrepancy.md) |
| Weighted Error Composition | Weighted Composition Of Endpoint And Strike-Density Errors | [weighted-scalar-error-composition.md](weighted-scalar-error-composition.md) |
| Strike-Error Quadratic Variation | Accepted-Strike Error Is A Positive Quadratic Variation | [accepted-strike-quadratic-variation.md](accepted-strike-quadratic-variation.md) |
| Prime-Square Boundary Formula | Prime-Square Window Boundary Residue Formula | [prime-square-window-boundary-residue-formula.md](prime-square-window-boundary-residue-formula.md) |
| Harmless-Energy Pair Correlation | Harmless Energy As A Fixed-Set Pair Correlation | [harmless-energy-fixed-set-pair-form.md](harmless-energy-fixed-set-pair-form.md) |
| Harmless-Class Uniformity | Complete-Period Uniformity Of Harmless 2-Gap Classes | [complete-period-harmless-class-uniformity.md](complete-period-harmless-class-uniformity.md) |
| Harmless Spectral Excess | Harmless Energy As Spectral Excess Above The Two-Class Floor | [harmless-energy-spectral-excess.md](harmless-energy-spectral-excess.md) |
| CRT Fiber Translation | Harmless-Class Counts As Translated CRT Fibers | [harmless-class-crt-translated-fibers.md](harmless-class-crt-translated-fibers.md) |
| Inverse-Phase Gram Matrix | Centered Inverse-Phase Gram Matrix | [centered-inverse-phase-gram-matrix.md](centered-inverse-phase-gram-matrix.md) |
| Phase-Operator Norm Bound | Centered Phase Operator Norm Boundary | [centered-phase-operator-norm-boundary.md](centered-phase-operator-norm-boundary.md) |
| Conductor Phase-Block Bound | Exact-Conductor Phase-Block Operator Bound | [exact-conductor-phase-block-operator-bound.md](exact-conductor-phase-block-operator-bound.md) |
| Ramanujan Cross-Conductor Geometry | Centered Ramanujan Cross-Conductor Geometry | [centered-ramanujan-cross-conductor-geometry.md](centered-ramanujan-cross-conductor-geometry.md) |
| Strike Divisor-Activation Kernel | Accepted-Strike Divisor Activation Kernel | [accepted-strike-divisor-activation-kernel.md](accepted-strike-divisor-activation-kernel.md) |
| Strike CRT Lift-Index | Accepted-Strike CRT Lift-Index Transform | [accepted-strike-crt-lift-index-transform.md](accepted-strike-crt-lift-index-transform.md) |
| Strike Summatory Remainder | Accepted-Strike Summatory Coprime Remainder | [accepted-strike-summatory-coprime-remainder.md](accepted-strike-summatory-coprime-remainder.md) |
| Cross-Layer CRT Orthogonality | Accepted-Strike Cross-Layer CRT Orthogonality | [accepted-strike-cross-layer-crt-orthogonality.md](accepted-strike-cross-layer-crt-orthogonality.md) |
| Layer Innovation Orthogonality | Layer Strikes Are Innovations Of The Layer Filtration | [layer-strike-innovation-orthogonality.md](layer-strike-innovation-orthogonality.md) |
| Past-Span Saturation | Past-Span Saturation Does Not Determine Placement | [past-span-saturation-does-not-determine-placement.md](past-span-saturation-does-not-determine-placement.md) |
| 2-Gap Placement Saturation | Two-Gap Placement Saturation And The Cross-Fiber Coupling Boundary | [two-gap-placement-saturation.md](two-gap-placement-saturation.md) |
| 2-Focused Alternation Law | Two-Focused Compression Alternation Law | [two-focused-alternation-law.md](two-focused-alternation-law.md) |
| Localized-Layer Gram Matrix | Accepted-Strike Localized Layer Gram Matrix | [accepted-strike-localized-layer-gram-matrix.md](accepted-strike-localized-layer-gram-matrix.md) |
| First-Deletion Variance Identity | Accepted-Strike First-Deletion Variance Identity | [accepted-strike-first-deletion-variance-identity.md](accepted-strike-first-deletion-variance-identity.md) |
| Active Two-Class Variance | Accepted-Strike Active Two-Class Variance Identity | [accepted-strike-active-two-class-variance-identity.md](accepted-strike-active-two-class-variance-identity.md) |
| First-Deletion Reindexing | Accepted-Strike First-Deletion Coordinate Reindexing | [accepted-strike-first-deletion-coordinate-reindexing.md](accepted-strike-first-deletion-coordinate-reindexing.md) |
| Joint Capacity Envelope | Endpoint-Observable Joint Capacity Envelope | [endpoint-observable-joint-capacity-envelope.md](endpoint-observable-joint-capacity-envelope.md) |
| Endpoint Capacity Insufficiency | Endpoint Capacity Cannot Certify The Collision Budget | [endpoint-capacity-cannot-certify-collision-budget.md](endpoint-capacity-cannot-certify-collision-budget.md) |
| Sampling-Density Recombination | Endpoint Sampling And Strike Density Recombine Into Harmful Residues | [endpoint-sampling-strike-density-harmful-residue-bridge.md](endpoint-sampling-strike-density-harmful-residue-bridge.md) |
| Pointwise Margin Insufficiency | Pointwise Two-Class Margin Does Not Imply The Collision Budget | [pointwise-two-class-margin-does-not-imply-collision-budget.md](pointwise-two-class-margin-does-not-imply-collision-budget.md) |
| Harmful-Residue Box Bound | Sharp Harmful-Residue Box Inside The Collision Ellipse | [sharp-harmful-residue-box-inside-collision-ellipse.md](sharp-harmful-residue-box-inside-collision-ellipse.md) |
| Sixfold-Capacity Energy Envelope | Sharp Sixfold-Capacity Harmful-Energy Envelope | [sharp-sixfold-capacity-harmful-energy-envelope.md](sharp-sixfold-capacity-harmful-energy-envelope.md) |
| Sixfold Population-Ratio Threshold | Sharp Sixfold-Capacity Population-Ratio Threshold | [sharp-sixfold-capacity-population-ratio-threshold.md](sharp-sixfold-capacity-population-ratio-threshold.md) |
| Capacity Threshold Hierarchy | Capacity Population-Threshold Hierarchy | [capacity-population-threshold-hierarchy.md](capacity-population-threshold-hierarchy.md) |
| Late-Layer Sixfold Floor | Late-Layer Sixfold Floor Controls Harmful Energy | [late-layer-sixfold-floor-controls-harmful-energy.md](late-layer-sixfold-floor-controls-harmful-energy.md) |
| One-Layer Ellipse Non-Composition | One-Layer Harmful Ellipses Do Not Compose | [one-layer-harmful-ellipses-do-not-compose.md](one-layer-harmful-ellipses-do-not-compose.md) |
| Terminal Harmful-Excess Energy | Weighted Harmful-Excess Energy Is Already Terminal | [weighted-harmful-excess-energy-is-terminal.md](weighted-harmful-excess-energy-is-terminal.md) |
| Integral Profile Attainment | Integral Population Profiles Attain the Harmful-Energy Threshold | [integral-population-profiles-attain-harmful-energy-threshold.md](integral-population-profiles-attain-harmful-energy-threshold.md) |
| Harmful-Excess Stability Decomposition | Harmful-Excess Energy Has an Exact Stability Decomposition | [harmful-excess-energy-exact-stability-decomposition.md](harmful-excess-energy-exact-stability-decomposition.md) |
| Capacity Minimizer Separation | Harmful Capacity Separates the Energy Minimizer | [harmful-capacity-separates-energy-minimizer.md](harmful-capacity-separates-energy-minimizer.md) |
| Harmful-Capacity Excess Envelope | Sharp Harmful-Capacity Excess Envelope | [sharp-harmful-capacity-excess-envelope.md](sharp-harmful-capacity-excess-envelope.md) |
| Paired CRT Primorial Scale | Paired Harmful-Excess CRT Orthogonality Has Primorial Scale | [paired-harmful-excess-crt-orthogonality-has-primorial-scale.md](paired-harmful-excess-crt-orthogonality-has-primorial-scale.md) |
| Native-Period Hybrid Envelope | Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope | [native-period-bessel-capacity-hybrid-envelope.md](native-period-bessel-capacity-hybrid-envelope.md) |
| Native-Period Capacity Overflow | Native-Period Capacity Overflow Quantifies the Hybrid Gain | [native-period-capacity-overflow-quantifies-hybrid-gain.md](native-period-capacity-overflow-quantifies-hybrid-gain.md) |
| Envelope Width Floor | Capacity-Envelope Width Floor Needs Population Slack | [capacity-envelope-width-floor-needs-population-slack.md](capacity-envelope-width-floor-needs-population-slack.md) |
| Seven-Layer Density Floor | Seven-Layer Density Floor Maximizes Capacity Width | [seven-layer-density-floor-maximizes-capacity-width.md](seven-layer-density-floor-maximizes-capacity-width.md) |
| Seven-Layer Overflow Forcing | Seven-Layer Floor Forces Native Overflow | [seven-layer-floor-forces-native-overflow.md](seven-layer-floor-forces-native-overflow.md) |
| Filter-Seven Cut Failure | Fixed Seven Cut Cannot Clear The Original Threshold | [fixed-seven-cut-cannot-clear-original-threshold.md](fixed-seven-cut-cannot-clear-original-threshold.md) |
| Fixed Native Cut Failure | Every Fixed Native Cut Fails The Original Threshold | [every-fixed-native-cut-fails-original-threshold.md](every-fixed-native-cut-fails-original-threshold.md) |
| Moving-Cut Block Loss | Moving Cut Loses Complete Native Blocks | [moving-cut-loses-complete-native-blocks.md](moving-cut-loses-complete-native-blocks.md) |
| Incomplete-Block Bessel Bound | Incomplete-Block Bessel Excludes No Capacity | [incomplete-block-bessel-excludes-no-capacity.md](incomplete-block-bessel-excludes-no-capacity.md) |
| Capacity Stability Gap | Capacity Stability Gap Cannot Rescue the Capacity Envelope | [capacity-stability-gap-cannot-rescue-capacity-envelope.md](capacity-stability-gap-cannot-rescue-capacity-envelope.md) |
| Filter-Seven Excess Bound | Filter-Seven Harmful Excess Is Boundary-Sized | [filter-seven-harmful-excess-is-boundary-sized.md](filter-seven-harmful-excess-is-boundary-sized.md) |
| Copy-Block Excess Control | Copy-Block Harmful Excess Is Controlled By Residue Energy | [copy-block-harmful-excess-controlled-by-residue-energy.md](copy-block-harmful-excess-controlled-by-residue-energy.md) |
| Divisor Local Factor | Relaxed Almost-Prime Weight Has An Exact Divisor Local Factor | [relaxed-almost-prime-divisor-local-factor.md](relaxed-almost-prime-divisor-local-factor.md) |
| Bilinear Character Obstruction | Relaxed Almost-Prime Bilinear Remainder Has A Character Obstruction | [relaxed-almost-prime-bilinear-character-obstruction.md](relaxed-almost-prime-bilinear-character-obstruction.md) |
| Cofactor Progression Discrepancy | Relaxed Cofactor Divisor Sum Is A Prime-Progression Discrepancy | [relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md](relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md) |
| Danger-Annulus Decomposition | Incremental Danger-Annulus Decomposition | [incremental-danger-annulus-decomposition.md](incremental-danger-annulus-decomposition.md) |
| Filter Adversariality Score | Realized Filter Adversariality Score | [realized-filter-adversariality-score.md](realized-filter-adversariality-score.md) |

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
10. [Global Count Threshold That Forces Local Survival](global-count-forcing-local-survival.md)
    - Gives a rigorous but generally impractical count-only bridge.
11. [Rotation Preserves Cyclic Gap Counts](rotation-preserves-cyclic-gap-counts.md)
    - Separates cyclic invariance from absolute-window placement.
12. [Absence of 2-Gaps Is Stable](absence-of-two-gaps-is-stable.md)
    - Shows that copy-or-merge filtering cannot recreate a missing 2-gap.
13. [Batched Short-Window Discrepancy Boundary](batched-short-window-discrepancy-boundary.md)
    - States exactly what batching proves and what local positivity still needs.
14. [Safe-Zone Exhaustion Curve](safe-zone-exhaustion-curve.md)
    - Bounds how many survivors populate the safe window `[p,p^2)`: a loose
      but universal proved bound (Schroeder 2017) versus a tight but unproven
      practical estimate, plus two documented dead ends.
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
    - Projects the Sixfold-Capacity Energy Envelope property's exact capacity interval onto `b_i^2`, giving the
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
      intersects that joint budget sharply with the Harmful-Capacity Excess Envelope property's coordinate
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
74. [Capacity-Envelope Width Floor Needs Population Slack](capacity-envelope-width-floor-needs-population-slack.md)
    - Proves the feasible harmful-count width
      `min(N,2B,rB-N)`, the envelope floor
      `X>=min(N,2B,rB-N)^2/4`, and the resulting explicit lower bound for
      the Native-Period Capacity Overflow property's overflow. The envelope vanishes at both `N=0` and
      `N=rB`, so no positive population-independent floor follows from
      `r,B` alone.
75. [Seven-Layer Density Floor Maximizes Capacity Width](seven-layer-density-floor-maximizes-capacity-width.md)
    - Proves that candidate #17's local-count threshold, together with the
      installed filter `5`, places every `r>=7` population in
      `2B<=N<=(r-2)B`. Hence the Envelope Width Floor property has maximal slack `sigma=2B` and
      width floor `X>=B^2`; whether its normalized sum exceeds the Native-Period Capacity Overflow property's
      remainder budget remains open.
76. [Seven-Layer Floor Forces Native Overflow](seven-layer-floor-forces-native-overflow.md)
    - At the native cut after filter `7`, proves `q_(1,2)=30/7` and
      `e_2>=(7B_7^2/30-s_2)_+>=1` for every integer `Q>=36`. Thus the hybrid
      envelope strictly improves the all-capacity envelope for every future
      prime head `Q>=37`, with gain at least `42d_m e_2`; clearance of the
      extinction deficit remains open.
77. [Fixed Seven Cut Cannot Clear The Original Threshold](fixed-seven-cut-cannot-clear-original-threshold.md)
    - Under candidate #17 at the first untouched filter `11`, proves that a
      chain with `Q>=17` and `m>=37` has
      `U_2^hyb>T^2/(2W_-)`. Thus the positive filter-`7` overflow cannot make
      the fixed early cut certify #24's original threshold; later cuts, the
      capacity-relaxed threshold, and localized suffix control remain open.
78. [Every Fixed Native Cut Fails The Original Threshold](every-fixed-native-cut-fails-original-threshold.md)
    - Under candidate #17 at the first suffix layer, proves that cut `k` fails
      whenever `m>P_k(r_k-2)^2(1+6/D)^2`. Hence every fixed cut eventually
      fails on unbounded chains, and any potentially successful cut must have
      `r_k>=2+sqrt(7m/3)/(1+6/D)`. Moving cuts, the capacity-relaxed threshold,
      and localized suffix control remain open.
79. [Moving Cut Loses Complete Native Blocks](moving-cut-loses-complete-native-blocks.md)
    - Under a finite `theta(x)>=cx` bound and Bertrand, proves that a
      threshold-clearing cut with `M_k<=H` forces
      `m<(3/7)(1+6/D)^2(2log(H)/c-2)^2`. Using PNT explicitly as an external
      dependency, the actual chain eventually violates this bound, so every
      sufficiently large potentially successful cut has `M_k>H` and
      `s_k=H`. The Incomplete-Block Bessel Bound property subsequently proves that the incomplete-block
      overflow vanishes at this moving-prime scale.
80. [Incomplete-Block Bessel Excludes No Capacity](incomplete-block-bessel-excludes-no-capacity.md)
    - Proves the finite bound
      `sum_(i<k)X_i/q_(i,k)<=3kD^2r_k^2/(25M_kP_k(r_k-2))` and the resulting
      criterion for `e_k=0`. Using PNT explicitly outside Stainless, the
      criterion holds at every sufficiently large moving cut forced by #78.
      Combined with #77--#79, the capacity-plus-native-Bessel envelope cannot
      certify #24's original threshold under full #17. The Capacity Stability Gap property next
      closes the separate-envelope `Gamma_cap` route; localized actual-energy
      bounds remain open.
81. [Capacity Stability Gap Cannot Rescue the Capacity Envelope](capacity-stability-gap-cannot-rescue-capacity-envelope.md)
    - Proves the finite post-`5` minimizer-capacity bound
      `K_i^star-C_i<=N_0/S-(2D-18)/(15r_i)` and, once those coordinates fit,
      `Gamma_cap<=(25P_m/18)(2/5+3N_0/(5S))^2`. Candidate #17 at filter `7`
      simultaneously forces `U_cap>=P_mD^2/1080`. Prime Mertens and PNT show
      that the stability gap is eventually positive but negligible relative
      to this envelope floor, so the capacity-relaxed threshold cannot rescue
      the separate capacity envelope on an unbounded family. The Filter-Seven Excess Bound property
      next supplies a localized bound at filter `7`; scaling it remains open.
82. [Filter-Seven Harmful Excess Is Boundary-Sized](filter-seven-harmful-excess-is-boundary-sized.md)
    - Enumerates the 21 admissible residues modulo `210` and proves that their
      centered integer-weight cumulative sums range from `-8` to `10`. Hence
      every interval has the sharp bound `|b_7|<=18/7`, and the actual
      filter-`7` energy is at most `54P_m/5`, replacing the Capacity Stability Gap property's
      separate capacity charge `>=P_mD^2/1080`. This removes one fixed-layer
      artifact. Scaling the argument is exactly candidate #23's signed
      accepted-boundary cancellation problem; native-period enumeration and
      generic inclusion--exclusion do not suffice.
83. [Copy-Block Harmful Excess Is Controlled By Residue Energy](copy-block-harmful-excess-controlled-by-residue-energy.md)
    - For one incoming prime, proves that the centered harmful excess in old-
      period copy block `j` is exactly `B_j=d_t+d_(t-2)` for a permuted pair
      of centered residue-histogram entries. Consequently
      `sum_j B_j^2=2V_r+2sum_t d_t d_(t-2)<=4V_r`, and any `k` consecutive
      complete blocks have squared discrepancy at most `4kV_r`. This composes
      candidate #20's residue energy with candidate #24's localized harmful
      excess while leaving two partial old-period boundary fragments open.
84. [Relaxed Almost-Prime Weight Has An Exact Divisor Local Factor](relaxed-almost-prime-divisor-local-factor.md)
    - For the asymmetric weight `gcd(n,W)=gcd(n+2,Z)=1` with `m|n`, proves
      the exact divisor-dependent local residue table, complete-period CRT
      density, and arbitrary-interval formula `N_m=rho(m)ell_m+E_m`. In the
      candidate-#25 range `1/3<alpha<1/2`, `Z=P(Q^(2alpha))` divides
      `W=P(Q)`, so coprime divisors share the explicit dimension-two/then-one
      density while wheel-sharing divisors vanish. The bound `|E_m|<=R-1`
      is only a periodic boundary bound; cancellation of its divisor average
      remains the first genuine Type-I obligation.
85. [Relaxed Almost-Prime Bilinear Remainder Has A Character Obstruction](relaxed-almost-prime-bilinear-character-obstruction.md)
    - In the nested-wheel range, expands the scalar-centered relaxed weight
      exactly into inverse-residue brackets
      `1_(n=-2m^(-1) mod d)-1/phi(d)` and then into nonprincipal bilinear
      character modes `chi(m)chi(n)`. On the complete reduced wheel, bounded
      quadratic-character coefficients modulo `3` correlate with the full
      relaxed survivor count while the scalar comparison has zero
      correlation. This blocks the naive scalar-density Type-II route but
      does not refute candidate #25's positivity target or a locally adapted
      comparison theorem on its short hyperbolic domain.
86. [Relaxed Cofactor Divisor Sum Is A Prime-Progression Discrepancy](relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md)
    - For every odd squarefree `d|W`, proves the exact complete-wheel factor
      `A_d=A_1/phi(d)` for the shifted count `d|n+2` and writes every interval
      error as one zero-mean periodic boundary remainder. In the square-safe
      window with `W=P(Q)`, this remainder is exactly
      `pi(I;d,-2)-pi(I)/phi(d)`. Thus candidate #25's natural accumulated
      Type-I input is an averaged prime arithmetic-progression theorem; CRT
      supplies its comparison factor but not its required cancellation.
87. [Incremental Danger-Annulus Decomposition](incremental-danger-annulus-decomposition.md)
    - For consecutive primes `p<q` with `p>=5`, separates the full square-safe
      window from the accepted-value annulus `V(p,q)=[p^2,q^2)` and the
      geometric width-`h` start interval `D_h(p,q)=[p^2-h,q^2-h)`. After
      filters `2` and `3`, it identifies the phase-compatible coordinate set
      `X_D(p,q)={x: p^2+4<=x<q^2-2, x congruent to 5 modulo 6}`; membership in
      this set does not assert an actual gap, while `L_D(p,q)` counts actual
      pre-filter 2-gaps starting there. It proves equality of full-window and
      annular accepted-strike counts, the raw capacity
      `R_V=2(q-p)+ceil((q-p)^2/p)`, and
      `K_D<=A(p,q)-1<=R_V-1`, but no positive lower bound for `L_D`.
88. [Realized Filter Adversariality Score](realized-filter-adversariality-score.md)
    - For prime `p>2` and a nonempty typed population `L>0`, declares a
      continuous monotone normalization of realized destruction with anchors
      `0` for no destroyed gaps, `1/2` for the random-residue/complete-copy
      benchmark `2/p`, and `1` for local extinction. It proves the exact
      survival limit `C_p<1`, the integer excess allowance
      `x_max=ceil((1-2/p)L)-1`, and the capacity ceiling
      `C_p(K/L)<=C_p(min(1,H/L))`. The concrete full-window instance uses
      `H=A` only for `p>=5`; the annular instance uses `H=A-1` for consecutive
      primes `p<q` with `p>=5` and `L_D>0`. Across 186 audited full-window
      populations, every observed score is below `1/2` and every corresponding
      proved capacity ceiling is below `1`. These are finite-population
      observations and bounds, not a deterministic-randomness theorem or an
      annular population result.

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
