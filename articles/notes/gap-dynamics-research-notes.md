# Gap Dynamics — Research Notes

**Status:** Working notes. This document is not part of the article
*Structural Properties and Signed Boundaries of 2-Gaps in Sieve Sequences*
(`articles/chapter6/gap-dynamics.md`). It preserves the navigational and
evidence-status material that was moved out of the article so the article
reads as a self-contained publication: per-section research-record pointers,
verification-status remarks, and the research map (formerly Appendix B).
The pointers reference maintained records in this repository; their content
evolves independently of the article.

**Extracted:** 2026-09-13, from `articles/chapter6/gap-dynamics.md`
(commit 98d3a8d7).

---

## 1. Per-Section Research-Record Pointers

Each entry below was removed from the indicated section of the article. The
pointers lead to property records and candidate notes in this repository;
the status remarks repeat the article's former evidence-status convention
(non-verification is the default and is no longer stated in the article).

### Title block (former proof-status note)

- The signed-localization theorems introduced here are mathematically proved
  but not yet Stainless-verified.

### 2.2 Evidence Status

- **Mathematically proved:** a complete mathematical proof is included here,
  but no corresponding `.holds` theorem currently exists.

### 3.1 Exact Global 2-Gap Count

- A supplementary research record is available in [Exact Global 2-Gap Count](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/exact-global-two-gap-count.md). No `.holds` theorem currently encodes this exact product count, so this result is not yet Stainless-verified.

### 3.2 Exact Filter Frequency Across Repeated Copies

- A supplementary research record is available in [Exact Filter Frequency Across Repeated Copies](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/copy-index-filter-frequency.md). The repeated-stream foundation is verified in the companion Sieve Sequence article, but no `.holds` theorem currently packages these two exact copy-index classes and the finite-slice bound. This result is not yet Stainless-verified.

### 3.3 Exact Batched 2-Gap Survival

- A supplementary research record is available in [Exact Batched 2-Gap Survival](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/exact-batched-two-gap-survival.md). No corresponding `.holds` theorem currently packages the finite-batch product; this result is not yet Stainless-verified.

### 3.4 Exact Global `(2,4,2)` Cluster Count

- A supplementary research record is available in [Exact Global Count Of `(2,4,2)` Two-Gap Clusters](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/exact-global-two-gap-cluster-count.md). No `.holds` theorem currently packages the cyclic cluster count; this result is not yet Stainless-verified.

### 3.5 Rotation Preserves Cyclic Gap Counts

- maintained mathematically in [Rotation Preserves Cyclic Gap Counts](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/rotation-preserves-cyclic-gap-counts.md); it is not yet Stainless-verified.

### 3.6 Absence Of 2-Gaps Is Stable

- A supplementary research record is available in [Absence Of 2-Gaps Is Stable Under Later Filtering](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/absence-of-two-gaps-is-stable.md). No dedicated `.holds` theorem currently quantifies over the complete cyclic gap transition, so this result is not yet Stainless-verified.

### 4.1 Safe-Window 2-Gaps Certify Twin Primes

- A supplementary research record is available in [Safe-Window 2-Gaps Certify Twin Primes](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md). No `.holds` theorem currently encodes the least-prime-divisor argument, so this result is not yet Stainless-verified.

### 4.2 Isolation Of 2-Gaps After Filter 3

- A supplementary research record is available in [Isolation Of 2-Gaps After Filtering By 3](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/two-gap-isolation-after-filter-three.md). No dedicated `.holds` theorem currently counts incident 2-gaps per accepted endpoint, so this result is not yet Stainless-verified.

### 4.3 Exact Accepted Local Filter Strikes

- A supplementary research record is available in [Exact Accepted Local Filter Strikes](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/exact-accepted-local-filter-strikes.md). No `.holds` theorem currently contains the prime-counting argument; this result is not yet Stainless-verified.

### 4.4 Sharp Local 2-Gap Survival Threshold

- A supplementary research record is available in [Sharp Local 2-Gap Survival Threshold](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md). No `.holds` theorem currently encodes the local populations or the prime-counting threshold; this result is not yet Stainless-verified.

### 5.1 Weighted Deletion Conservation

- A supplementary research record is available in [Weighted Deletion Conservation Law](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/weighted-deletion-conservation-law.md). No `.holds` theorem currently encodes the weighted conditioned chain, so this result is not yet Stainless-verified.

### 5.2 Terminal Survival Criterion

- Supplementary research records are available in [Weighted Harmful-Excess Energy Is Already Terminal](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/weighted-harmful-excess-energy-is-terminal.md) and [Weighted Harmful-Excess Quadratic Survival](https://github.com/thiagomata/prime-numbers/blob/master/candidates/weighted-harmful-excess-quadratic-survival.md). No `.holds` theorem currently encodes the weighted chain, so this result is not yet Stainless-verified.

### 6. Why The Capacity Envelope Is Exhausted

- The broader research program contains additional mathematically proved
  capacity analyses; in the article these analyses remain in the
  supplementary research map (Section 3 below).

### 7. Exact Filter-Seven Localization

- A supplementary research record is available in [Filter-Seven Harmful Excess Is Boundary-Sized](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/filter-seven-harmful-excess-is-boundary-sized.md). The 21 weights, their zero sum, and all cyclic subsums are not yet encoded as a `.holds` theorem.

### 8.1 Accepted-Boundary Discrepancy Estimate

- A supplementary model record is [Accepted-Anchor Strike Density](https://github.com/thiagomata/prime-numbers/blob/master/candidates/accepted-anchor-strike-density.md).

### 8.2 Residue-Collision Energy Estimate

- A supplementary model record is [Conditioned Residue-Collision Energy](https://github.com/thiagomata/prime-numbers/blob/master/candidates/conditioned-residue-collision-energy.md).

### 9. Copy-Block Harmful Excess And Residue Energy

- A supplementary research record is available in [Copy-Block Harmful Excess Is Controlled By Residue Energy](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/copy-block-harmful-excess-controlled-by-residue-energy.md). The open relative collision input is formulated in [Conditioned Residue-Collision Energy](https://github.com/thiagomata/prime-numbers/blob/master/candidates/conditioned-residue-collision-energy.md). The centered rational histogram and block observable are not yet modeled as a `.holds` theorem.

### 11.1 Why This Is Hard: The Type-II Barrier

- A supplementary survey mapping recent Type-I/Type-II results to these exact obligations is available in [Recent Prime-Producing Sieves: A Deep-Dive](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/research/recent-prime-producing-sieves-deep-dive.md).

---

## 2. Evidence-Status Vocabulary (Former §2.2 Material)

- **Mathematically proved:** a complete mathematical proof is included in
  the article, but no corresponding `.holds` theorem currently exists.
- The article's derivations and appendices are the authority for its
  mathematical claims; linked property records are supplementary navigation
  through the wider research program.
- A mathematical proof is not called Stainless-verified merely because its
  finite instances can be computed.

---

## 3. Research Map (Former Appendix B)

This non-load-bearing map records adjacent investigations and the separate
almost-prime program. None of the properties below is used as a premise of a
theorem in the article. The proof status is quoted from each property's own
record: where a proof is conditional, the condition family named there is
repeated, and the record itself states the full hypotheses. **Proved** means
mathematically proved in the record; Stainless verification is not claimed
for any row.

Table 1 lists the properties treated only in their own property records —
properties left out of the article. Table 2 lists the eighteen properties
with a direct connection to the article and states that connection per row.

**Table 1 — properties left out of the article.**

| Property | Investigation line | Proof status |
|----------|--------------------|--------------|
| [Reverse-Engineered Head Scenario](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/reverse-engineered-eventual-head-scenario.md) | Scenario localization | Proved as a conditional certificate; the existence of an unbounded family of certificates is not proved. |
| [Perfect Scenario Infinitude](https://github.com/thiagomata/prime-numbers/blob/master/candidates/infinite-perfect-scenario-property.md) | Scenario localization | Under independent verification; the infinitude assertion is an open claim. |
| [Count-Forces-Survival Threshold](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/global-count-forcing-local-survival.md) | Scenario localization | Proved sufficient condition; the known exact global count does not generally meet it at large stages. |
| [Batched Discrepancy Boundary](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/batched-short-window-discrepancy-boundary.md) | Scenario localization | Partly proved: complete-period formula proved; the required general short-window positivity bound is open. |
| [Fixed-k Shot Spacing](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/stable-small-k-shot-spacing.md) | Scenario localization | Proved. |
| [Pair Separation Premise](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/interval-premise-from-pair-existence.md) | Scenario localization | Proved as a conditional lemma. |
| [Local Count Shot-Capacity Premise](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/local-count-forces-k2-shot-capacity.md) | Scenario localization | Proved as a conditional local-count lemma. |
| [Seven-Layer Capacity Floor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/exact-seven-layer-capacity-floor.md) | Capacity and conservation | Proved. |
| [Close-Pair Matching Bound](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/local-density-forces-close-pair-matching.md) | Capacity and conservation | Proved. |
| [Raw Close-Pair Attrition](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/filtering-attrition-bound-raw-close-pairs.md) | Capacity and conservation | Proved. |
| [Matching Attrition Bound](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/filtering-attrition-bound-close-pair-matching.md) | Capacity and conservation | Proved. |
| [Post-Filter-3 Harmful Capacity](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/harmful-residue-capacity-after-filter-three.md) | Capacity and conservation | Proved as a conditional local-count lemma. |
| [Two-Class Collision Survival](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/two-class-survival-from-collision-energy.md) | Capacity and conservation | Proved as a conditional collision-energy lemma. |
| [Weighted Chain Survival](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/weighted-collision-energy-chain-survival.md) | Capacity and conservation | Proved as a conditional chain lemma. |
| [Pair Local Factor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/two-gap-pair-local-factor-by-separation.md) | Pair correlation and energy | Proved (complete-period theorem). |
| [Pair-Correlation Average](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/complete-period-two-gap-pair-correlation-average.md) | Pair correlation and energy | Proved (complete-period theorem). |
| [Fourier Correlation Bound](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/fourier-two-gap-correlation-prefix-bound.md) | Pair correlation and energy | Proved (finite Fourier theorem). |
| [Localized Fourier Boundary](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/localized-two-gap-correlation-fourier-boundary.md) | Pair correlation and energy | Partly proved: rectangle identities proved; the required localized spectral bound is open. |
| [Conductor-Decay Destruction](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/short-interval-localization-destroys-prime-conductor-decay.md) | Pair correlation and energy | Proved — finite Fourier lemma. |
| [Large-Sieve Budget Mismatch](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/black-box-large-sieve-does-not-fit-weighted-collision-budget.md) | Pair correlation and energy | Proved, conditional only on granting the stated standard large-sieve input. |
| [First-Deletion Terminal Energy](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/first-deletion-pair-terminal-energy.md) | Pair correlation and energy | Proved — exact identity. |
| [Endpoint Excess-Imbalance Split](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/two-endpoint-observables-separate-harmful-excess-and-imbalance.md) | Pair correlation and energy | Partly proved: exact identities and conditional implications proved; sampling and strike-discrepancy bounds open. |
| [Orthogonal Residue-Energy Split](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/orthogonal-residue-energy-decomposition-after-two-class-filter.md) | Pair correlation and energy | Proved — exact identity. |
| [Möbius Strike-Density Sum](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-density-boundary-decomposition.md) | Accepted-strike and spectral | Proved — exact identity. |
| [Endpoint Discrepancy Contraction](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/endpoint-density-contracts-strike-discrepancy.md) | Accepted-strike and spectral | Proved. |
| [Weighted Error Composition](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/weighted-scalar-error-composition.md) | Accepted-strike and spectral | Proved. |
| [Strike-Error Quadratic Variation](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-quadratic-variation.md) | Accepted-strike and spectral | Proved — exact identity. |
| [Prime-Square Boundary Formula](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/prime-square-window-boundary-residue-formula.md) | Accepted-strike and spectral | Proved — exact identity and exact counterexample. |
| [Harmless-Energy Pair Correlation](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/harmless-energy-fixed-set-pair-form.md) | Accepted-strike and spectral | Proved — exact identities. |
| [Harmless-Class Uniformity](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/complete-period-harmless-class-uniformity.md) | Accepted-strike and spectral | Proved — exact identities. |
| [Harmless Spectral Excess](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/harmless-energy-spectral-excess.md) | Accepted-strike and spectral | Proved — exact identity and problem boundary. |
| [CRT Fiber Translation](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/harmless-class-crt-translated-fibers.md) | Accepted-strike and spectral | Proved — exact identities and strategy boundary. |
| [Inverse-Phase Gram Matrix](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/centered-inverse-phase-gram-matrix.md) | Accepted-strike and spectral | Proved — exact finite identities. |
| [Phase-Operator Norm Bound](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/centered-phase-operator-norm-boundary.md) | Accepted-strike and spectral | Proved — exact finite operator identity and strategy boundary. |
| [Conductor Phase-Block Bound](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/exact-conductor-phase-block-operator-bound.md) | Accepted-strike and spectral | Proved — exact finite block estimate and strategy boundary. |
| [Ramanujan Cross-Conductor Geometry](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/centered-ramanujan-cross-conductor-geometry.md) | Accepted-strike and spectral | Proved — exact finite identities and exact counterexample to universal cross-conductor orthogonality. |
| [Strike Divisor-Activation Kernel](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-divisor-activation-kernel.md) | Accepted-strike and spectral | Proved — exact finite quadratic identity. |
| [Strike CRT Lift-Index](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-crt-lift-index-transform.md) | Accepted-strike and spectral | Proved — exact finite identities. |
| [Strike Summatory Remainder](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-summatory-coprime-remainder.md) | Accepted-strike and spectral | Proved — exact identity and strategy boundary. |
| [Cross-Layer CRT Orthogonality](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-cross-layer-crt-orthogonality.md) | Accepted-strike and spectral | Proved. |
| [Localized-Layer Gram Matrix](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-localized-layer-gram-matrix.md) | Accepted-strike and spectral | Proved. |
| [First-Deletion Variance Identity](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-first-deletion-variance-identity.md) | Accepted-strike and spectral | Proved. |
| [Active Two-Class Variance](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-active-two-class-variance-identity.md) | Accepted-strike and spectral | Proved. |
| [First-Deletion Reindexing](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/accepted-strike-first-deletion-coordinate-reindexing.md) | Accepted-strike and spectral | Proved. |
| [Joint Capacity Envelope](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/endpoint-observable-joint-capacity-envelope.md) | Capacity composition | Proved. |
| [Endpoint Capacity Insufficiency](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/endpoint-capacity-cannot-certify-collision-budget.md) | Capacity composition | Proved — logical insufficiency result. |
| [Sampling-Density Recombination](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/endpoint-sampling-strike-density-harmful-residue-bridge.md) | Capacity composition | Proved — exact identity. |
| [Pointwise Margin Insufficiency](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/pointwise-two-class-margin-does-not-imply-collision-budget.md) | Capacity composition | Proved — logical insufficiency result. |
| [Harmful-Residue Box Bound](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/sharp-harmful-residue-box-inside-collision-ellipse.md) | Capacity composition | Proved. |
| [Sixfold-Capacity Energy Envelope](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/sharp-sixfold-capacity-harmful-energy-envelope.md) | Capacity composition | Proved as a conditional local-capacity theorem. |
| [Sixfold Population-Ratio Threshold](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/sharp-sixfold-capacity-population-ratio-threshold.md) | Capacity composition | Proved as a conditional local-population theorem. |
| [Capacity Threshold Hierarchy](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/capacity-population-threshold-hierarchy.md) | Capacity composition | Proved — comparison theorem. |
| [Late-Layer Sixfold Floor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/late-layer-sixfold-floor-controls-harmful-energy.md) | Capacity composition | Proved as a conditional layer-range theorem. |
| [One-Layer Ellipse Non-Composition](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/one-layer-harmful-ellipses-do-not-compose.md) | Capacity composition | Proved — comparison obstruction. |

**Table 2 — properties connected to this article.**

| Property | Connection to this article | Proof status |
|----------|----------------------------|--------------|
| [Integral Profile Attainment](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/integral-population-profiles-attain-harmful-energy-threshold.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved — algebraic boundary. |
| [Harmful-Excess Stability Decomposition](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/harmful-excess-energy-exact-stability-decomposition.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved — conditioned-chain identity. |
| [Capacity Minimizer Separation](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/harmful-capacity-separates-energy-minimizer.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved — conditioned-chain stability theorem. |
| [Harmful-Capacity Excess Envelope](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/sharp-harmful-capacity-excess-envelope.md) | Supports §6.1; narrated there, full proof in Appendix C.1. | Proved as a conditional capacity theorem. |
| [Paired CRT Primorial Scale](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/paired-harmful-excess-crt-orthogonality-has-primorial-scale.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved — boundary result. |
| [Native-Period Hybrid Envelope](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/native-period-bessel-capacity-hybrid-envelope.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved — conditioned-chain bound. |
| [Native-Period Capacity Overflow](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/native-period-capacity-overflow-quantifies-hybrid-gain.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved — conditioned-chain corollary. |
| [Envelope Width Floor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/capacity-envelope-width-floor-needs-population-slack.md) | Supports §6.2; narrated there, full proof in Appendix C.2. | Proved — conditioned-chain boundary. |
| [Seven-Layer Density Floor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/seven-layer-density-floor-maximizes-capacity-width.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved as a conditional bridge. |
| [Seven-Layer Overflow Forcing](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/seven-layer-floor-forces-native-overflow.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved — unconditional envelope improvement. |
| [Filter-Seven Cut Failure](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/fixed-seven-cut-cannot-clear-original-threshold.md) | Supports §6.4; narrated there, full proof in Appendix C.3. | Proved as a conditional envelope obstruction. |
| [Fixed Native Cut Failure](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/every-fixed-native-cut-fails-original-threshold.md) | Supports §6.4; narrated there, full proof in Appendix C.4. | Proved as a conditional envelope obstruction. |
| [Moving-Cut Block Loss](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/moving-cut-loses-complete-native-blocks.md) | Supports §6.5; narrated there, full proof in Appendix C.5. | Proved under its stated conditions; the asymptotic corollary additionally uses Bertrand's postulate and the prime number theorem. |
| [Incomplete-Block Bessel Bound](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/incomplete-block-bessel-excludes-no-capacity.md) | Supports §6.5; narrated there, full proof in Appendix C.6. | Proved under its stated conditions; the asymptotic corollary additionally uses Bertrand's postulate and the prime number theorem. |
| [Capacity Stability Gap](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/capacity-stability-gap-cannot-rescue-capacity-envelope.md) | Feeds the Section 6 exhaustion audit; summarized collectively, no individual section. | Proved under its stated conditions; the asymptotic corollary additionally uses the prime number theorem and Mertens' theorem for primes. |
| [Divisor Local Factor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-almost-prime-divisor-local-factor.md) | Belongs to the separate almost-prime program (§11); full proof in the draft article. | Proved — exact local factor and boundary decomposition. |
| [Bilinear Character Obstruction](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md) | Belongs to the separate almost-prime program (§11); full proof in the draft article. | Proved — exact decomposition and complete-wheel obstruction. |
| [Cofactor Progression Discrepancy](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md) | Belongs to the separate almost-prime program (§11); full proof in the draft article. | Proved: exact reduction; the accumulated prime-progression estimate is open. |

---

External pointers removed from the article body that are not tied to one
section: the relaxed almost-prime program is developed in
[draft-relaxed-almost-prime-sieve-sequence.md](draft-relaxed-almost-prime-sieve-sequence.md);
the Type-I/Type-II survey is available in
[recent-prime-producing-sieves-deep-dive.md](../properties/sieve-sequence/research/recent-prime-producing-sieves-deep-dive.md).
