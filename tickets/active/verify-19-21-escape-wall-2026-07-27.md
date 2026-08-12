# Verify Whether Candidates #19-#22 Escape the Twin-Prime-Strength Wall

**Created:** 2026-07-27
**Status:** In progress
**Depends on:** `prove-hereditary-shot-spacing-2026-07-23.md` (the wall
identified there), `algebraic-conditioned-survival-2026-07-27.md` (the latest
orthogonal energy reduction)

> Persistent-memory ticket. Update continuously per `TICKET_DISCIPLINE.md`.

## START HERE

The #19-#21 audit is complete but its original blanket verdict was too coarse.
Use the revised three-way classification: same-wall premise, noncircular
component, or terminal consumer. The Terminal Harmful-Excess Energy property now classifies restricted #12's
weighted harmful norm as terminal. Candidate #22 remains an independently
noncircular distribution diagnostic, but it is not required for survival
after scalar feasibility.

The finite-Fourier audit of candidate #22 is complete. Its remaining route is
a genuinely coefficient-weighted bilinear estimate using the CRT
coefficients, interval multipliers, or chain weights. Generic conductor
orthogonality is exactly false.

Dedicated #23 and #13 algebraic audits are now complete through properties
#55 and #64 respectively. Candidate #13 plus #23 recombines exactly into the
two harmful residue deviations, so the direct restricted #12 route is now the
preferred scalar representation. The Terminal Harmful-Excess Energy property proves that either aggregate
representation is terminal at candidate #21's global allowance.

The One-Layer Ellipse Non-Composition property now proves that the one-layer capacity thresholds do not compose
into #21's global allowance, even on the ideal multiplicative population
scale. The correct scalar interface is a direct weighted aggregate for the
realized harmful energies or capacity envelopes.

The properties from Terminal Harmful-Excess Energy through Harmful-Capacity Excess Envelope and candidate #24 give the complete separate-layer
capacity boundary. The properties from Paired CRT Primorial Scale through Native-Period Capacity Overflow now give the first cross-layer
refinement for the harmful-excess observables

```math
g_i(n)
=
F_i(n)
\left(
h_i(n)-\frac2{r_i}
\right),
\qquad
b_i=\sum_{n\in W_Q}g_i(n),
```

where `F_i` is the current paired-survivor indicator and `h_i` is the
two-residue hit indicator.

The Paired CRT Primorial Scale property proves exact complete-block cancellation, cross-layer
orthogonality, and norms. Final-period Bessel retains the primorial and is
exhausted. The Native-Period Hybrid Envelope property instead uses every intermediate native period,
intersects its prefix Bessel budget sharply with coordinate capacities, and
proves

```math
E_b
\le
\mathcal U_{\mathrm{hyb}}
\le
\mathcal U_{\mathrm{cap}}.
```

The Native-Period Capacity Overflow property defines the normalized capacity overflow

```math
e_k
=
\left(
\sum_{i<k}
\frac{X_i}{M_kd_ip_ia_i}
-
s_k
\right)_+
```

and proves that cut `k` gains at least

```math
\frac{M_kd_m}{r_{k-1}-2}e_k
```

over the all-capacity envelope.

The Envelope Width Floor property now lower-bounds that overflow through the realized
population slack

```math
\sigma_i=\min(N_i,2B_i,r_iB_i-N_i).
```

Its synchronization with candidate #24 and both permanent catalogs is
complete. The conditional #17-to-#24 bridge is also proved: candidate #17's
local-count threshold places every applicable realized population in
the Envelope Width Floor property's maximal-width regime

```math
2B_i\le N_i\le(r_i-2)B_i,
```

and hence forces `sigma_i=2B_i`. The lower inequality comes from #17's count
threshold; the upper inequality comes independently from the three allowed
two-gap-start classes modulo `30`. The exact fixed-cut parameter comparison is
now complete. Its positive half is: at the native cut after filter `7`,
`q_(1,2)=30/7`, and for every `Q>=36`,

```math
e_2
\ge
\left(
\frac{7B_7^2}{30}-((Q^2-Q-2)\bmod210)
\right)_+
\ge1.
```

Thus the hybrid envelope is unconditionally and strictly smaller than the
all-capacity envelope for every future prime head `Q>=37`. The bridge does
not prove candidate #17 or candidate #24; the quantified gain still has to be
compared with the exact remaining extinction deficit. The Filter-Seven Cut Failure property completes
that comparison for the original threshold at the fixed `k=2` cut: under #17
at filter `11`, the untouched suffix forces
`U_2^hyb>T^2/(2W_-)` on chains with `m>=37`. Resume from a moving cut, not by
enlarging the settled filter-`7` overflow. The Fixed Native Cut Failure property now generalizes this
to every cut:

```math
m
>
P_k(r_k-2)^2(1+6/D)^2
\quad\Longrightarrow\quad
\mathcal U_k^{\mathrm{hyb}}
>
\frac{T^2}{2W_-}.
```

Hence every fixed cut eventually fails, and any cut that could clear the
original threshold must satisfy

```math
r_k
\ge
2+
\frac{\sqrt{7m/3}}{1+6/D}.
```

The next live question is whether moving this far makes the native modulus
too large for useful complete-block cancellation. The Moving-Cut Block Loss property answers that
question. Under the finite hypotheses `theta(r_(k-1))>=c r_(k-1)` and
Bertrand, a threshold-clearing cut with `M_k<=H` must satisfy

```math
m
<
\frac37(1+6/D)^2
\left(
\frac{2\log H}{c}-2
\right)^2.
```

Using PNT externally, the actual `m=pi(Q)-3` eventually exceeds this
logarithmic-squared bound. Hence every sufficiently large potentially
successful cut has `M_k>H` and `s_k=H`: there are no complete native blocks.
The remaining native-period question is the Bessel constraint on that single
incomplete block. The Incomplete-Block Bessel Bound property closes that question. For every cut,

```math
\sum_{i<k}\frac{X_i}{q_{i,k}}
\le
\frac{3kD^2r_k^2}{25M_kP_k(r_k-2)}.
```

When `M_k>H` and

```math
M_kP_k
\ge
\frac{3kD^2r_k^2}{25H(r_k-2)},
```

one has `e_k=0` and `U_k^hyb=U_cap`. PNT makes this product inequality hold
at every sufficiently large moving cut that could avoid the suffix
obstruction. Combined with the properties from Filter-Seven Cut Failure through Moving-Cut Block Loss, the current
capacity-plus-native-Bessel envelope cannot certify #24's original threshold
under full candidate #17. The Capacity Stability Gap property now closes the `Gamma_cap` repair of
that same envelope: all post-`5` minimizer capacities eventually fit, the
remaining filter-`5` gap is negligible, and filter `7` already forces
`U_cap>=P_mD^2/1080`.

The Filter-Seven Excess Bound property supplies the first localized-energy success:
`|b_7|<=18/7`, so the actual filter-`7` energy is at most `54P_m/5` rather
than the capacity charge of order `P_mD^2`. Its direct generalization is
the Sampling-Density Recombination property's identity `b_i=delta_(0,i)+delta_(-2,i)`, exactly candidate
#23's accepted-boundary discrepancy. Start from the need for new signed
mean-square or cross-layer cancellation. Do not restart complete-period
Bessel, native-period Bessel, separate-layer capacity optimization,
`Gamma_cap` alone, fixed-period enumeration, first-deletion reindexing, or
empirical-range extension.

## Goal

Determine whether the algebra-first candidates #19, #20, #21, and #22 escape
the short-window positivity wall that blocked #14 (and that the team's
chain-population reframe also hit). The wall: every per-layer / chain
population bound so far reduces, at the final layer or in aggregate, to a
twin-prime-strength short-window positivity estimate for the pair `(n, n+2)`.

The decision this ticket supports: is there a viable new proof path among
#19-#22, or has the candidate program reached a characterization boundary?

## Strategy

Read each candidate precisely. For each, identify:
1. The PROVEN one-layer algebraic bound (what's already established).
2. The OPEN estimate needed to extend to the chain / final layer.
3. Whether that open estimate, at the final layer of a chain (where the
   population is the twin primes in `[Q,Q^2)`), reduces to twin-prime
   positivity.

Reduction test:

1. **Same wall:** the proposed premise is equivalent to final positivity,
   explicitly assumes a positive final population, or can only be normalized
   after inserting such a lower bound.
2. **Noncircular component:** the premise may remain true when the final
   population is zero and can be investigated without first proving
   positivity.
3. **Terminal consumer:** the statement implies survival by design but
   decomposes into independently estimable noncircular components.

Merely observing that a sufficient theorem implies twin-prime positivity is
not enough to classify it as circular; every successful sufficient theorem
does. The audit must identify where positivity is assumed or reintroduced in
the proposed proof.

## Current State

- Candidates #19-#21 have been audited.
- Subsequent algebra found and corrected a stopping-index off-by-one:
  pre-filter energy includes the first deleting layer. The correct energy stop
  is `s(x)=min(tau(x)+1,m)`.
- Candidate #22 and the exact orthogonal decomposition are now part of the
  audit:

  ```math
  V_i
  =
  U_i
  +
  \frac{r_i}{2(r_i-2)}b_i^2
  +
  \frac12\Delta_i^2.
  ```
- The earlier claim that #19-#21 constituted a complete characterization was
  premature. Candidate #22 supplies a noncircular component whose proof
  strength has not yet been resolved.
- Repository synchronization is complete. Candidate notes #10, #13, #19-#22,
  both catalogs, the orthogonal property chain, the #14 cross-scope note, and
  the research-landscape summaries now use the revised classification.
  Candidate #10 is explicitly excluded as the missing accepted-strike density
  theorem.
- Candidate #23 now states the missing accepted-anchor strike-density theorem
  separately. It defines
  `epsilon_i=H_i/A_i-1/r_i`, gives both pointwise and weighted aggregate
  formulations, and inserts its error together with #13 into #21's exact
  remaining harmless-energy allowance.
- The exact accepted-strike discrepancy is now reduced to boundary arithmetic.
  For an old-filter modulus `P`, interval `[L,U)`, and incoming prime `r`,
  accepted strikes are the coprime count in the scaled interval
  `[ceil(L/r),ceil(U/r))`. Centered inclusion-exclusion gives

  ```math
  H-\frac Ar
  =
  \left(\ell_r-\frac\ell r\right)\frac{\varphi(P)}P
  +
  E_P(L_r,U_r)
  -
  \frac1rE_P(L,U).
  ```

  This is promoted as
  `properties/sieve-sequence/accepted-strike-density-boundary-decomposition.md`.
- Along a fixed-window conditioned chain, let
  `E_i=A_i-(U-L)phi(P_i)/P_i`. The centered strike discrepancy has the exact
  recurrence

  ```math
  H_i-\frac{A_i}{r_i}
  =
  \left(1-\frac1{r_i}\right)E_i-E_{i+1}.
  ```

  It telescopes linearly under the one-anchor survival weights
  `v_i=product_{j>i}(1-1/r_j)`.
- Post-3 endpoint isolation removes the endpoint-to-anchor ratio. For `N_i`
  complete 2-gaps whose endpoints lie in the `A_i` eligible anchors,

  ```math
  2N_i\le A_i,
  \qquad
  |2N_i\varepsilon_i|
  \le
  \left|H_i-\frac{A_i}{r_i}\right|.
  ```

  This is promoted as
  `properties/sieve-sequence/endpoint-density-contracts-strike-discrepancy.md`.
- Weighted Minkowski gives the sharp aggregate scalar composition. With

  ```math
  \mathcal E_\beta
  =
  \sum_iw_i\frac{r_i}{2(r_i-2)}H_i^2\eta_i^2,
  \qquad
  \mathcal E_D
  =
  \sum_iw_i\frac{r_i}{2(r_i-2)}D_i^2,
  ```

  and

  ```math
  \mathcal E_\Delta
  =
  \frac12\sum_iw_iH_i^2\eta_i^2,
  ```

  the proved bound is

  ```math
  \sum_iw_iV_i
  \le
  \sum_iw_iU_i
  +
  \left(
  \sqrt{\mathcal E_\beta}
  +
  \sqrt{\mathcal E_D}
  \right)^2
  +
  \mathcal E_\Delta.
  ```

  This is promoted as
  `properties/sieve-sequence/weighted-scalar-error-composition.md`.
- Candidate #23's weighted square has an exact positive quadratic-variation
  decomposition. With

  ```math
  q_i=1-\frac1{r_i},
  \qquad
  c_i=w_i\frac{r_i}{2(r_i-2)},
  ```

  it has the form

  ```math
  \mathcal E_D
  +
  c_0q_0(1-q_0)E_0^2
  =
  \sum_i c_iq_i(E_i-E_{i+1})^2
  +
  c_{m-1}(1-q_{m-1})E_m^2
  +
  \sum_{i=1}^{m-1}\gamma_iE_i^2,
  ```

  where every `gamma_i>0`. This is promoted as
  `properties/sieve-sequence/accepted-strike-quadratic-variation.md`.
- The prime-square endpoints have the exact residue form

  ```math
  E_P(Q,Q^2)
  =
  \sum_{\substack{d\mid P\\d>1}}
  \mu(d)\frac{[Q]_d-[Q^2]_d}{d}.
  ```

  Terms with `d|(Q-1)` vanish, but the full sum has no universal sign. In the
  fixed window `[19,19^2)`, it is negative for `P=2310` and positive for
  `P=30030`. This is promoted as
  `properties/sieve-sequence/prime-square-window-boundary-residue-formula.md`.
  The defeated universal-sign and sign-preservation subclaims are indexed in
  `candidates/refuted/accepted-strike-boundary-sign-laws.md`.
- Candidate #22 now has an exact fixed-set pair form. If `M_i=N_{i+1}`, then

  ```math
  U_i
  =
  \#\{
  (x,y)\in S_{i+1}^2:
  r_i\mid x-y
  \}
  -
  \frac{M_i^2}{r_i-2},
  ```

  and

  ```math
  U_i
  =
  V_{r_i}(S_{i+1})
  -
  \frac{2M_i^2}{r_i(r_i-2)}.
  ```

  The weighted fixed-set kernel uses `f_{i+1}`, stops before the first deleting
  filter, and has the exact additional negative centering

  ```math
  -
  \sum_{i<t}
  \frac{2w_i}{r_i(r_i-2)}.
  ```

  This is promoted as
  `properties/sieve-sequence/harmless-energy-fixed-set-pair-form.md`.
- The magnitude of #22's additional negative pair-kernel centering is
  uniformly bounded:

  ```math
  0
  \le
  \sum_{i<t}\frac{2w_i}{r_i(r_i-2)}
  \le
  \frac8{15}.
  ```

  It is therefore a real constant improvement but cannot cancel the
  `2 log(Q)/log(5)` growth in the previously failed worst-difference estimate.
- Over a complete CRT period after filter `r_i`, every harmless start class
  has the same count, so the harmless energy is exactly zero. Complete blocks
  cancel from centered class counts, leaving only remainder-prefix energy.
  This is promoted as
  `properties/sieve-sequence/complete-period-harmless-class-uniformity.md`.
- Candidate #22 is exactly the localized nontrivial Fourier mass above the
  sharp floor forced by the two empty harmful classes:

  ```math
  U_i
  =
  \frac1{r_i}\sum_{k\ne0}|\widehat d_i(k)|^2
  -
  \frac{2M_i^2}{r_i(r_i-2)}.
  ```

  This is promoted as
  `properties/sieve-sequence/harmless-energy-spectral-excess.md`.
- A bounded exact falsifier checked the integer-equivalent pointwise law
  `(r_i-2)sum_a c_{i,a}^2-M_i^2<=(r_i-2)M_i` on all 1,035 layers with prime
  heads `5<=Q<224`. No violation occurred. The lineage library's independent
  hand-derived tests pass. This finite non-result is inconclusive and is not
  evidence for either the pointwise law or the preferred aggregate theorem.
- the CRT Fiber Translation property gives the exact translated-fiber form
  `d_a=rho ell_a+E_(ell_a)(v_a)`, where
  `v_a=ceil((Q-a)/r)+sa`, `s=r^(-1) mod P`, the lengths differ by at most
  one, and distinct phases are spaced on the order of `P/r`. The remaining
  pointwise theorem is centered `L^2` discrepancy on these explicit phases.
- the Inverse-Phase Gram Matrix property evaluates the centered inverse-phase Gram matrix. Its
  single-frequency cost is `h-|K_m|^2/h`, its phase sum `K_m` is an explicit
  collapsed geometric expression, and its cross-frequency entry is
  `K_(m-n)-K_m K_(-n)/h`. The full quadratic form is not diagonal.
- the Phase-Operator Norm Bound property proves the inverse phases have orthogonal full-Fourier rows:
  `AA^*=PI` and `CAA^*C=PC`. The centered operator norm is sharply `sqrt(P)`,
  so black-box composition reproduces the full-shift Parseval energy exactly;
  the one-unit fiber-length correction has the same period-scale boundary.
- the Conductor Phase-Block Bound property restricts to exact conductor `q`. If `mu_q` is the largest
  inverse-phase multiplicity modulo `q`, then the squared block norm is at
  most `q mu_q<r+2q`, and the interval multiplier contributes
  `min(ell,q)`. This is a genuine conductor-scale improvement, but triangle
  recombination creates an oversized square-root divisor sum.
- the Ramanujan Cross-Conductor Geometry property gives the exact centered cross-conductor Ramanujan trace.
  Distinct conductor blocks are not orthogonal: already at `P=30`, `r=7`,
  the coprime pair `q=2`, `q'=3` has squared cross norm `168/25`. Another pair
  has squared normalized Hilbert--Schmidt coherence `2793/3203`.
- the properties from Joint Capacity Envelope through Sampling-Density Recombination solve #13's exact endpoint-capacity geometry and prove
  that #13 plus #23 is precisely the sum/difference decomposition of the two
  harmful start-residue deviations.
- the properties from Pointwise Margin Insufficiency through Sixfold Population-Ratio Threshold show that the old pointwise survival margin is
  insufficient, solve the sharp harmful-energy capacity envelope, and reduce
  its one-layer criterion exactly to

  ```math
  G>\rho_*(r)B.
  ```

- the properties from Capacity Threshold Hierarchy through Late-Layer Sixfold Floor place this threshold strictly below #14's count floor,
  classify when #19's `2B+1` floor is enough, and prove that it is enough
  throughout `Q^2-Q-3<3r(r-1)`, in particular
  `r>=Q/sqrt(3)+1`.
- the One-Layer Ellipse Non-Composition property proves that these one-layer comparisons do not imply #21's
  global weighted scalar budget. At half of each local allowance on the ideal
  multiplicative scale, the global overrun factor is at least `m^2/2`.

## What is Learned

Revised verdict per candidate:

- **#19 (sixfold harmful-residue capacity): SAME WALL AS A HEREDITARY
  CANDIDATE.** The proved one-layer bound
  `K_r <= 2(floor(L_Q/(6r))+1)` is valid and clean (verified the arithmetic;
  uses the 5-mod-6 phase to bound the two harmful classes). But the open
  hereditary floor `G_r(W_Q) >= 2 floor(L_Q/(6r))+3` at the FINAL layer
  (`r~Q`) demands order-`Q` certified-prime 2-gaps in `[Q,Q^2)` — twin-prime-
  strength. The candidate's own Limitation admits this: "may retain the same
  parity obstruction that blocks direct twin-prime sieving." The naive
  cumulative recurrence is also flagged lossy (sum of 1/r diverges). Same wall,
  self-acknowledged. Keep #19 as an unconditional one-layer tool, not the
  primary hereditary theorem.

- **#20 (conditioned residue-collision energy): MIXED.** Its collision estimate
  has genuinely different shape: a second-moment/four-point-correlation bound,
  not a count. But the candidate also requires a positive population floor of
  3-6 gaps. The open estimate
  `C_r <= N_r + N_r^2/r` requires, per the candidate's own Limitation, "a lower
  bound for `N_r` strong enough to encounter the parity problem again." The
  normalization step (converting an absolute four-point upper bound into a
  bound in terms of the unknown `N_r`) is where the wall re-enters. The
  collision theorem itself is noncircular; the full two-premise candidate
  returns to the wall through its population premise.

- **#21 (cumulative weighted collision budget): TERMINAL CONSUMER, NOT AN
  ESCAPE CLAIM.** Its budget implies survival by design. Calling it "the same
  wall" solely for that reason is uninformative. The useful question is whether
  its three orthogonal components can be bounded independently. A dedicated
  property
  (`black-box-large-sieve-does-not-fit-weighted-collision-budget.md`) records
  that the ordinary large-sieve route does not fit. Worst-difference,
  complete-origin Fourier, and symmetric capacity routes also fail. These are
  quantitative failures of particular estimates, not proof that every
  component bound is circular.

- **#22 (conditioned harmless-class collision energy): CURRENT ESCAPE-WALL
  TEST.** The pointwise benchmark

  ```math
  U_i\le N_{i+1}
  ```

  remains true when `N_{i+1}=0`, because then `U_i=0`. It therefore does not
  assume final positivity. It is the same natural collision scale as #20 on
  the smaller `r_i-2` harmless alphabet, so it may still be parity-hard, but
  that has not been established. The sharper research target is a weighted
  aggregate bound for `sum_i w_i U_i`, not necessarily the pointwise
  inequality at every layer.

**Current meta-conclusion:** #19 still reaches the population wall; #20 mixes
a noncircular collision statement with a circular population premise; #21 is
a terminal consumer; and #22 is a genuinely noncircular component whose
provability is open. The candidate program has isolated the difficulty more
precisely, but has not yet proved either an escape or a complete
characterization boundary.

- **#23 (accepted-anchor strike density): NONCIRCULAR SCALAR COMPONENT.**
  The error `epsilon_i=H_i/A_i-1/r_i` is defined without assuming a final
  survivor. Together with #13's endpoint bias it gives the exact bound
  `|b_i|<=H_i eta_i+2N_i xi_i`. The useful target is a weighted estimate for
  `sum_i w_i N_i^2 epsilon_i^2`, not necessarily a uniform pointwise
  discrepancy. A proof that normalizes by a positive late-layer population
  would nevertheless reintroduce the wall.
- Candidate #23's bulk density is not open: it cancels exactly by
  inclusion--exclusion. The missing theorem is cancellation between two
  centered Möbius boundary sums, preferably after applying the chain weights.
  This identifies a more specific target than generic local equidistribution.
- The boundary differences are not independent across layers: each is an
  adjacent difference in one boundary-error sequence. This supplies exact
  linear cancellation. Candidate #21, however, uses
  `w_i=product_{j>i}(1-2/r_j)` and squared errors, so the next theorem must
  control the cross terms `E_i E_{i+1}` or the quadratic variation of `E_i`.
- The factor `N_i/A_i` is not an additional distribution theorem. Endpoint
  disjointness proves `2N_i/A_i<=1`, so #23 reduces to a denominator-free
  weighted quadratic variation of the accepted-anchor boundary errors.
- For any `lambda_i>0`, Young's inequality separates #13 and #23:

  ```math
  b_i^2
  \le
  (1+\lambda_i)H_i^2\eta_i^2
  +
  \left(1+\frac1{\lambda_i}\right)
  \left(H_i-\frac{A_i}{r_i}\right)^2.
  ```

  The former combined-square allowance can therefore be replaced by two
  independently auditable budgets.
- At the aggregate level, optimizing the scalar composition yields
  `(sqrt(E_beta)+sqrt(E_D))^2`; arbitrary layerwise Young parameters are not
  part of the final interface. Candidate #13 owns `E_beta` and `E_Delta`,
  candidate #23 owns `E_D`, and candidate #22 owns `sum_i w_i U_i`.
- Squaring #23's adjacent boundary recurrence destroys the linear
  cancellation in a precise way: it produces positive adjacent variation,
  terminal mass, and strictly positive interior mass. The recurrence is useful
  for characterizing `E_D`, but supplies no upper bound for it.
- Primality of `Q` removes the ceiling functions and kills divisor terms
  supported on `Q-1`, but does not force sign or sign preservation. A remaining
  #23 proof would require a new mean-square estimate for a signed
  Möbius-residue sum, not another consequence of the copy/filter recurrence.
- Candidate #22 is strictly narrower than the older post-filter variance:
  recentering from `r_i` classes to the actual `r_i-2` harmless alphabet
  subtracts `2M_i^2/(r_i(r_i-2))`. This correction survives in both the
  layerwise and fixed-pair formulations.
- Writing `R_i` for ordered off-diagonal harmless pairs with
  `r_i|(x-y)`, the remaining theorem is exactly a weighted upper bound for
  `sum_i w_i R_i`; diagonal pairs and both centering terms are already known.
- The harmless recentering does not change the asymptotic verdict on
  worst-difference multiplication: its extra gain is at most `8/15` per pair,
  while the crude positive-divisor coefficient grows logarithmically.
- Candidate #22 has no complete-period distribution error. Its entire open
  content is short-window localization of an exactly balanced cyclic harmless
  class sequence.
- The off-diagonal count is candidate #20's four-endpoint pattern family after
  all four endpoints survive the current filter. Post-deletion conditioning
  is the only remaining structural distinction.
- Harmless recentering subtracts only the forced local Fourier floor. It does
  not repair generic localized estimates that retain the complete-period
  population rather than `M_i`.
- The bounded pointwise falsifier produced no counterexample, so empirical
  work stops here as planned. The result changes no proof status and does not
  justify extending the range.
- Every harmless class is a translated interval sample of one common CRT
  word. Generic uncentered sampling is still period-normalized, but this does
  not settle the candidate because `U_i` projects away the classwise constant
  mode before measuring energy.
- Harmless-class centering can make an individual Fourier mode cheap. The
  unresolved question is whether those savings survive the full
  cross-frequency quadratic form for the particular CRT coefficient vector.
- Centering alone does not improve the aggregate operator norm. Any spectral
  progress must couple exact CRT conductor factors to the centered kernel, not
  bound the coefficient vector and sampling operator independently.
- Exact-conductor restriction does improve each block, but absolute
  recombination destroys the gain. The remaining issue is quantitatively
  cross-conductor, not single-conductor.
- Conductor distinctness and coprimality do not supply cross-block
  cancellation. Any remaining #22 theorem must use the actual signed CRT
  coefficient vectors or combine layers before absolute values.
- The scalar decomposition no longer needs #13 and #23 to be proved
  separately: the Sampling-Density Recombination property exposes restricted candidate #12 as the direct
  two-harmful-class target.
- Sixfold capacity gives an exact conditional scalar criterion rather than a
  sampling theorem. Its population threshold lies strictly between #19 and
  #14. Conditional on #19's floor, the scalar gap is now confined to
  early/middle layers only at the one-layer level; #22 remains an independent
  harmless-class problem.
- Candidate #21 still needs a genuinely aggregate scalar theorem. Neither
  #19's late-layer implication nor #14's stronger local count floor allocates
  those layers inside the single global second-moment allowance.
- A new exact classification test is in progress. Define

  ```math
  E_b
  =
  \sum_iw_i\frac{r_i}{2(r_i-2)}b_i^2,
  \qquad
  W_-=\sum_iw_{i-1}.
  ```

  The Weighted Deletion Conservation property and weighted Cauchy prove

  ```math
  E_b
  \ge
  \frac{(T-N_m)^2}{2W_-}.
  ```

  Since `w_i>w_{i-1}`, one has `W>W_-`. Thus `N_m=0` implies
  `E_b>T^2/(2W)`, placing the direct harmful-excess budget on the terminal
  side of the vocabulary's scope classification when `T>0`; when `T=0`, the
  strict candidate budget is impossible by nonnegativity. The theorem and its
  exact normalized-population quadratic-variation form are now recorded in
  `properties/sieve-sequence/weighted-harmful-excess-energy-is-terminal.md`
  and registered as the Terminal Harmful-Excess Energy property.
- Candidate #12 now preserves its valid one-layer survival and capacity
  results while classifying its direct weighted harmful norm as a terminal
  conditioned-chain theorem.
- Candidate #21 now distinguishes the terminal harmful theorem from candidate
  #22's independently noncircular harmless diagnostic. Its exact recurrence,
  decomposition, and conditional implication remain unchanged.
- Candidate #22 now maps its local `M_i=N_{i+1}` notation explicitly and
  records that its harmless aggregate is redundant for survival once its
  separated scalar feasibility condition is proved. Its exact reductions and
  standalone open distribution status remain valid.
- The candidate catalog now replaces the stale parallel-component dependency
  chain with the the Terminal Harmful-Excess Energy property classification and reranks #12, #21, #22, and
  #23 accordingly.
- Candidate #13 now preserves its endpoint-sampling role while recording that
  the completed #13+#23 or direct #12 aggregate scalar interface is terminal;
  #22 is not an additional survival obligation after scalar feasibility.
- Candidate #23 now distinguishes its noncircular strike-density component
  from the terminal scalar theorem assembled with #13, and records that #22
  is not required after that scalar allowance is positive.
- The stale-role audit found no further candidate or property theorem needing
  correction. Three persistent-memory files retain superseded current
  guidance: `algebraic-conditioned-survival-2026-07-27.md`,
  `prove-endpoint-observable-sampling-2026-07-28.md`, and the completed
  `audit-one-layer-global-scope-2026-07-29.md`.
- `algebraic-conditioned-survival-2026-07-27.md` now classifies restricted
  #12 and assembled #13+#23 as terminal scalar routes, #21 as a terminal
  framework, and #22 as an independent diagnostic.
- `prove-endpoint-observable-sampling-2026-07-28.md` now classifies its
  weighted realized-capacity target as terminal and removes #22 as a later
  survival allowance.
- The completed one-layer/global audit now records the Terminal Harmful-Excess Energy property's later
  supersession and has moved to `tickets/done/`.
- A second stale-boundary scan found the Sixfold-Capacity Energy Envelope property, #63, #64, and #65 still
  describe the direct harmful aggregate as a separate component without the
  terminal classification. Their local theorems remain valid.
- the One-Layer Ellipse Non-Composition property now preserves its non-composition result while classifying
  `sum_iw_iC_i<T^2/(2W)` as a terminal capacity theorem; #22 is not a later
  survival requirement.
- the Sixfold-Capacity Energy Envelope property now labels its sharp envelope as one-layer and the direct
  cumulative realized-envelope estimate as terminal.
- the Capacity Threshold Hierarchy property now preserves its strict one-layer threshold hierarchy while
  classifying the direct aggregate harmful theorem as terminal.
- the Late-Layer Sixfold Floor property now preserves its late-layer one-layer implication while
  classifying the remaining global harmful theorem as terminal.
- All four property boundaries identified by the the Terminal Harmful-Excess Energy property follow-up scan
  are corrected.
- Final stale-role, property-link, vocabulary-scope, ticket-lifecycle, and
  repository-wide Markdown checks pass. The unrelated staged empirical CSV
  remains untouched.
- the Terminal Harmful-Excess Energy property exposes a strictly leaner terminal candidate than #21:
  `E_b<T^2/(2W_-)`. It ignores harmless dispersion and imbalance, and
  `W_-<W` gives it a larger allowance than #21's full-energy budget.
- Candidate #24,
  `candidates/weighted-harmful-excess-quadratic-survival.md`, now states this
  sharp conservation-only quadratic certificate. Its implication is proved;
  its infinitely-many-head arithmetic antecedent is open.
- The candidate catalog registers #24 as the top quadratic survival target
  and reclassifies #21 as a stronger secondary composition framework.
- the Terminal Harmful-Excess Energy property now names candidate #24 as its sharp conservation-only
  quadratic consumer and links directly to it.
- Candidate #21 now identifies #24 as the minimal quadratic target and
  retains full collision energy only as a possible source of additional
  arithmetic structure.
- Candidate #12 now identifies its full two-harmful-class ellipse as a
  stronger possible estimator while deferring to candidate #24's
  one-dimensional `b_i` energy and larger `W_-` allowance as the minimal
  quadratic survival target.
- The first actual-chain constraint audit has a sharp negative result. For
  every fixed prime chain, the Cauchy-equality extinction profile is rational,
  positive before the endpoint, and monotone. Scaling `N_0` clears all
  denominators, so every `N_i` and `K_i=N_i-N_{i+1}` is a nonnegative integer
  while

  ```math
  E_b=\frac{T^2}{2W_-},
  \qquad
  N_m=0.
  ```

  Therefore integrality, population monotonicity, and the exact recurrence
  alone cannot improve candidate #24's threshold. A successful upper bound
  must use arithmetic restrictions on which initial gaps each prime can
  delete.
- The scaled equality construction is now proved in
  `properties/sieve-sequence/integral-population-profiles-attain-harmful-energy-threshold.md`.
  Its boundary explicitly excludes CRT realizability and therefore does not
  refute candidate #24.
- The construction is registered as the Integral Profile Attainment property. Candidate #24 and the
  candidate catalog now state that population integrality and monotonicity
  are exhausted; the remaining route must use first-hit CRT deletion
  geometry.
- The Cauchy bound now has the exact stability decomposition

  ```math
  E_b
  =
  \frac{(T-N_m)^2}{2W_-}
  +
  \sum_iw_i\frac1{2a_i}
  \left(
  b_i-\frac{a_i(T-N_m)}{W_-}
  \right)^2.
  ```

  The remainder is the unique weighted distance from the endpoint-constrained
  minimizer. Under extinction it measures exactly how far an actual CRT
  deletion profile is from the Integral Profile Attainment property's abstract equality schedule.
- The identity is registered as the Harmful-Excess Stability Decomposition property. Candidate #24 now keeps its
  original upper-bound obligation separate from the optional stability-gap
  route: a positive CRT gap enlarges the survival-certifying threshold, but
  does not itself upper-bound `E_b`.
- Final candidate/property/current-ticket guidance checks pass. The existing
  first-deletion Gram, coordinate-reindexing, terminal-pair, and stopped-kernel
  properties were reread before proposing another lemma. They already prove
  that first-hit factorization or divisor-incidence swapping alone collapses
  back to the original energy. The unrelated staged empirical CSV remains
  untouched.
- The capacity-compatibility audit gives an exact new interface. With
  `p_i=2/r_i`, the Integral Profile Attainment property's equality profile has

  ```math
  K_i^\star
  =
  \frac{N_0}{S}
  \left(
  1+p_iP_iR_{i+1}
  \right).
  ```

  Therefore a proved total harmful cap `K_i<=C_i` admits the equality profile
  exactly when `K_i^star<=C_i` at every layer. If one cap is smaller, it
  excludes zero stability remainder but does not exclude extinction. Combined
  with the Harmful-Excess Stability Decomposition property, the cap supplies a quantitative lower bound on the
  stability remainder; it still supplies no upper bound for actual `E_b`.
- The full perturbation calculation is now proved in
  `properties/sieve-sequence/harmful-capacity-separates-energy-minimizer.md`.
  If `alpha_j=w_j/(2a_j)` and

  ```math
  D_i
  =
  \frac1{\alpha_i}
  +
  p_i^2
  \sum_{j<i}
  \frac{A_{j+1,i}^2}{\alpha_j},
  ```

  then every extinct profile satisfying `K_i<=C_i` obeys

  ```math
  E_b
  \ge
  \frac{T^2}{2W_-}
  +
  \max_i
  \frac{(K_i^\star-C_i)_+^2}{D_i}.
  ```

  This is the first explicit arithmetic enlargement of candidate #24's
  extinction threshold, but it remains a lower-bound interface.
- The theorem is registered as the Capacity Minimizer Separation property. Candidate #24 now contains the
  proved relaxed certificate

  ```math
  E_b
  <
  \frac{T^2}{2W_-}
  +
  \Gamma_{\mathrm{cap}},
  ```

  while preserving the missing coefficient-sensitive upper bound as the
  primary obligation.
- the Sixfold-Capacity Energy Envelope property's exact capacity polytope already gives the sharp missing
  one-layer projection for candidate #24. With population `N_i`, common
  one-class capacity `B_i`, and harmful total `K_i`,

  ```math
  \ell_i
  =
  \max(0,N_i-(r_i-2)B_i),
  \qquad
  u_i
  =
  \min(N_i,2B_i).
  ```

  Since `b_i=K_i-2N_i/r_i` and the square is convex,

  ```math
  b_i^2
  \le
  \max
  \left\{
  \left(\ell_i-\frac{2N_i}{r_i}\right)^2,
  \left(u_i-\frac{2N_i}{r_i}\right)^2
  \right\}.
  ```

  This exact b-only envelope is not yet stated as a property. It is sharper
  for #24 than the Sixfold-Capacity Energy Envelope property's full harmful-plus-imbalance maximum.
- The projection and aggregate composition are now proved in
  `properties/sieve-sequence/sharp-harmful-capacity-excess-envelope.md`.
  Defining the sharp endpoint maximum by `M_i`, one has

  ```math
  E_b
  \le
  \mathcal U_{\mathrm{cap}}
  :=
  \sum_i
  w_i\frac{r_i}{2(r_i-2)}M_i.
  ```

  Together with the Capacity Minimizer Separation property,

  ```math
  \mathcal U_{\mathrm{cap}}
  <
  \frac{T^2}{2W_-}
  +
  \Gamma_{\mathrm{cap}}
  ```

  is a proved sufficient condition for final survival. The open obligation is
  the displayed aggregate inequality for actual conditioned populations.
- The theorem is registered as the Harmful-Capacity Excess Envelope property. Candidate #24 now states the
  complete capacity-only interface:

  ```math
  E_b
  \le
  \mathcal U_{\mathrm{cap}},
  \qquad
  N_m=0
  \Longrightarrow
  E_b
  \ge
  \frac{T^2}{2W_-}
  +
  \Gamma_{\mathrm{cap}}.
  ```

  Thus the only missing capacity-only step is the explicit aggregate
  comparison between these two proved bounds.
- The strategy assessment shows that the separate-layer capacity route does
  not weaken candidate #19's abundance obligation. the Sixfold Population-Ratio Threshold property's decisive
  extremal branch has `K_i=2B_i` and zero left/right imbalance, so property
  #70's b-only envelope fits the one-layer scalar allowance exactly when

  ```math
  \frac{N_i}{B_i}
  >
  \rho_*(r_i)
  =
  \frac{2}{
  2/r_i+(1-2/r_i)^{3/2}
  }.
  ```

  Since `rho_*(r_i)>2`, this is strictly stronger than candidate #19's
  ordinary capacity-survival threshold `N_i>2B_i`.
- For a one-layer chain, `K_0^star=N_0`. If `N_0<=2B_0`, then
  `Gamma_cap=0` and the sharp capacity envelope cannot certify survival. If
  `N_0>2B_0`, the ordinary capacity theorem already certifies survival.
  The properties from Capacity Minimizer Separation through Harmful-Capacity Excess Envelope therefore create no new one-layer regime; their only
  possible gain is genuinely cross-layer.
- the Harmful-Capacity Excess Envelope property, candidate #24, and both permanent catalogs now record this
  classification. The complete capacity-only loop is synchronized:

  ```text
  proved capacities
      -> the Capacity Minimizer Separation property extinction stability gap
      -> the Harmful-Capacity Excess Envelope property sharp separate-layer upper envelope
      -> explicit terminal aggregate comparison
      -> cross-layer CRT restriction still missing
  ```
- Candidate #19 now links the properties from Capacity Minimizer Separation through Harmful-Capacity Excess Envelope and states the same boundary:
  its proved capacity can feed a cross-layer #24 argument, but the exact local
  b-only threshold remains `G/B>rho_*(r)>2`.
- The paired harmful-excess CRT observables have exact complete-period
  cancellation and cross-layer orthogonality. If `d_i` is the complete-period
  paired-survivor density, `p_i=2/r_i`, and `R` is the final CRT period, then

  ```math
  \sum_{a\bmod R}g_i(a)=0,
  \qquad
  \sum_{a\bmod R}g_i(a)g_j(a)=0
  \quad(i\ne j),
  ```

  ```math
  \lVert g_i\rVert_2^2
  =
  Rd_ip_i(1-p_i).
  ```

  Consequently, for a window of length `L<=R`, Bessel gives

  ```math
  E_b
  \le
  LR
  \max_i\frac{w_id_i}{r_i}
  =
  \frac{LRd_m}{r_0-2}.
  ```

  The factor `Rd_m` is the number of final allowed CRT classes in one full
  period and is primorial-scale. Exact cross-layer orthogonality therefore
  does not supply the short-window upper bound required by #24 when used only
  through black-box Bessel.
- This result is now promoted as
  `properties/sieve-sequence/paired-harmful-excess-crt-orthogonality-has-primorial-scale.md`.
  It is registered as the Paired CRT Primorial Scale property, uses no empirical evidence, and makes no
  Stainless claim.
- Candidate #24 now includes the Paired CRT Primorial Scale property's exact orthogonality and norm,
  rejects complete-period black-box Bessel, and states the remaining target
  as a localized interval-correlation or coefficient-sensitive inequality.
- Candidate #24's catalog entry and detailed algebraic next step are
  synchronized with the Paired CRT Primorial Scale property. The repository now consistently rejects
  complete-period Bessel as the missing estimate.
- A sharper algebraic composition is available before introducing an unproved
  localized-correlation hypothesis. For a cut `k`, the prefix observables
  `g_0,...,g_(k-1)` all have periods dividing `M_k` and remain orthogonal over
  that native period. If

  ```math
  s_k=L\bmod M_k,
  ```

  complete blocks cancel and native-period Bessel bounds the prefix energy by

  ```math
  \mathcal B_k
  =
  \begin{cases}
  0,&k=0,\\
  \dfrac{s_kM_kd_m}{r_0-2},&1\le k\le m.
  \end{cases}
  ```

  This coarse prefix estimate can be combined sharply with the Harmful-Capacity Excess Envelope property,
  rather than merely chosen instead of it. Put

  ```math
  q_{i,k}=M_kd_ip_ia_i,
  \qquad
  \alpha_i=\frac{w_i}{2a_i},
  \qquad
  c_{i,k}=\frac{M_i^{\mathrm{cap}}}{q_{i,k}}.
  ```

  With `y_i=b_i^2` and `t_i=y_i/q_(i,k)`, the exact available constraints for
  the prefix are

  ```math
  0\le t_i\le c_{i,k},
  \qquad
  \sum_{i<k}t_i\le s_k.
  ```

  Their objective coefficients are

  ```math
  \beta_{i,k}
  =
  \alpha_iq_{i,k}
  =
  \frac{M_kd_m}{r_i-2},
  ```

  which decrease with `i`. Therefore the sharp capacity-truncated Bessel
  envelope fills the indices in order:

  ```math
  t_{i,k}^{\star}
  =
  \min
  \left(
  c_{i,k},
  \left(
  s_k-\sum_{j<i}c_{j,k}
  \right)_+
  \right),
  ```

  ```math
  \mathcal H_k
  =
  \sum_{i<k}\beta_{i,k}t_{i,k}^{\star}.
  ```

  The Harmful-Capacity Excess Envelope property bounds the suffix. Thus the proposed sharp hybrid is

  ```math
  \mathcal U_k^{\mathrm{hyb}}
  =
  \mathcal H_k
  +
  \sum_{i=k}^{m-1}
  w_i\frac{r_i}{2(r_i-2)}M_i^{\mathrm{cap}}.
  ```

  The cut `k=0` is the all-capacity envelope, so minimizing over `k` can never
  weaken the Harmful-Capacity Excess Envelope property. Without the box constraints, `k=m` reduces to property
  #71's complete-period Bessel bound when `L<R`.
- The corrected sharp theorem is now promoted as
  `properties/sieve-sequence/native-period-bessel-capacity-hybrid-envelope.md`.
  It proves

  ```math
  E_b
  \le
  \mathcal U_{\mathrm{hyb}}
  \le
  \mathcal U_{\mathrm{cap}},
  ```

  with strict improvement at cut `k` exactly when

  ```math
  \sum_{i<k}
  \frac{M_i^{\mathrm{cap}}}{M_kd_ip_ia_i}
  >
  s_k.
  ```

  The theorem also composes with the Capacity Minimizer Separation property's extinction gap. It does not
  prove that the resulting terminal inequality holds universally.
- The theorem is registered as the Native-Period Hybrid Envelope property in the permanent property
  catalog.
- Candidate #24 now states the Native-Period Hybrid Envelope property's sharp native-period/capacity
  envelope, exact strict-gain criterion, and relaxed survival certificate.
  Its limitation correctly remains the unproved aggregate threshold comparison
  for an unbounded family of actual chains.
- Candidate #24's catalog entry and detailed algebraic next step are now
  synchronized. Both name `U_hyb`, not the superseded all-capacity comparison,
  as the strongest proved explicit envelope.
- the Native-Period Hybrid Envelope property's exact greedy program has a useful scalar consequence. Define

  ```math
  e_k
  =
  \left(
  \sum_{i<k}c_{i,k}-s_k
  \right)_+.
  ```

  The greedy solution excludes exactly `e_k` units of normalized capacity
  mass. Since the smallest prefix objective coefficient is

  ```math
  \beta_{k-1,k}
  =
  \frac{M_kd_m}{r_{k-1}-2},
  ```

  the gain over all-capacity satisfies

  ```math
  \Delta_k
  :=
  \mathcal U_{\mathrm{cap}}
  -
  \mathcal U_k^{\mathrm{hyb}}
  \ge
  \frac{M_kd_m}{r_{k-1}-2}e_k.
  ```

  This gives a simpler scalar sufficient comparison once proved formally.
- The scalar comparison is now proved in
  `properties/sieve-sequence/native-period-capacity-overflow-quantifies-hybrid-gain.md`.
  In fact,

  ```math
  \frac{M_kd_m}{r_{k-1}-2}e_k
  \le
  \Delta_k
  \le
  \frac{M_kd_m}{r_0-2}e_k,
  ```

  so `e_k>0` is exactly strict hybrid gain, and its lower coefficient gives
  the advertised simplified survival criterion. The result adds no new
  cancellation source and leaves the overflow-to-threshold comparison open.
- The scalar theorem is registered as the Native-Period Capacity Overflow property in the permanent property
  catalog.
- Candidate #24 now includes the Native-Period Capacity Overflow property's exact overflow definition,
  two-sided hybrid-gain bound, simplified survival certificate, and explicit
  open lower-bound obligation.
- Final consistency audit passes: the properties from Paired CRT Primorial Scale through Native-Period Capacity Overflow exist and are numbered,
  candidate #24 and both permanent catalogs agree on `U_hyb` and `e_k`,
  `git diff --check` is clean, and the separately staged giant CSV remains
  untouched.
- The first overflow-floor audit is complete algebraically. For one layer,
  let

  ```math
  \ell=\max(0,N-(r-2)B),
  \qquad
  u=\min(N,2B),
  \qquad
  \mu=\frac{2N}{r}.
  ```

  Then the sharp capacity envelope has the exact midpoint form

  ```math
  X
  =
  \left(
  \frac{u-\ell}{2}
  +
  \left|
  \mu-\frac{\ell+u}{2}
  \right|
  \right)^2,
  ```

  and its feasible width is

  ```math
  u-\ell
  =
  \min(N,2B,rB-N).
  ```

  Consequently,

  ```math
  X
  \ge
  \frac14
  \min(N,2B,rB-N)^2.
  ```

  The Native-Period Capacity Overflow property therefore receives the explicit overflow floor

  ```math
  e_k
  \ge
  \left(
  \sum_{i<k}
  \frac{
  \min(N_i,2B_i,r_iB_i-N_i)^2
  }{
  4M_kd_ip_ia_i
  }
  -
  s_k
  \right)_+.
  ```

  This floor is useful only through actual population slack. For `B>0`,
  `X=0` exactly at `N=0` or `N=rB`; in particular, positive `N` does not
  imply a positive population-independent floor because the fully occupied
  feasible profile `N=rB` also has `X=0`.
- The result is promoted as
  `properties/sieve-sequence/capacity-envelope-width-floor-needs-population-slack.md`.
  It includes the exact midpoint identity, the three-case width proof, the
  zero characterization, and the induced the Native-Period Capacity Overflow property survival certificate.
- The theorem is registered as the Envelope Width Floor property in the permanent property
  catalog.
- Candidate #24 now includes the Envelope Width Floor property's population-slack floor, exact
  zero characterization, induced overflow certificate, and the requirement
  for an unbounded-family slack theorem or localized residue input.
- The conditional #17-to-#24 population-slack bridge is proved. For
  `Q>=17`, `7<=r<Q`, and `B=floor((Q^2-Q-3)/(6r))+1`, candidate #17's
  local-count threshold gives `N>=2B`. Independently, the three possible
  modulo-30 start classes give `N<=(r-2)B`. Hence the Envelope Width Floor property's slack is
  exactly `sigma=2B`, and its width floor is the maximal value `X>=B^2`.
  This does not prove candidate #17; it identifies exactly what #17 would
  contribute to candidate #24.
- The filter-`7` specialization supplies unconditional positive native
  overflow. With `r_0=5`, `r_1=7`, cut `k=2`, `M_2=210`, and pre-filter-`7`
  pair density `3/30`, the exact norm is `q_(1,2)=30/7`. The proved seven-layer
  floor gives `X_1>=B_7^2`, so `e_2>=1` for every integer `Q>=36`. The Native-Period Capacity Overflow property
  therefore gives a strict capacity-envelope reduction
  `Delta_2>=42d_m e_2`. This is an unconditional envelope improvement, not a
  survival theorem.
- The exact fixed-cut scale audit is complete. If candidate #17's threshold
  holds at the first untouched layer `r_2=11`, then for every chain with
  `Q>=17` and `m>=37`,

  ```math
  \mathcal U_2^{\mathrm{hyb}}
  >
  \frac{T^2}{2W_-}.
  ```

  The proof lower-bounds the untouched filter-`11` suffix term by
  `(847/486)P_m(D/66)^2` and upper-bounds the original threshold by
  `P_m(D/6+1)^2/(2m)`. Thus the positive filter-`7` overflow cannot make the
  fixed `k=2` envelope certify the original #24 threshold on long chains.
  Later cuts and the capacity-relaxed threshold remain open.
- The arbitrary-cut scale audit is complete. Under candidate #17 at the first
  untouched layer, cut `k` cannot clear the original threshold whenever
  `m>P_k(r_k-2)^2(1+6/D)^2`. Thus every fixed `k` eventually fails. Since
  `P_k<=P_2=3/7`, threshold clearance requires
  `r_k>=2+sqrt(7m/3)/(1+6/D)`. This is a necessary moving-prime rate, not a
  sufficient cut construction.
- The moving-cut complete-block audit is complete. If a cut both clears the
  original threshold and has `M_k<=H`, then a finite theta lower bound and
  Bertrand force
  `m<(3/7)(1+6/D)^2(2log(H)/c-2)^2`. PNT gives
  `m=pi(Q)-3~Q/log(Q)`, so this inequality eventually fails. Therefore every
  sufficiently large potentially successful cut has `M_k>H` and remainder
  `s_k=H`. This uses Bertrand/PNT as explicit external dependencies and does
  not rule out one-incomplete-block Bessel gain.
- The one-incomplete-block audit is complete. The finite bound
  `sum_(i<k) X_i/q_(i,k)<=3kD^2r_k^2/(25M_kP_k(r_k-2))` gives the exact
  sufficient criterion
  `M_kP_k>=3kD^2r_k^2/(25H(r_k-2))` for `e_k=0`. PNT makes the left side
  exponentially large in the required moving-cut prime while the right side
  is polynomial, so every sufficiently large potentially successful moving
  cut has `e_k=0` and `U_k^hyb=U_cap`. With the Filter-Seven Cut Failure property's
  `U_cap>=U_2^hyb>T^2/(2W_-)`, no native cut clears the original threshold
  under full candidate #17.
- The `Gamma_cap` scale audit is complete. For every `i>=1`, the minimizing
  deletion mass satisfies
  `K_i^star-C_i<=N_0/S-(2D-18)/(15r_i)`. Thus the finite condition
  `S>=15QN_0/(2D-18)` removes every post-5 capacity violation. The only
  possible contribution then obeys
  `Gamma_cap<=(25P_m/18)(2/5+3N_0/(5S))^2`. In contrast, candidate #17 at
  filter `7` and the Seven-Layer Density Floor property give
  `U_cap>=P_mD^2/1080`, while the original threshold is at most
  `P_m(D/6+1)^2/(2m)`. Prime Mertens plus PNT give
  `S` of order `Q log Q`, so the finite condition holds and both allowance
  terms are negligible relative to the filter-7 envelope floor. The relaxed
  capacity threshold therefore cannot rescue the separate capacity envelope
  on an unbounded family under full candidate #17.
- The first localized actual-energy audit succeeds sharply at filter `7`.
  In one modulo-`210` period, the 21 admissible starts have centered weights
  `7g_7` equal to six copies of `5` and fifteen copies of `-2`. In residue
  order their cumulative sums range from `-8` to `10`, so every interval has
  `|b_7|<=18/7`. Consequently the actual filter-`7` energy is at most
  `(49P_m/30)(18/7)^2=54P_m/5`, replacing the separate capacity charge
  `>=P_mD^2/1080`. This is a genuine `D^2`-scale saving, but it controls only
  one fixed early layer.
- The direct generalization of the Filter-Seven Excess Bound property is not a new algebraic route.
  The Sampling-Density Recombination property gives `b_i=delta_(0,i)+delta_(-2,i)`, so the general native
  prefix discrepancy is exactly the two-residue accepted-boundary arithmetic
  already reduced in candidate #23. Complete-period cancellation removes the
  bulk, but independent inclusion--exclusion summands give an exponential
  bound, and total variation over the native residue certificate grows with
  `prod_(j<i)(r_j-2)`. Scaling #82 therefore requires a new signed mean-square
  or Möbius-boundary cancellation theorem, not further fixed-period
  enumeration.

### Independent property-catalog audit (2026-07-29)

Independent reviewer (me) surveyed all ~40 new `properties/sieve-sequence/`
notes and verified a stratified sample across three tiers per
`TICKET_DISCIPLINE.md` §6 (verify, don't trust on authority):

- **Tier 1 — negative/insufficiency results: all SOUND and carefully scoped.**
  Verified the arithmetic of `black-box-large-sieve-does-not-fit-weighted-
  collision-budget` (`λ₀=A/3`, `3NA ≤ L/2+3 < 2(L+Q²)` for `Q≥7`), the integer
  histogram counterexample in `pointwise-two-class-does-not-imply-collision-
  budget` (`Q/(T²/2) = 1+1/(r(r−2)) > 1`), and the Cauchy-Schwarz composition
  obstruction in `one-layer-harmful-ellipses-do-not-compose`
  (`W·Σ(1/wᵢ) ≥ m² ≥ 4 > 2`). All properly scoped as "tool cannot certify,"
  not "candidate is false."
- **Tier 2 — load-bearing positive identities: all SOUND.** Verified
  `two-class-survival-from-collision-energy` (variance identity `V_r=C_r−N²/r`
  exact; sufficient energy inequality `2V_r<N²(1−2/r)² ⇒ K_r<N` clean),
  `harmful-residue-capacity-after-filter-three` (5-mod-6 ⇒ separation 6r ⇒
  one-class capacity `⌊L_Q/(6r)⌋+1`; threshold `N≥2⌊L_Q/(6r)⌋+3 ⇒ N−K_r≥1`
  correct). Plus the earlier-validated `stable-small-k-shot-spacing`,
  `local-count-forces-k2`, `interval-premise-from-pair-existence` (corrected
  form).
- **Tier 3 — heavy-machinery spot-check: no overclaim found.** Spot-checked
  `fourier-two-gap-correlation-prefix-bound`: the fourth-moment identity
  `|1+z|⁴ = 6+4(z+z⁻¹)+z²+z⁻²` summed over `p`-th roots (annihilating
  nonconstant powers for `p≥5`, giving `6p`; trivial char 16; nontrivial
  `6p−16`) is exactly correct. CRT factorization of the product-set Fourier
  transform is standard. Honestly scoped as complete-period/large-prefix, not
  short-window.

**Net verdict:** the new body of work is mathematically sound and
methodologically disciplined. It does NOT change the wall characterization —
it *sharpens* it: converts "blocked by something parity-like" into a precise
inventory of which standard tools fail (proved), what the one viable shape is
(specialized four-point dispersion for `{0,2,d,d+2}`), and why that is hard
(it would itself imply final-window positivity). Real progress on
understanding the obstruction, not a proof that escapes it.

## Failed Paths

- **#19 hereditary population floor:** explicitly demands order-`Q` local
  abundance at late layers.
- **#20 absolute-to-relative normalization:** returns to a lower bound for the
  unknown conditioned population.
- **#21 signed harmful-excess conservation:** exactly equivalent to final
  survival and therefore circular when used alone.
- **#21 worst-difference, generic Fourier, black-box large-sieve, and symmetric
  capacity estimates:** independently audited and quantitatively too weak.
- **Blanket implication test:** rejected. Classifying every sufficient theorem
  as "the same wall" merely because it implies survival cannot distinguish a
  circular premise from an independently provable upper bound.
- **Unsigned inclusion--exclusion for #23:** bounding every centered divisor
  term separately gives
  `|E_P(L,U)|<tau(P)-1=2^omega(P)-1`, exponentially large in the number of
  installed filters. Retry only with signed Möbius cancellation, correlation
  between the original and scaled boundary sums, or weighted cross-layer
  cancellation.
- **Using #23's linear telescope as the quadratic estimate:** the exact
  one-anchor weighted sum controls signed first powers only. Candidate #21
  needs differently weighted squares, and squaring introduces uncontrolled
  adjacent products `E_iE_{i+1}`. Retry only with a quadratic-variation,
  sign-correlation, or monotonicity theorem for the boundary errors.
- **Summation by parts of #23's squared recurrence:** exact expansion does not
  produce favorable cancellation. After reindexing, all interior mass
  coefficients are strictly positive; only the known initial boundary term is
  negative. Retry only if new arithmetic information directly upper-bounds
  the square-window boundary-error magnitude or variation.
- **Prime-square universal sign or sign preservation for #23:** refuted
  exactly. For `Q=19`, `E_2310=-5/77`, while adjoining filter `13` gives
  `E_30030=1403/1001>0`. Retry only with an averaged cancellation theorem that
  does not assume a fixed sign.
- **#23 activation, CRT-lift, and summatory rewrites as upper bounds:**
  The properties from Strike Divisor-Activation Kernel through Strike Summatory Remainder prove exact compressed forms, but all represent the same
  dilation discrepancy and supply no inequality by themselves. Retry only
  with new spectral or analytic input.
- **#23 complete-period layer orthogonality plus Bessel:** the Cross-Layer CRT Orthogonality property is
  exact, but its norm retains the full final primorial. Retry only after
  localization or with an additional averaging variable.
- **#23 localized Gram trace/self-bound:** the Localized-Layer Gram Matrix property removes the primorial,
  but the trace is exactly the sum of per-layer Cauchy bounds. Retry only with
  a sharper estimate using the signed nested off-diagonal matrix.
- **#23 first-deletion spectral factorization without new arithmetic:**
  The properties from First-Deletion Variance Identity through First-Deletion Reindexing factor the matrix, identify its exact deletion-class
  variance, and reindex the whole variance back to `sum_i c_iD_i^2`. Retry
  only with arithmetic constraints on deletion counts or external averaging.
- **#21 local ellipse composition:** the One-Layer Ellipse Non-Composition property proves that even strict
  success at every one-layer scalar threshold can exceed the global weighted
  allowance by a factor at least `m^2/2`. Retry only with a direct estimate of
  `sum_i w_i Q_i` or `sum_i w_i C_i`, using actual cross-layer arithmetic.
- **Treating restricted #12's global harmful norm as an independently
  noncircular component:** the new conditioned-chain theorem proves its
  `b_i^2` component alone is above candidate #21's allowance whenever the
  final population is zero. Retry only as an explicitly terminal theorem, or
  change the composition framework so it uses signed conservation without
  imposing this quadratic budget.
- **Candidate #22 synchronization patch, attempt 1:** the patch expected a
  duplicated `(x,y) in S_{i+1}^2` line copied from truncated terminal output,
  but the file contains that condition only once. No file changed. Retry
  against the exact current block; this is a context-generation failure, not
  a mathematical failure.
- **Candidate #23 synchronization patch, attempt 1:** one hunk omitted the
  source's article “the” before `separate #23`, and the cleanup hunk expected a
  duplicated URL where the actual duplication is the preceding bullet label.
  No file changed. Retry against the exact current text; this is a patch
  context failure, not a failed theorem.
- **Candidate #23 synchronization patch, attempt 2:** the supposed duplicated
  bullet label was itself an artifact of two overlapping `sed` output ranges.
  Line-numbered inspection proves the source contains exactly one label and
  one URL. No file changed. The final retry must omit cleanup entirely and use
  only independently confirmed source contexts.
- **Completed audit-ticket closure, attempt 1:** the move patch expected a
  What is Learned sentence not present in the source. No file changed or
  moved. Retry with exact anchors from each persistent-memory section; this is
  a context-generation failure, not a mathematical failure.

## Open Concerns

- Candidate #22's pointwise benchmark may be stronger than the weighted
  aggregate #21 actually needs.
- Although `U_i<=N_{i+1}` is noncircular at zero population, a proposed proof
  might reintroduce the wall by normalizing an absolute correlation estimate
  with an unproved lower bound for `N_{i+1}`.
- Endpoint sampling controls `beta_i` and `Delta_i`, but the accepted-strike
  density error `epsilon_i=H_i/A_i-1/r_i` still lacks a candidate theorem.
  Candidate #10 does not directly control it.
- The ordinary large sieve, generic Fourier localization, worst-difference
  bounds, and symmetric class capacity are already quantitatively
  insufficient. A new proposal must identify the structural gain it adds.
- The exact threshold `mathcal U_*(Q)` can be nonpositive if the scalar error
  budgets consume the complete #21 allowance; constants must be audited
  before harmless dispersion is attacked.
- Candidate #23 now has exact activation-shell, CRT-lift, summatory-remainder,
  complete-period orthogonality, localized Gram, and first-deletion
  formulations. None proves the weighted strike-density bound. Its generic
  algebraic audit is complete, and the remaining target is a new arithmetic
  mean-square estimate for the exact summatory dilation remainders.
- The Möbius boundary identity currently counts every accepted anchor in an
  interval. Candidate #13 trims anchors whose fixed-radius neighborhood
  crosses the boundary. An explicit endpoint-correction lemma is required
  before the identity can be inserted into #13/#23 without qualification.
- The endpoint-density contraction resolves the magnitude of `N_i/A_i`, but
  does not control the boundary-error quadratic variation. Choosing
  the optimal aggregate composition still requires independent bounds for
  both the #13 and #23 budgets.
- the Strike-Error Quadratic Variation property is a lower-energy decomposition, not the upper estimate
  candidate #23 requires. Without special information about the endpoints
  `[Q,Q^2)`, further algebraic rearrangement of the same recurrence is a loop.
- the Prime-Square Boundary Formula property supplies exact endpoint information but no usable universal
  bound. Proving the required mean-square cancellation for its Möbius-residue
  sum may be as difficult as the original conditioned distribution problem;
  its strength has not yet been classified against known parity barriers.
- The extra negative correction in the Harmless-Energy Pair Correlation property is genuine, but it does not
  control the positive off-diagonal pair count by itself. A worst-difference
  estimate multiplied by `N_0^2` remains forbidden by the earlier #21 audit.
- **#22 extra centering plus worst-difference:** the new negative gain is at
  most `8/15` per pair and therefore cannot repair the old logarithmic
  positive-divisor bound. Retry only with aggregate pair incidence or
  correlation cancellation, not another per-difference maximum.
- **#22 harmless recentering plus generic localized Fourier bounds:** the floor
  subtraction is local, while the existing Young/conductor estimates retain
  the complete-period population. Retry only with a localized spectral
  inequality normalized by `M_i` or with difference-kernel cancellation.
- **#22 uncentered inverse-phase large-sieve sampling:** phase spacing alone
  gives a large-sieve factor of complete-period size. Retry only after the
  harmless-class mean projection is inserted into the phase Gram matrix.
- **#22 centered black-box operator norm:** full Fourier row orthogonality
  gives the sharp norm `sqrt(P)` after centering and returns exactly to
  full-shift Parseval. Retry only with arithmetic alignment of the actual CRT
  coefficient vector or after summing chain weights.
- **#22 conductor blocks plus triangle inequality:** individual squared norms
  fall below `r+2q`, but summing block norms introduces
  `prod_(p|P)(1+sqrt(2/(p-2)))`. Retry only with cross-conductor cancellation
  or an almost-orthogonal square sum.
- **#22 distinct/coprime conductor orthogonality:** refuted exactly by
  `P=30`, `r=7`, `q=2`, `q'=3`, where the centered squared cross norm is
  `168/25`. Retry only with coefficient-weighted cancellation; conductor
  labels alone are insufficient.
- **Transform-only first-hit rewrite for #24:** the properties from First-Deletion Variance Identity through First-Deletion Reindexing and the
  weighted pair-kernel identities already show that Gram factorization,
  coordinate reindexing, or divisor-incidence swapping without a new mass
  constraint closes back to the original quadratic energy. Do not add another
  first-deletion identity as a substitute for an estimate.
- **Capacity-property validation regex:** the first post-correction search
  used an unsupported escape sequence and returned no mathematical result.
  Fixed-string validation succeeded; do not retry the malformed regex.
- **LaTeX formula validation in regex mode:** a second search repeated the
  unsupported `\mathrm` escape class while checking candidate #24. It changed
  no file and fixed-string validation passed. Do not use regex mode for LaTeX
  formulas again in this ticket.
- **Wrapped/case-sensitive fixed-string validation:** two later searches
  missed correct catalog text because one phrase changed case and another was
  split across Markdown lines. Exact-range reads and `git diff --check`
  passed. Validate wrapped prose by reading its range rather than guessing
  one physical-line string.
- **Literal anchor in fixed-string mode:** the final catalog search used
  `rg -F "^69."`, which treats `^` literally and therefore did not match the
  numbered entry. An exact-range read confirmed entries #69 and #70. Do not
  mix regex anchors with fixed-string mode.
- **Paired harmful-excess complete-period Bessel:** the observables are exactly
  orthogonal, but their norms are proportional to the full final CRT period.
  The resulting bound is `LRd_m/(r_0-2)`, far above the square-window scale.
  Do not retry complete-period orthogonality without a genuinely localized
  coefficient or interval-correlation estimate.
- **Candidate #24 the Paired CRT Primorial Scale property synchronization, attempt 1:** the patch expected
  a wrapped `the properties from Capacity Minimizer Separation through Harmful-Capacity Excess Envelope are` line that is not present as a separate
  physical line. No candidate file changed. The exact numbered source range is
  now captured; retry only against those confirmed anchors.
- **Native-prefix hybrid draft, endpoint normalization:** the first ticket
  formula assigned a Bessel prefix term at `k=0` even though that prefix is
  empty. It was corrected immediately to `B_0=0`. Preserve the explicit
  endpoint convention in the promoted theorem.
- **Candidate catalog the Native-Period Hybrid Envelope property synchronization:** validation found one
  stale sentence still calling the `U_cap` comparison “the remaining target.”
  The first cleanup patch then missed because its context wrapped
  `enlargement` differently from the source. Exact numbered inspection enabled
  the final permitted correction; the catalog now consistently uses `U_hyb`.
- **Positive capacity-overflow floor from `r_i,B_i` alone:** impossible.
  the Harmful-Capacity Excess Envelope property's sharp coordinate envelope vanishes on the feasible profiles
  `N_i=0` and `N_i=r_iB_i`. Retry only with a quantitative restriction keeping
  some actual population away from both empty and full capacity, or with
  localized residue information beyond the capacity box.
- **Finish #24 by enlarging only the proved filter-`7` overflow:** blocked for
  the fixed `k=2` envelope. Under candidate #17 at `r=11`, the untouched
  filter-`11` capacity term alone exceeds the original extinction threshold
  for `m>=37`. Retry only by moving the cut so filter `11` and later layers
  enter the joint Bessel budget, by using `Gamma_cap` quantitatively, or by
  proving localized information that reduces the suffix below its capacity
  maximum.
- **Replace filter `7` by any other fixed native cut:** blocked for the
  original threshold under candidate #17 at the first untouched layer. The
  exact obstruction is
  `m>P_k(r_k-2)^2(1+6/D)^2`. Retry only with a cut index growing with the
  chain, the capacity-relaxed `Gamma_cap` allowance, or localized suffix
  control.
- **Use a moving cut while retaining complete native blocks:** asymptotically
  blocked for the original threshold under candidate #17 at the first suffix
  layer. The exact finite retry condition is
  `m<(3/7)(1+6/D)^2(2log(H)/c-2)^2` under
  `theta(r_(k-1))>=c r_(k-1)` and Bertrand. PNT shows the actual full chain
  eventually violates it. Retry only through the one-incomplete-block Bessel
  constraint, the capacity-relaxed threshold, or a different localized
  estimate.
- **Use native-period Bessel on the remaining incomplete block:**
  asymptotically blocked for the original threshold under full candidate #17.
  The finite retry condition is failure of
  `M_kP_k>=3kD^2r_k^2/(25H(r_k-2))`; PNT shows this failure cannot persist at
  the moving-prime scale forced by the Fixed Native Cut Failure property. Retry only with a smaller
  localized upper bound replacing `X_i`, the capacity-relaxed `Gamma_cap`
  threshold, or a different cross-layer inequality.
- **Use `Gamma_cap` to rescue the separate/native capacity envelope:**
  asymptotically blocked under full candidate #17. The Capacity Stability Gap property proves that
  all post-`5` minimizer capacities eventually fit and
  `Gamma_cap<=(25P_m/18)(2/5+3N_0/(5S))^2`, while filter `7` forces
  `U_cap>=P_mD^2/1080`. PNT/Mertens make both the original threshold and the
  stability gap negligible relative to this envelope floor. Retry only with
  a smaller localized upper bound for actual `E_b` or a genuinely different
  joint cross-layer inequality.
- **Generalize the Filter-Seven Excess Bound property by enumerating each larger native period:** does
  not scale. The coefficient is exactly the two-residue boundary discrepancy
  already isolated by candidate #23. Generic inclusion--exclusion is
  exponential in the installed-prime count, while total-variation control
  grows with the native accepted population. Retry only with a signed
  mean-square/cross-layer cancellation theorem or a proved recursive prefix
  bound that beats this growth.

## Next Action

The Filter-Seven Excess Bound property is registered and synchronized. Stop at the strategy boundary:
its direct native-period enumeration generalization converges to candidate
#23's already-classified boundary discrepancy. The next useful theorem must
be genuinely new arithmetic information: either a signed mean-square bound
for the two harmful boundary sums after chain weights are inserted, or a
recursive prefix-discrepancy bound whose growth is sub-native. Do not create a
duplicate candidate for the same boundary identity.

Treat the Harmful-Excess Stability Decomposition property's positive extinction gap as secondary unless the same
arithmetic input also supplies, or materially relaxes, a usable upper bound
for actual `E_b`.

Do not restart the exhausted #22/#23 generic algebraic routes and do not
collect additional empirical evidence.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-27 | Ticket created. Inherited wall: every per-layer/chain population bound tested so far reduces to twin-prime-strength short-window positivity. #14, #10, the chain-population reframe, the sqrt-recurrence all converged there. | Read #19-#21 and apply the reduction test to each. |
| 2026-07-27 | The original audit used an overbroad test: every sufficient theorem implies survival, but that does not make every independently estimable component circular. New algebra gives `V_i=U_i+r_i b_i^2/(2(r_i-2))+Delta_i^2/2`, and #22's `U_i<=N_{i+1}` remains valid at zero population. | Expanded the audit to #22, reclassified #21 as a terminal consumer, withdrew the premature complete-characterization claim, and selected the weighted harmless-energy bound as the decisive next escape-wall test. |
| 2026-07-27 | All current #19-#22 research artifacts are synchronized; stale-claim, stopping-index, ticket-section, relative-link, and Markdown checks pass. | Closed the documentation audit. Next derive and strength-test `mathcal U_*(Q)` without using a final-population lower bound. |
| 2026-07-27 | Candidate #23 now isolates accepted-anchor strike density from #10. The exact bridge gives `|b_i|<=H_i eta_i+2N_i xi_i`, and the resulting scalar terms can be subtracted explicitly from #21's allowance for weighted harmless energy. | Add #23 to the catalog, then audit whether its weighted error can be bounded without late-population normalization. |
| 2026-07-27 | Accepted strikes equal a coprime count in a scaled interval. Centered inclusion--exclusion cancels the bulk density exactly and leaves two Möbius boundary sums; the unsigned bound is exponential and unusable. | Promoted the exact identity, recorded unsigned inclusion--exclusion as failed, and selected weighted boundary cancellation plus the #13 endpoint correction as the next algebraic test. |
| 2026-07-27 | The centered strike discrepancy is exactly `(1-1/r_i)E_i-E_{i+1}` and therefore telescopes linearly under one-anchor weights. The #21 obligation is quadratic and uses two-endpoint weights, so the linear conservation law is not sufficient. | Narrowed #23 to weighted quadratic variation of adjacent boundary errors, with `(N_i/A_i)^2` and endpoint trimming as the next coefficients to audit. |
| 2026-07-27 | Post-3 endpoint isolation proves `2N_i<=A_i`, hence `|2N_i epsilon_i|<=|H_i-A_i/r_i|`. Young's inequality then separates the #13 endpoint bias from #23's boundary discrepancy. | Promoted the Endpoint Discrepancy Contraction property, removed `N_i/A_i` from #23's open target, and selected the denominator-free scalar allowance as the next #22 refinement. |
| 2026-07-27 | Weighted Minkowski combines #13 and #23 sharply at the aggregate level: the scalar cost is `(sqrt(E_beta)+sqrt(E_D))^2+E_Delta`. | Promoted the Weighted Error Composition property, synchronized #22/#23, and isolated `E_D` as a weighted quadratic variation of adjacent accepted-anchor boundary errors. |
| 2026-07-27 | The exact square expansion of #23 is a positive quadratic energy: every interior mass coefficient is positive, so the linear strike telescope cannot upper-bound the squared budget. | Promoted the Strike-Error Quadratic Variation property, recorded summation by parts as exhausted without new boundary arithmetic, and selected square-window endpoint structure as the go/no-go test. |
| 2026-07-27 | Prime-square endpoints give the exact residue sum `sum mu(d)([Q]_d-[Q^2]_d)/d`, but an exact `Q=19` chain changes sign after adjoining filter `13`. Universal sign and sign preservation are refuted. | Promoted the Prime-Square Boundary Formula property, cataloged the failed sign laws under `candidates/refuted/`, classified further #23 recurrence algebra as exhausted without new mean-square input, and recommended shifting primary work to #22. |
| 2026-07-27 | Candidate #22 is an ordered harmless-survivor pair correlation on `S_0`. Relative to the old post-filter variance, it has the exact negative correction `2M_i^2/(r_i(r_i-2))`, and its kernel stops before the deleting layer. | Promoted the Harmless-Energy Pair Correlation property and reduced the next theorem to the weakest weighted upper bound for the off-diagonal harmless collision count `sum_i w_i R_i`. |
| 2026-07-27 | The extra harmless centering is at most `8/15` per pair, so it cannot offset the logarithmic coefficient in the failed worst-difference bound. | Recorded the combined route as failed and selected the exact post-deletion autocorrelation sum for the next aggregate-pair analysis. |
| 2026-07-27 | Harmless classes are exactly uniform over a complete CRT period, so `U=0`; complete blocks cancel and all #22 energy is remainder-prefix energy. The off-diagonal term is the conditioned version of candidate #20's four-point correlation. | Promoted the Harmless-Class Uniformity property, removed stale #23 instructions from Next Action, and selected a short-prefix spectral audit for #22. |
| 2026-07-27 | Candidate #22 is the localized nontrivial Fourier mass above the sharp two-empty-class floor. Generic spectral localization still retains the complete-period population, so harmless recentering does not repair its scale. | Promoted the Harmless Spectral Excess property, recorded generic localized Fourier composition as failed, and selected a bounded exact falsifier for the stronger pointwise benchmark `U_i<=M_i`. |
| 2026-07-27 | The bounded exact falsifier found no violation of `U_i<=M_i` in 1,035 layers for prime heads `5<=Q<224`; the independent lineage tests pass. Finite agreement is inconclusive and supplies no proof evidence. | Stopped empirical work at the predetermined bound and selected the exact CRT translated-fiber normal form as the next algebraic audit. |
| 2026-07-27 | Every harmless-class count is an interval sum of one common prior-filter CRT word at phase `ceil((Q-a)/r)+sa`; the phases are almost equally spaced, but uncentered Parseval and generic large-sieve sampling remain period-normalized. | Promoted the CRT Fiber Translation property, synchronized candidate #22, recorded the uncentered route as failed, and selected the centered inverse-phase Gram matrix as the next exact lemma. |
| 2026-07-27 | Harmless-class centering has exact single-mode cost `h-|K_m|^2/h`, but the full energy contains cross-frequency Gram entries `K_(m-n)-K_m K_(-n)/h`; it is not a diagonal Fourier sum. | Promoted the Inverse-Phase Gram Matrix property, synchronized candidate #22, and selected an exact full-operator audit before attempting coefficient estimates. |
| 2026-07-27 | The inverse phases have orthogonal full-Fourier rows, and harmless-class centering leaves sharp operator norm `sqrt(P)`; black-box composition returns exactly to full-shift Parseval scale. | Promoted the Phase-Operator Norm Bound property, synchronized candidate #22, recorded centered operator-norm composition as failed, and selected an audit of arithmetic alignment by exact CRT conductor. |
| 2026-07-27 | Restricting to exact conductor `q` improves the squared phase-block norm to `q mu_q<r+2q`, but triangle recombination introduces an oversized square-root divisor product. | Promoted the Conductor Phase-Block Bound property, synchronized candidate #22, recorded absolute block recombination as failed, and selected the exact centered Ramanujan cross-block geometry as the next test. |
| 2026-07-27 | Exact Ramanujan geometry shows distinct and even coprime conductor blocks are not centered-orthogonal; an exact pair has squared normalized coherence `2793/3203`. | Promoted the Ramanujan Cross-Conductor Geometry property, cataloged the refuted orthogonality law, classified further unweighted finite-Fourier rearrangement as exhausted, and selected dedicated #23 mean-square work. |
| 2026-07-28 | Dedicated #23 work promoted the properties from Strike Divisor-Activation Kernel through Localized-Layer Gram Matrix: activation shells, CRT lift indices, summatory dilation remainders, complete-period layer orthogonality, and the exact localized Gram matrix. Complete-period Bessel retains the primorial, while local trace composition is only per-layer Cauchy. | Synchronized the umbrella ticket with the dedicated #23 ticket and selected the first-deletion rank-one factorization as the live algebraic micro-goal. |
| 2026-07-28 | the properties from First-Deletion Variance Identity through First-Deletion Reindexing factor the localized strike Gram matrix by deletion time, identify its exact negative variance, and reindex that variance completely back to the original strike energy. First-deletion geometry supplies no independent upper bound without new arithmetic mass constraints. | Closed candidate #23's generic algebraic audit and handed the next top-candidate work to #13's endpoint-sampling component. |
| 2026-07-29 | the properties from Joint Capacity Envelope through Late-Layer Sixfold Floor reduce #13+#23 to the direct two-harmful-residue norm, derive its sharp sixfold-capacity ratio, place that ratio strictly between #19 and #14, and show #19's floor already suffices in the explicit late-layer range. | Synchronized the umbrella assessment and selected the weighted early/middle harmful-capacity contribution as the remaining scalar audit. |
| 2026-07-29 | the One-Layer Ellipse Non-Composition property proves that one-layer harmful ellipses do not compose into #21's global allowance; even half-local energies overrun it by at least `m^2/2` on the ideal multiplicative scale. | Corrected candidate #21 and both active tickets, recorded the local-to-global route as failed, and stopped at the required strategy checkpoint. |
| 2026-07-29 | the Weighted Deletion Conservation property plus weighted Cauchy appears to give `E_b> T^2/(2W)` whenever `N_m=0`, because the natural dual weight sum is `W_-<W`. | Reopened the checkpoint for one exact classification theorem before spending effort on another scalar upper bound. |
| 2026-07-29 | The weighted lower bound is proved: `E_b> T^2/(2W)` when `N_m=0` and `T>0`, while the strict budget is impossible when `T=0`. Equivalently, `E_b<T^2/(2W)` already forces `N_m>0`. The same energy is exactly the quadratic variation of normalized population. | Added the standalone property; next register it as #66 and correct the candidate roles. |
| 2026-07-29 | The terminal harmful-excess theorem is registered as the Terminal Harmful-Excess Energy property in the permanent catalog. | Correct candidate #12's description of its direct weighted aggregate role. |
| 2026-07-29 | Candidate #12 now distinguishes its valid one-layer sufficient margin from its terminal conditioned-chain quadratic target. | Correct candidate #21's decomposition and next-step interpretation. |
| 2026-07-29 | Candidate #21 now identifies the harmful-excess square as terminal and candidate #22 as an independent but insufficient harmless diagnostic. | Correct candidate #22's strategic role without changing its formulas or open status. |
| 2026-07-29 | The first #22 synchronization patch made no change because one context line was duplicated in captured terminal output but not in the source file. | Recorded the tooling-context failure and regenerated the edit from the exact file text. |
| 2026-07-29 | Candidate #22 now states that its harmless theorem is independently noncircular but redundant for survival after the separated scalar feasibility condition; its local `M_i` notation is mapped explicitly. | Rerank the candidate catalog and replace the stale parallel-component dependency chain. |
| 2026-07-29 | The candidate catalog now classifies #12 and #21 as terminal, #22 as an independent diagnostic, and #23 as a fallback terminal-scalar representation. | Correct the remaining stale #13 and #23 role language. |
| 2026-07-29 | Candidate #13 now distinguishes its local sampling theorem from the terminal aggregate scalar interface and no longer lists #22 as an additional survival obligation after scalar feasibility. | Correct candidate #23's fallback scalar role. |
| 2026-07-29 | The first #23 synchronization patch made no change because two contexts were generated from an imprecise read: one missing article and one misidentified duplicate line. | Recorded the tooling-context failure and regenerated the edit from exact source text. |
| 2026-07-29 | The second #23 synchronization patch made no change because overlapping read ranges falsely displayed one bullet twice. | Confirmed the source with line numbers; make one final retry containing only role corrections and the new property link. |
| 2026-07-29 | Candidate #23 now keeps its standalone strike estimate noncircular while classifying the #13+#23 aggregate scalar theorem as terminal; the final permitted patch retry succeeded. | Audit active guidance for the superseded parallel-component strategy. |
| 2026-07-29 | The stale-role audit found the permanent candidates and properties synchronized. Three current ticket-guidance sections still preserve the pre-#66 #12+#22 frontier. | Correct those current sections one file at a time while preserving historical logs. |
| 2026-07-29 | The algebraic-conditioned-survival ticket now records the Terminal Harmful-Excess Energy property as controlling and stops the exhausted #22-first route. | Correct the endpoint-observable ticket's aggregate target and open concerns. |
| 2026-07-29 | The endpoint-observable ticket now classifies `sum_iw_iC_i` below the #21 allowance as a terminal theorem and no longer treats #22 as a subsequent survival requirement. | Update and close the completed one-layer/global audit ticket. |
| 2026-07-29 | The first completed-audit closure patch made no change because one planned What is Learned context was not present in the source. | Recorded the context failure and regenerated the lifecycle patch from exact section text. |
| 2026-07-29 | The completed audit now records the Terminal Harmful-Excess Energy property's supersession and is in `tickets/done/`. A follow-up scan found four property boundaries with pre-Terminal-Harmful-Excess-Energy component language. | Correct the One-Layer Ellipse Non-Composition, Sixfold-Capacity Energy Envelope, Capacity Threshold Hierarchy, and Late-Layer Sixfold Floor properties one at a time. |
| 2026-07-29 | the One-Layer Ellipse Non-Composition property now states the sharp later result: a direct weighted capacity envelope below #21's global allowance already forces survival by the Terminal Harmful-Excess Energy property. | Correct the Sixfold-Capacity Energy Envelope property's Boundary. |
| 2026-07-29 | the Sixfold-Capacity Energy Envelope property now distinguishes its exact one-layer envelope from the terminal cumulative realized-envelope theorem. | Correct the Capacity Threshold Hierarchy property's final hierarchy boundary. |
| 2026-07-29 | the Capacity Threshold Hierarchy property now states that its threshold hierarchy is one-layer and the open direct aggregate harmful theorem is terminal. | Correct the Late-Layer Sixfold Floor property's final boundary. |
| 2026-07-29 | the Late-Layer Sixfold Floor property now states that its late-layer result is one-layer and the remaining direct global harmful estimate is terminal. All the Terminal Harmful-Excess Energy property boundary corrections are complete. | Run the final cross-repository audit. |
| 2026-07-29 | Final audit passes. The Terminal Harmful-Excess Energy property also reveals a sharper terminal condition than #21: use only `E_b` and the natural allowance `T^2/(2W_-)`, which is strictly larger because `W_-<W`. | Create candidate #24 and rank it above #21 as the leanest current quadratic survival target. |
| 2026-07-29 | Candidate #24 now records the sharp conservation-only quadratic threshold, its normalized-population variation form, and the proved terminal implication. | Register and rank #24 in the candidate catalog. |
| 2026-07-29 | The catalog now registers #24 as the top quadratic survival target and shows `#21 => #24 => survival`; #22 remains independent. | Link the Terminal Harmful-Excess Energy property and candidate #21 directly to #24. |
| 2026-07-29 | the Terminal Harmful-Excess Energy property now names and links candidate #24 as its sharp conservation-only quadratic condition. | Synchronize candidate #21 as the stronger secondary framework. |
| 2026-07-29 | Candidate #21 now defers to #24 as the minimal quadratic survival condition and keeps full energy only where it may add arithmetic leverage. | Correct candidate #12's aggregate target hierarchy. |
| 2026-07-29 | Candidate #12 now distinguishes its stronger full two-class ellipse from candidate #24's minimal one-dimensional harmful-excess energy and larger natural allowance. | Audit the actual-chain constraints on the normalized-population quadratic variation before proposing another theorem. |
| 2026-07-29 | For every fixed prime chain, the Cauchy-equality extinction profile is a rational monotone population profile; scaling `N_0` makes all populations and deletions integral without changing equality. Integrality and monotonicity therefore cannot improve #24's threshold. | Promote the algebraic boundary as a property, then require genuine residue/deletion geometry in the next candidate step. |
| 2026-07-29 | The integral equality construction is now a standalone property with a narrow boundary: it refutes population-only strengthening but does not realize the schedule by CRT residue classes. | Register it as the Integral Profile Attainment property and synchronize candidate #24. |
| 2026-07-29 | the Integral Profile Attainment property is registered, and candidate #24 plus its catalog entry now require genuine CRT deletion geometry rather than population-only constraints. | Derive the exact square-completion remainder around the Cauchy minimizer. |
| 2026-07-29 | Exact square completion gives `E_b=(T-N_m)^2/(2W_-)+sum_i w_i(b_i-b_i^*)^2/(2a_i)` with a unique minimizer. Under extinction, the remainder is precisely the distance from the Integral Profile Attainment property's equality profile. | Register the identity as the Harmful-Excess Stability Decomposition property and expose the separate upper-bound and stability-gap interfaces in candidate #24. |
| 2026-07-29 | the Harmful-Excess Stability Decomposition property is registered. Candidate #24 now states correctly that a positive CRT stability gap only enlarges the certificate threshold and must still be paired with an upper bound for actual `E_b`. | Synchronize the candidate catalog and audit current guidance for stale population-only or gap-alone strategies. |
| 2026-07-29 | Final synchronization passes. Existing first-deletion Gram/reindexing and weighted pair-kernel properties show that transform-only first-hit algebra returns to the original energy; the staged empirical CSV is untouched. | Stop at the checkpoint. Next require a genuinely new CRT mass restriction before proposing an upper-bound candidate for actual `E_b`. |
| 2026-07-29 | The equality deletion mass is `K_i^*=(N_0/S)(1+(2/r_i)P_iR_(i+1))`. A harmful-class cap below this value excludes the Cauchy minimizer and yields a positive stability gap, but it does not exclude extinction or upper-bound `E_b`. | Promote the exact compatibility and gap formula, preserving the separate upper-bound obligation. |
| 2026-07-29 | The cap violation now has an explicit dual-norm gap: extinction forces `E_b>=T^2/(2W_-)+max_i (K_i^*-C_i)_+^2/D_i`. The theorem is algebraic and uses the proved harmful capacities. | Register the result as the Capacity Minimizer Separation property and synchronize candidate #24 without claiming an energy upper bound. |
| 2026-07-29 | One validation search used an invalid regex escape; it changed no file. Fixed-string searches and `git diff --check` pass. | Record the tooling failure and do not retry that regex. |
| 2026-07-29 | the Capacity Minimizer Separation property is registered, and candidate #24 now includes the proved `Gamma_cap` relaxed certificate while retaining the separate upper-bound obligation. | Synchronize the candidate catalog, then return to actual-energy control. |
| 2026-07-29 | A second validation command repeated the unsupported LaTeX escape in regex mode; it changed no file. Fixed-string validation passed. | Ban regex-mode LaTeX validation for the remainder of the ticket. |
| 2026-07-29 | the Sixfold-Capacity Energy Envelope property's feasible interval projects sharply onto `b_i^2`: its capacity-only maximum is the larger endpoint square over `ell_i<=K_i<=u_i`. This is sharper for #24 than the full two-coordinate envelope. | Promote the b-only envelope and combine its weighted sum with the Capacity Minimizer Separation property's enlarged threshold. |
| 2026-07-29 | The sharp b-only envelope is proved: `E_b<=U_cap`, and `U_cap<T^2/(2W_-)+Gamma_cap` is sufficient for survival. The aggregate inequality remains open and population-profile dependent. | Register the result as the Harmful-Capacity Excess Envelope property, synchronize #24, and assess whether the explicit target escapes candidate #19's abundance wall. |
| 2026-07-29 | the Harmful-Capacity Excess Envelope property is registered, and candidate #24 now has a proved sharp capacity-only upper envelope paired with the Capacity Minimizer Separation property's enlarged extinction threshold. | Update the catalog and classify whether the remaining aggregate comparison is weaker than candidate #19's population floor. |
| 2026-07-29 | The b-only capacity envelope has exactly the Sixfold Population-Ratio Threshold property's threshold `N_i/B_i>rho_*(r_i)>2`, because the decisive filled-harmful branch has zero imbalance. In one layer, `Gamma_cap` is zero below ordinary capacity survival and redundant above it. | Classify separate-layer capacity optimization as exhausted; preserve the Capacity Minimizer Separation and Harmful-Capacity Excess Envelope properties only as a possible cross-layer interface. |
| 2026-07-29 | the Harmful-Capacity Excess Envelope property, candidate #24, and both catalogs now state that the capacity-only route has no new one-layer regime. Its only remaining value is a joint cross-layer restriction lowering the sum of separately sharp endpoint maxima. | Stop at the cross-layer checkpoint; reject further independent one-layer envelopes. |
| 2026-07-29 | Two fixed-string validations missed correct prose because of case and physical-line wrapping; exact-range reads passed. | Use exact-range reads for wrapped prose and keep fixed strings for formulas. |
| 2026-07-29 | Candidate #19 now records how its capacities feed the properties from Capacity Minimizer Separation through Harmful-Capacity Excess Envelope while preserving its unchanged local-abundance boundary. All directly affected permanent artifacts are synchronized. | Run the final consistency audit and retain only the joint cross-layer CRT problem as the next useful #24 work. |
| 2026-07-29 | The final fixed-string catalog search mistakenly used a literal regex anchor; exact-range validation confirmed entries #69--#70 and `git diff --check` passed. | Record the validation misuse and stop without further search variants. |
| 2026-07-29 | The paired harmful-excess observables are exactly mean-zero and mutually orthogonal over the final CRT period, with norm `Rd_i(2/r_i)(1-2/r_i)`. Black-box Bessel yields `E_b<=LRd_m/(r_0-2)`, retaining the primorial-scale class count. | Promote the exact boundary and reject complete-period Bessel as the missing #24 estimate. |
| 2026-07-29 | The paired orthogonality theorem is now a standalone property. It proves the exact cross-layer geometry while classifying its direct Bessel use as quantitatively insufficient for a short safe window. | Register it as the Paired CRT Primorial Scale property and narrow candidate #24's next theorem to localized interval correlations or actual-coefficient cancellation. |
| 2026-07-29 | The first candidate #24 synchronization patch made no change because its context assumed a prose wrap not present in the source. | Captured the exact numbered range; make one corrected patch using confirmed anchors. |
| 2026-07-29 | the Paired CRT Primorial Scale property is registered, and candidate #24 now rules out complete-period Bessel while requiring localized interval correlations or coefficient-sensitive cancellation. | Synchronize the candidate catalog and audit the resulting proof frontier. |
| 2026-07-29 | The catalog is synchronized. Using each prefix's native period gives a concrete hybrid: cancel complete `M_k` blocks and apply Bessel to layers `<k`, then use the Harmful-Capacity Excess Envelope property's capacity envelope on layers `>=k`. The `k=0` cut recovers the all-capacity bound, so optimization cannot be worse. | Prove the exact hybrid formula and test its algebraic strength before proposing any new correlation hypothesis. |
| 2026-07-29 | The initial hybrid draft incorrectly charged the empty `k=0` prefix; the endpoint is now `B_0=0`. Combining prefix Bessel with each `b_i^2` capacity is a linear program whose ratios `M_kd_m/(r_i-2)` decrease with `i`, so greedy saturation gives the sharp combined envelope. | Promote the corrected sharp hybrid as a property, then compare it algebraically with the all-capacity bound. |
| 2026-07-29 | The sharp native-period/capacity hybrid is proved. It always improves or matches `U_cap`, improves strictly exactly when the normalized prefix capacity box exceeds the interval remainder `s_k`, and composes with `Gamma_cap` to give a terminal survival criterion. | Register as the Native-Period Hybrid Envelope property and synchronize candidate #24 and the catalogs. |
| 2026-07-29 | the Native-Period Hybrid Envelope property is registered in the permanent property catalog. | Add its hybrid certificate and exact gain criterion to candidate #24. |
| 2026-07-29 | Candidate #24 now uses `U_hyb` as its strongest proved capacity/orthogonality envelope and preserves the universal threshold comparison as open. | Synchronize the candidate catalog and reassess the remaining algebraic obligation. |
| 2026-07-29 | Candidate #24 and both catalogs are synchronized after removing one stale `U_cap` target; the first cleanup patch missed a wrapped context, and the exact-range retry succeeded. The greedy hybrid rejects exactly the normalized overflow `e_k`, giving a prospective gain at least `M_kd_m e_k/(r_(k-1)-2)`. | Prove the scalar overflow-gain lemma and compose it with the extinction threshold. |
| 2026-07-29 | The scalar overflow theorem is proved: the exact hybrid gain lies between the smallest and largest prefix coefficient times `e_k`, yielding a simplified terminal certificate. | Register as the Native-Period Capacity Overflow property and synchronize candidate #24 and the catalogs. |
| 2026-07-29 | the Native-Period Capacity Overflow property is registered in the permanent property catalog. | Add the overflow certificate and its open lower-bound obligation to candidate #24. |
| 2026-07-29 | Candidate #24 now states the Native-Period Capacity Overflow property's scalar overflow certificate and identifies a lower bound for `e_k` at the extinction-deficit scale as the next independent input. | Synchronize the candidate catalog and run the final consistency audit. |
| 2026-07-29 | Final audit passes: the properties from Paired CRT Primorial Scale through Native-Period Capacity Overflow, candidate #24, and both catalogs are synchronized; no stale `U_cap` target remains; Markdown is clean; the staged giant CSV is untouched. | Stop at the overflow checkpoint until an independent lower bound for `e_k` or stronger localized correlation input is available. |
| 2026-07-29 | The sharp capacity envelope has exact width `min(N,2B,rB-N)` and is at least one quarter of its square, yielding an explicit lower bound for `e_k`. The bound necessarily vanishes at empty and fully occupied feasible populations, so `r,B` alone cannot force positive overflow. | Promote the width-floor theorem and require actual population slack or localized residue input next. |
| 2026-07-29 | The capacity-width floor and population-free obstruction are now a standalone property, including their composition with the Native-Period Capacity Overflow property's survival certificate. | Register as the Envelope Width Floor property and synchronize candidate #24 and the catalogs. |
| 2026-07-29 | the Envelope Width Floor property is registered in the permanent property catalog. | Add its population-slack floor and population-free obstruction to candidate #24. |
| 2026-07-29 | Candidate #24 now states the Envelope Width Floor property's population-slack overflow floor and proves why `r_i,B_i` alone cannot make it positive. | Synchronize the candidate catalog and run the final audit. |
| 2026-08-03 | the Envelope Width Floor property is synchronized across candidate #24 and both catalogs. Candidate #17's count threshold appears to force the Envelope Width Floor property's maximal population-slack width: the lower side is a floor comparison, and the upper side follows from the three allowed start classes modulo `30`. | Make the conditional #17-to-#24 middle-regime bridge the next one-lemma proof; do not claim either candidate is thereby proved. |
| 2026-08-03 | The #17-to-#24 bridge is proved: #17 gives `N>=2B`, installed filter `5` gives `N<=(r-2)B`, and therefore the Envelope Width Floor property has `sigma=2B` and `X>=B^2`. | Register the bridge as the Seven-Layer Density Floor property, then compare its normalized `B_i^2` sum with the Native-Period Capacity Overflow property's remainder budget before claiming any cross-candidate gain. |
| 2026-08-03 | The proved `r=7` floor makes the first native overflow unconditional: `q_(1,2)=30/7` and `e_2>=(7B_7^2/30-s_2)_+>=1` for every `Q>=36`. Hence the Native-Period Capacity Overflow property strictly improves the capacity envelope by at least `42d_m e_2`. | Promote as the Seven-Layer Overflow Forcing property, then compare the quantified gain with candidate #24's exact extinction deficit; strict improvement is not yet survival. |
| 2026-08-03 | the Seven-Layer Overflow Forcing property is registered and candidates #17/#24 and both permanent catalogs now distinguish unconditional strict hybrid gain from the still-open survival comparison. | Audit whether the fixed `k=2` envelope can clear the original or capacity-relaxed extinction threshold; if not, state the exact obstruction and move only to later cuts or localized information. |
| 2026-08-03 | The fixed cut after filter `7` cannot clear the original #24 threshold on long chains under candidate #17 at the first untouched layer: for `m>=37`, the filter-`11` suffix term alone gives `U_2^hyb>T^2/(2W_-)`. | Promote as the Filter-Seven Cut Failure property; stop enlarging the settled filter-`7` overflow and test whether the same obstruction holds for every fixed cut. |
| 2026-08-03 | the Filter-Seven Cut Failure property is registered and candidate #24 and both catalogs now classify the fixed `k=2` route. All Markdown, link, and stale-claim checks pass; the Stainless baseline remains `30/0/0` and the unrelated staged giant CSV is untouched. | Generalize the suffix comparison to arbitrary fixed `k`; determine whether a successful native cut must grow with the future head. |
| 2026-08-03 | The suffix comparison generalizes exactly: cut `k` fails the original threshold when `m>P_k(r_k-2)^2(1+6/D)^2`. Every fixed cut therefore eventually fails, and `P_k<=3/7` gives the necessary movement rate `r_k>=2+sqrt(7m/3)/(1+6/D)`. | Promote as the Fixed Native Cut Failure property; next compare this necessary movement with the native-modulus requirement for useful complete-block cancellation. |
| 2026-08-03 | the Fixed Native Cut Failure property is registered and candidate #24 and both catalogs now classify every fixed cut. The repository has no internal primorial-growth lemma strong enough for the next comparison; Bertrand and PNT are already used elsewhere as explicit external mathematical dependencies. | Prove an exact conditional `m=O(log^2 H)` bound for cuts with `M_k<=H`, then use PNT only in a separately labeled asymptotic corollary. |
| 2026-08-03 | A moving cut that clears the original threshold and retains `M_k<=H` must satisfy an exact logarithmic-squared chain bound under a finite theta lower bound and Bertrand. PNT makes that bound incompatible with `m=pi(Q)-3` for all sufficiently large heads, so any potentially successful cut has `M_k>H` and `s_k=H`. | Promote as the Moving-Cut Block Loss property; next test whether the one-incomplete-block Bessel budget can exclude any capacity mass at all. |
| 2026-08-03 | The incomplete-block capacity sum is at most `3kD^2r_k^2/(25M_kP_k(r_k-2))`; if the corresponding finite product inequality holds, then `e_k=0`. PNT makes it hold at every sufficiently large moving cut, so the current native hybrid cannot clear the original #24 threshold under full #17. | Promote as the Incomplete-Block Bessel Bound property and stop the exhausted native-period route; next choose between `Gamma_cap` and localized actual-energy control. |
| 2026-07-29 | Independent reviewer (separate agent) audited the full ~40 new properties per `TICKET_DISCIPLINE.md` §6. Stratified sample across 3 tiers (negative/insufficiency, load-bearing positive identities, heavy-machinery). | All checked notes are mathematically SOUND and carefully scoped. Net: the new work sharpens the wall (precise inventory of which standard tools fail, the one viable shape left) but does not escape it. Recorded as "Independent property-catalog audit" subsection in What is Learned. No corrections needed to the team's properties. |
| 2026-08-03 | the Incomplete-Block Bessel Bound property, candidate #24, and both catalogs are synchronized; stale transitional claims that incomplete-block Bessel remained open were corrected. Markdown and link checks pass, the Stainless baseline remains `30/0/0`, and the unrelated staged giant CSV is untouched. | Stop at the strategy boundary. Prefer auditing `Gamma_cap` first because it stays inside #24's proved scalar framework; use localized actual-energy control only if that audit shows no asymptotic room. |
| 2026-08-03 | The user selected the recommended `Gamma_cap` branch. Existing properties (Capacity Minimizer Separation through Harmful-Capacity Excess Envelope) already reduce it to `U_cap<T^2/(2W_-)+Gamma_cap`; no separate ticket or stronger existing lemma was found. | Compare the minimizer-capacity violations with the aggregate envelope excess under full candidate #17, without retrying exhausted one-layer or native-period arguments. |
| 2026-08-03 | The `Gamma_cap` comparison closes algebraically: after a finite `S` condition all post-5 minimizer capacities fit, the remaining gap is at most `(25P_m/18)(2/5+3N_0/(5S))^2`, but candidate #17 forces `U_cap>=P_mD^2/1080` already at filter `7`. PNT/Mertens make both the original threshold and `Gamma_cap` negligible against this floor. | Promote the finite and asymptotic obstruction as the Capacity Stability Gap property, then synchronize candidate #24 and both catalogs. |
| 2026-08-03 | the Capacity Stability Gap property is registered and synchronized across candidate #24, both catalogs, and the boundaries of the properties from Moving-Cut Block Loss through Incomplete-Block Bessel Bound. The stability gap is eventually positive but cannot rescue the separately maximized capacity envelope under full #17. | Stop at the strategy boundary; next prefer localized control of actual `b_i^2`, with a genuinely joint cross-layer inequality as the fallback. |
| 2026-08-03 | At filter `7`, the modulo-`210` centered-weight certificate has cumulative range `18`, proving the sharp interval bound `|b_7|<=18/7` and actual energy contribution at most `54P_m/5`. This replaces the capacity-envelope charge of order `P_mD^2` by a boundary constant. | Promote as the Filter-Seven Excess Bound property, then test which part of the cumulative-discrepancy argument scales to a general native period. |
| 2026-08-03 | the Filter-Seven Excess Bound property is registered and synchronized across candidate #24 and both catalogs. It proves a genuine fixed-layer localized saving without claiming uniformity in the growing native modulus. | Compare the general cumulative discrepancy with candidate #23's existing boundary arithmetic before proposing a scalable theorem. |
| 2026-08-03 | The general the Filter-Seven Excess Bound property coefficient is exactly `b_i=delta_(0,i)+delta_(-2,i)`, the accepted-boundary discrepancy already classified in candidate #23. Fixed-period enumeration scales with the native accepted population and generic inclusion--exclusion is exponential, so neither supplies the required chain bound. | Stop rather than duplicate #23; continue only with a new signed mean-square/cross-layer cancellation input or a sub-native recursive prefix bound. |
| 2026-08-03 | the Filter-Seven Excess Bound property, candidate #24, both catalogs, and the active-ticket cold-start guidance are synchronized. The positive fixed-layer theorem and the failed naive scaling route are both preserved; no candidate was refuted. | Stop at the new-arithmetic boundary until a signed mean-square/cross-layer cancellation theorem or sub-native recursive discrepancy bound is selected. |
