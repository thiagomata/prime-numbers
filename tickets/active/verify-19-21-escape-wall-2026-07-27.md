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
component, or terminal consumer. Property #66 now classifies restricted #12's
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
preferred scalar representation. Property #66 proves that either aggregate
representation is terminal at candidate #21's global allowance.

Property #65 now proves that the one-layer capacity thresholds do not compose
into #21's global allowance, even on the ideal multiplicative population
scale. The correct scalar interface is a direct weighted aggregate for the
realized harmful energies or capacity envelopes.

Properties #66--#70 and candidate #24 give the complete separate-layer
capacity boundary. Properties #71--#73 now give the first cross-layer
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

Property #71 proves exact complete-block cancellation, cross-layer
orthogonality, and norms. Final-period Bessel retains the primorial and is
exhausted. Property #72 instead uses every intermediate native period,
intersects its prefix Bessel budget sharply with coordinate capacities, and
proves

```math
E_b
\le
\mathcal U_{\mathrm{hyb}}
\le
\mathcal U_{\mathrm{cap}}.
```

Property #73 defines the normalized capacity overflow

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

Start from this overflow checkpoint. The next useful input must independently
lower-bound some `e_k` at the scale of the remaining extinction deficit, or
provide localized interval correlations stronger than the native-period
Bessel budget. Do not restart complete-period Bessel, separate-layer capacity
optimization, first-deletion reindexing, or empirical-range extension.

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
- Property #43 gives the exact translated-fiber form
  `d_a=rho ell_a+E_(ell_a)(v_a)`, where
  `v_a=ceil((Q-a)/r)+sa`, `s=r^(-1) mod P`, the lengths differ by at most
  one, and distinct phases are spaced on the order of `P/r`. The remaining
  pointwise theorem is centered `L^2` discrepancy on these explicit phases.
- Property #44 evaluates the centered inverse-phase Gram matrix. Its
  single-frequency cost is `h-|K_m|^2/h`, its phase sum `K_m` is an explicit
  collapsed geometric expression, and its cross-frequency entry is
  `K_(m-n)-K_m K_(-n)/h`. The full quadratic form is not diagonal.
- Property #45 proves the inverse phases have orthogonal full-Fourier rows:
  `AA^*=PI` and `CAA^*C=PC`. The centered operator norm is sharply `sqrt(P)`,
  so black-box composition reproduces the full-shift Parseval energy exactly;
  the one-unit fiber-length correction has the same period-scale boundary.
- Property #46 restricts to exact conductor `q`. If `mu_q` is the largest
  inverse-phase multiplicity modulo `q`, then the squared block norm is at
  most `q mu_q<r+2q`, and the interval multiplier contributes
  `min(ell,q)`. This is a genuine conductor-scale improvement, but triangle
  recombination creates an oversized square-root divisor sum.
- Property #47 gives the exact centered cross-conductor Ramanujan trace.
  Distinct conductor blocks are not orthogonal: already at `P=30`, `r=7`,
  the coprime pair `q=2`, `q'=3` has squared cross norm `168/25`. Another pair
  has squared normalized Hilbert--Schmidt coherence `2793/3203`.
- Properties #56--#58 solve #13's exact endpoint-capacity geometry and prove
  that #13 plus #23 is precisely the sum/difference decomposition of the two
  harmful start-residue deviations.
- Properties #59--#62 show that the old pointwise survival margin is
  insufficient, solve the sharp harmful-energy capacity envelope, and reduce
  its one-layer criterion exactly to

  ```math
  G>\rho_*(r)B.
  ```

- Properties #63--#64 place this threshold strictly below #14's count floor,
  classify when #19's `2B+1` floor is enough, and prove that it is enough
  throughout `Q^2-Q-3<3r(r-1)`, in particular
  `r>=Q/sqrt(3)+1`.
- Property #65 proves that these one-layer comparisons do not imply #21's
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
  separately: property #58 exposes restricted candidate #12 as the direct
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

  Property #25 and weighted Cauchy prove

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
  and registered as property #66.
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
  chain with the property #66 classification and reranks #12, #21, #22, and
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
- The completed one-layer/global audit now records property #66's later
  supersession and has moved to `tickets/done/`.
- A second stale-boundary scan found properties #61, #63, #64, and #65 still
  describe the direct harmful aggregate as a separate component without the
  terminal classification. Their local theorems remain valid.
- Property #65 now preserves its non-composition result while classifying
  `sum_iw_iC_i<T^2/(2W)` as a terminal capacity theorem; #22 is not a later
  survival requirement.
- Property #61 now labels its sharp envelope as one-layer and the direct
  cumulative realized-envelope estimate as terminal.
- Property #63 now preserves its strict one-layer threshold hierarchy while
  classifying the direct aggregate harmful theorem as terminal.
- Property #64 now preserves its late-layer one-layer implication while
  classifying the remaining global harmful theorem as terminal.
- All four property boundaries identified by the property #66 follow-up scan
  are corrected.
- Final stale-role, property-link, vocabulary-scope, ticket-lifecycle, and
  repository-wide Markdown checks pass. The unrelated staged empirical CSV
  remains untouched.
- Property #66 exposes a strictly leaner terminal candidate than #21:
  `E_b<T^2/(2W_-)`. It ignores harmless dispersion and imbalance, and
  `W_-<W` gives it a larger allowance than #21's full-energy budget.
- Candidate #24,
  `candidates/weighted-harmful-excess-quadratic-survival.md`, now states this
  sharp conservation-only quadratic certificate. Its implication is proved;
  its infinitely-many-head arithmetic antecedent is open.
- The candidate catalog registers #24 as the top quadratic survival target
  and reclassifies #21 as a stronger secondary composition framework.
- Property #66 now names candidate #24 as its sharp conservation-only
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
- The construction is registered as property #67. Candidate #24 and the
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
  deletion profile is from property #67's abstract equality schedule.
- The identity is registered as property #68. Candidate #24 now keeps its
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
  `p_i=2/r_i`, property #67's equality profile has

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
  with property #68, the cap supplies a quantitative lower bound on the
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
- The theorem is registered as property #69. Candidate #24 now contains the
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
- Property #61's exact capacity polytope already gives the sharp missing
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
  for #24 than property #61's full harmful-plus-imbalance maximum.
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

  Together with property #69,

  ```math
  \mathcal U_{\mathrm{cap}}
  <
  \frac{T^2}{2W_-}
  +
  \Gamma_{\mathrm{cap}}
  ```

  is a proved sufficient condition for final survival. The open obligation is
  the displayed aggregate inequality for actual conditioned populations.
- The theorem is registered as property #70. Candidate #24 now states the
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
  not weaken candidate #19's abundance obligation. Property #62's decisive
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
  Properties #69--#70 therefore create no new one-layer regime; their only
  possible gain is genuinely cross-layer.
- Property #70, candidate #24, and both permanent catalogs now record this
  classification. The complete capacity-only loop is synchronized:

  ```text
  proved capacities
      -> property #69 extinction stability gap
      -> property #70 sharp separate-layer upper envelope
      -> explicit terminal aggregate comparison
      -> cross-layer CRT restriction still missing
  ```
- Candidate #19 now links properties #69--#70 and states the same boundary:
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
  It is registered as property #71, uses no empirical evidence, and makes no
  Stainless claim.
- Candidate #24 now includes property #71's exact orthogonality and norm,
  rejects complete-period black-box Bessel, and states the remaining target
  as a localized interval-correlation or coefficient-sensitive inequality.
- Candidate #24's catalog entry and detailed algebraic next step are
  synchronized with property #71. The repository now consistently rejects
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

  This coarse prefix estimate can be combined sharply with property #70,
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

  Property #70 bounds the suffix. Thus the proposed sharp hybrid is

  ```math
  \mathcal U_k^{\mathrm{hyb}}
  =
  \mathcal H_k
  +
  \sum_{i=k}^{m-1}
  w_i\frac{r_i}{2(r_i-2)}M_i^{\mathrm{cap}}.
  ```

  The cut `k=0` is the all-capacity envelope, so minimizing over `k` can never
  weaken property #70. Without the box constraints, `k=m` reduces to property
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

  The theorem also composes with property #69's extinction gap. It does not
  prove that the resulting terminal inequality holds universally.
- The theorem is registered as property #72 in the permanent property
  catalog.
- Candidate #24 now states property #72's sharp native-period/capacity
  envelope, exact strict-gain criterion, and relaxed survival certificate.
  Its limitation correctly remains the unproved aggregate threshold comparison
  for an unbounded family of actual chains.
- Candidate #24's catalog entry and detailed algebraic next step are now
  synchronized. Both name `U_hyb`, not the superseded all-capacity comparison,
  as the strongest proved explicit envelope.
- Property #72's exact greedy program has a useful scalar consequence. Define

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
- The scalar theorem is registered as property #73 in the permanent property
  catalog.
- Candidate #24 now includes property #73's exact overflow definition,
  two-sided hybrid-gain bound, simplified survival certificate, and explicit
  open lower-bound obligation.
- Final consistency audit passes: properties #71--#73 exist and are numbered,
  candidate #24 and both permanent catalogs agree on `U_hyb` and `e_k`,
  `git diff --check` is clean, and the separately staged giant CSV remains
  untouched.

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
  properties #48--#50 prove exact compressed forms, but all represent the same
  dilation discrepancy and supply no inequality by themselves. Retry only
  with new spectral or analytic input.
- **#23 complete-period layer orthogonality plus Bessel:** property #51 is
  exact, but its norm retains the full final primorial. Retry only after
  localization or with an additional averaging variable.
- **#23 localized Gram trace/self-bound:** property #52 removes the primorial,
  but the trace is exactly the sum of per-layer Cauchy bounds. Retry only with
  a sharper estimate using the signed nested off-diagonal matrix.
- **#23 first-deletion spectral factorization without new arithmetic:**
  properties #53--#55 factor the matrix, identify its exact deletion-class
  variance, and reindex the whole variance back to `sum_i c_iD_i^2`. Retry
  only with arithmetic constraints on deletion counts or external averaging.
- **#21 local ellipse composition:** property #65 proves that even strict
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
- Property #38 is a lower-energy decomposition, not the upper estimate
  candidate #23 requires. Without special information about the endpoints
  `[Q,Q^2)`, further algebraic rearrangement of the same recurrence is a loop.
- Property #39 supplies exact endpoint information but no usable universal
  bound. Proving the required mean-square cancellation for its Möbius-residue
  sum may be as difficult as the original conditioned distribution problem;
  its strength has not yet been classified against known parity barriers.
- The extra negative correction in property #40 is genuine, but it does not
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
- **Transform-only first-hit rewrite for #24:** properties #53--#55 and the
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
- **Candidate #24 property #71 synchronization, attempt 1:** the patch expected
  a wrapped `Properties #69--#70 are` line that is not present as a separate
  physical line. No candidate file changed. The exact numbered source range is
  now captured; retry only against those confirmed anchors.
- **Native-prefix hybrid draft, endpoint normalization:** the first ticket
  formula assigned a Bessel prefix term at `k=0` even though that prefix is
  empty. It was corrected immediately to `B_0=0`. Preserve the explicit
  endpoint convention in the promoted theorem.
- **Candidate catalog property #72 synchronization:** validation found one
  stale sentence still calling the `U_cap` comparison “the remaining target.”
  The first cleanup patch then missed because its context wrapped
  `enlargement` differently from the source. Exact numbered inspection enabled
  the final permitted correction; the catalog now consistently uses `U_hyb`.

## Next Action

Stop at the normalized-capacity overflow checkpoint. Resume only with a
genuinely independent lower bound for some `e_k` at the extinction-deficit
scale, or with a localized interval-correlation inequality that is stronger
than native-period Bessel.

Treat property #68's positive extinction gap as secondary unless the same
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
| 2026-07-27 | Post-3 endpoint isolation proves `2N_i<=A_i`, hence `|2N_i epsilon_i|<=|H_i-A_i/r_i|`. Young's inequality then separates the #13 endpoint bias from #23's boundary discrepancy. | Promoted property #36, removed `N_i/A_i` from #23's open target, and selected the denominator-free scalar allowance as the next #22 refinement. |
| 2026-07-27 | Weighted Minkowski combines #13 and #23 sharply at the aggregate level: the scalar cost is `(sqrt(E_beta)+sqrt(E_D))^2+E_Delta`. | Promoted property #37, synchronized #22/#23, and isolated `E_D` as a weighted quadratic variation of adjacent accepted-anchor boundary errors. |
| 2026-07-27 | The exact square expansion of #23 is a positive quadratic energy: every interior mass coefficient is positive, so the linear strike telescope cannot upper-bound the squared budget. | Promoted property #38, recorded summation by parts as exhausted without new boundary arithmetic, and selected square-window endpoint structure as the go/no-go test. |
| 2026-07-27 | Prime-square endpoints give the exact residue sum `sum mu(d)([Q]_d-[Q^2]_d)/d`, but an exact `Q=19` chain changes sign after adjoining filter `13`. Universal sign and sign preservation are refuted. | Promoted property #39, cataloged the failed sign laws under `candidates/refuted/`, classified further #23 recurrence algebra as exhausted without new mean-square input, and recommended shifting primary work to #22. |
| 2026-07-27 | Candidate #22 is an ordered harmless-survivor pair correlation on `S_0`. Relative to the old post-filter variance, it has the exact negative correction `2M_i^2/(r_i(r_i-2))`, and its kernel stops before the deleting layer. | Promoted property #40 and reduced the next theorem to the weakest weighted upper bound for the off-diagonal harmless collision count `sum_i w_i R_i`. |
| 2026-07-27 | The extra harmless centering is at most `8/15` per pair, so it cannot offset the logarithmic coefficient in the failed worst-difference bound. | Recorded the combined route as failed and selected the exact post-deletion autocorrelation sum for the next aggregate-pair analysis. |
| 2026-07-27 | Harmless classes are exactly uniform over a complete CRT period, so `U=0`; complete blocks cancel and all #22 energy is remainder-prefix energy. The off-diagonal term is the conditioned version of candidate #20's four-point correlation. | Promoted property #41, removed stale #23 instructions from Next Action, and selected a short-prefix spectral audit for #22. |
| 2026-07-27 | Candidate #22 is the localized nontrivial Fourier mass above the sharp two-empty-class floor. Generic spectral localization still retains the complete-period population, so harmless recentering does not repair its scale. | Promoted property #42, recorded generic localized Fourier composition as failed, and selected a bounded exact falsifier for the stronger pointwise benchmark `U_i<=M_i`. |
| 2026-07-27 | The bounded exact falsifier found no violation of `U_i<=M_i` in 1,035 layers for prime heads `5<=Q<224`; the independent lineage tests pass. Finite agreement is inconclusive and supplies no proof evidence. | Stopped empirical work at the predetermined bound and selected the exact CRT translated-fiber normal form as the next algebraic audit. |
| 2026-07-27 | Every harmless-class count is an interval sum of one common prior-filter CRT word at phase `ceil((Q-a)/r)+sa`; the phases are almost equally spaced, but uncentered Parseval and generic large-sieve sampling remain period-normalized. | Promoted property #43, synchronized candidate #22, recorded the uncentered route as failed, and selected the centered inverse-phase Gram matrix as the next exact lemma. |
| 2026-07-27 | Harmless-class centering has exact single-mode cost `h-|K_m|^2/h`, but the full energy contains cross-frequency Gram entries `K_(m-n)-K_m K_(-n)/h`; it is not a diagonal Fourier sum. | Promoted property #44, synchronized candidate #22, and selected an exact full-operator audit before attempting coefficient estimates. |
| 2026-07-27 | The inverse phases have orthogonal full-Fourier rows, and harmless-class centering leaves sharp operator norm `sqrt(P)`; black-box composition returns exactly to full-shift Parseval scale. | Promoted property #45, synchronized candidate #22, recorded centered operator-norm composition as failed, and selected an audit of arithmetic alignment by exact CRT conductor. |
| 2026-07-27 | Restricting to exact conductor `q` improves the squared phase-block norm to `q mu_q<r+2q`, but triangle recombination introduces an oversized square-root divisor product. | Promoted property #46, synchronized candidate #22, recorded absolute block recombination as failed, and selected the exact centered Ramanujan cross-block geometry as the next test. |
| 2026-07-27 | Exact Ramanujan geometry shows distinct and even coprime conductor blocks are not centered-orthogonal; an exact pair has squared normalized coherence `2793/3203`. | Promoted property #47, cataloged the refuted orthogonality law, classified further unweighted finite-Fourier rearrangement as exhausted, and selected dedicated #23 mean-square work. |
| 2026-07-28 | Dedicated #23 work promoted properties #48--#52: activation shells, CRT lift indices, summatory dilation remainders, complete-period layer orthogonality, and the exact localized Gram matrix. Complete-period Bessel retains the primorial, while local trace composition is only per-layer Cauchy. | Synchronized the umbrella ticket with the dedicated #23 ticket and selected the first-deletion rank-one factorization as the live algebraic micro-goal. |
| 2026-07-28 | Properties #53--#55 factor the localized strike Gram matrix by deletion time, identify its exact negative variance, and reindex that variance completely back to the original strike energy. First-deletion geometry supplies no independent upper bound without new arithmetic mass constraints. | Closed candidate #23's generic algebraic audit and handed the next top-candidate work to #13's endpoint-sampling component. |
| 2026-07-29 | Properties #56--#64 reduce #13+#23 to the direct two-harmful-residue norm, derive its sharp sixfold-capacity ratio, place that ratio strictly between #19 and #14, and show #19's floor already suffices in the explicit late-layer range. | Synchronized the umbrella assessment and selected the weighted early/middle harmful-capacity contribution as the remaining scalar audit. |
| 2026-07-29 | Property #65 proves that one-layer harmful ellipses do not compose into #21's global allowance; even half-local energies overrun it by at least `m^2/2` on the ideal multiplicative scale. | Corrected candidate #21 and both active tickets, recorded the local-to-global route as failed, and stopped at the required strategy checkpoint. |
| 2026-07-29 | Property #25 plus weighted Cauchy appears to give `E_b> T^2/(2W)` whenever `N_m=0`, because the natural dual weight sum is `W_-<W`. | Reopened the checkpoint for one exact classification theorem before spending effort on another scalar upper bound. |
| 2026-07-29 | The weighted lower bound is proved: `E_b> T^2/(2W)` when `N_m=0` and `T>0`, while the strict budget is impossible when `T=0`. Equivalently, `E_b<T^2/(2W)` already forces `N_m>0`. The same energy is exactly the quadratic variation of normalized population. | Added the standalone property; next register it as #66 and correct the candidate roles. |
| 2026-07-29 | The terminal harmful-excess theorem is registered as property #66 in the permanent catalog. | Correct candidate #12's description of its direct weighted aggregate role. |
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
| 2026-07-29 | The algebraic-conditioned-survival ticket now records property #66 as controlling and stops the exhausted #22-first route. | Correct the endpoint-observable ticket's aggregate target and open concerns. |
| 2026-07-29 | The endpoint-observable ticket now classifies `sum_iw_iC_i` below the #21 allowance as a terminal theorem and no longer treats #22 as a subsequent survival requirement. | Update and close the completed one-layer/global audit ticket. |
| 2026-07-29 | The first completed-audit closure patch made no change because one planned What is Learned context was not present in the source. | Recorded the context failure and regenerated the lifecycle patch from exact section text. |
| 2026-07-29 | The completed audit now records property #66's supersession and is in `tickets/done/`. A follow-up scan found four property boundaries with pre-#66 component language. | Correct properties #65, #61, #63, and #64 one at a time. |
| 2026-07-29 | Property #65 now states the sharp later result: a direct weighted capacity envelope below #21's global allowance already forces survival by property #66. | Correct property #61's Boundary. |
| 2026-07-29 | Property #61 now distinguishes its exact one-layer envelope from the terminal cumulative realized-envelope theorem. | Correct property #63's final hierarchy boundary. |
| 2026-07-29 | Property #63 now states that its threshold hierarchy is one-layer and the open direct aggregate harmful theorem is terminal. | Correct property #64's final boundary. |
| 2026-07-29 | Property #64 now states that its late-layer result is one-layer and the remaining direct global harmful estimate is terminal. All property #66 boundary corrections are complete. | Run the final cross-repository audit. |
| 2026-07-29 | Final audit passes. Property #66 also reveals a sharper terminal condition than #21: use only `E_b` and the natural allowance `T^2/(2W_-)`, which is strictly larger because `W_-<W`. | Create candidate #24 and rank it above #21 as the leanest current quadratic survival target. |
| 2026-07-29 | Candidate #24 now records the sharp conservation-only quadratic threshold, its normalized-population variation form, and the proved terminal implication. | Register and rank #24 in the candidate catalog. |
| 2026-07-29 | The catalog now registers #24 as the top quadratic survival target and shows `#21 => #24 => survival`; #22 remains independent. | Link property #66 and candidate #21 directly to #24. |
| 2026-07-29 | Property #66 now names and links candidate #24 as its sharp conservation-only quadratic condition. | Synchronize candidate #21 as the stronger secondary framework. |
| 2026-07-29 | Candidate #21 now defers to #24 as the minimal quadratic survival condition and keeps full energy only where it may add arithmetic leverage. | Correct candidate #12's aggregate target hierarchy. |
| 2026-07-29 | Candidate #12 now distinguishes its stronger full two-class ellipse from candidate #24's minimal one-dimensional harmful-excess energy and larger natural allowance. | Audit the actual-chain constraints on the normalized-population quadratic variation before proposing another theorem. |
| 2026-07-29 | For every fixed prime chain, the Cauchy-equality extinction profile is a rational monotone population profile; scaling `N_0` makes all populations and deletions integral without changing equality. Integrality and monotonicity therefore cannot improve #24's threshold. | Promote the algebraic boundary as a property, then require genuine residue/deletion geometry in the next candidate step. |
| 2026-07-29 | The integral equality construction is now a standalone property with a narrow boundary: it refutes population-only strengthening but does not realize the schedule by CRT residue classes. | Register it as property #67 and synchronize candidate #24. |
| 2026-07-29 | Property #67 is registered, and candidate #24 plus its catalog entry now require genuine CRT deletion geometry rather than population-only constraints. | Derive the exact square-completion remainder around the Cauchy minimizer. |
| 2026-07-29 | Exact square completion gives `E_b=(T-N_m)^2/(2W_-)+sum_i w_i(b_i-b_i^*)^2/(2a_i)` with a unique minimizer. Under extinction, the remainder is precisely the distance from property #67's equality profile. | Register the identity as property #68 and expose the separate upper-bound and stability-gap interfaces in candidate #24. |
| 2026-07-29 | Property #68 is registered. Candidate #24 now states correctly that a positive CRT stability gap only enlarges the certificate threshold and must still be paired with an upper bound for actual `E_b`. | Synchronize the candidate catalog and audit current guidance for stale population-only or gap-alone strategies. |
| 2026-07-29 | Final synchronization passes. Existing first-deletion Gram/reindexing and weighted pair-kernel properties show that transform-only first-hit algebra returns to the original energy; the staged empirical CSV is untouched. | Stop at the checkpoint. Next require a genuinely new CRT mass restriction before proposing an upper-bound candidate for actual `E_b`. |
| 2026-07-29 | The equality deletion mass is `K_i^*=(N_0/S)(1+(2/r_i)P_iR_(i+1))`. A harmful-class cap below this value excludes the Cauchy minimizer and yields a positive stability gap, but it does not exclude extinction or upper-bound `E_b`. | Promote the exact compatibility and gap formula, preserving the separate upper-bound obligation. |
| 2026-07-29 | The cap violation now has an explicit dual-norm gap: extinction forces `E_b>=T^2/(2W_-)+max_i (K_i^*-C_i)_+^2/D_i`. The theorem is algebraic and uses the proved harmful capacities. | Register the result as property #69 and synchronize candidate #24 without claiming an energy upper bound. |
| 2026-07-29 | One validation search used an invalid regex escape; it changed no file. Fixed-string searches and `git diff --check` pass. | Record the tooling failure and do not retry that regex. |
| 2026-07-29 | Property #69 is registered, and candidate #24 now includes the proved `Gamma_cap` relaxed certificate while retaining the separate upper-bound obligation. | Synchronize the candidate catalog, then return to actual-energy control. |
| 2026-07-29 | A second validation command repeated the unsupported LaTeX escape in regex mode; it changed no file. Fixed-string validation passed. | Ban regex-mode LaTeX validation for the remainder of the ticket. |
| 2026-07-29 | Property #61's feasible interval projects sharply onto `b_i^2`: its capacity-only maximum is the larger endpoint square over `ell_i<=K_i<=u_i`. This is sharper for #24 than the full two-coordinate envelope. | Promote the b-only envelope and combine its weighted sum with property #69's enlarged threshold. |
| 2026-07-29 | The sharp b-only envelope is proved: `E_b<=U_cap`, and `U_cap<T^2/(2W_-)+Gamma_cap` is sufficient for survival. The aggregate inequality remains open and population-profile dependent. | Register the result as property #70, synchronize #24, and assess whether the explicit target escapes candidate #19's abundance wall. |
| 2026-07-29 | Property #70 is registered, and candidate #24 now has a proved sharp capacity-only upper envelope paired with property #69's enlarged extinction threshold. | Update the catalog and classify whether the remaining aggregate comparison is weaker than candidate #19's population floor. |
| 2026-07-29 | The b-only capacity envelope has exactly property #62's threshold `N_i/B_i>rho_*(r_i)>2`, because the decisive filled-harmful branch has zero imbalance. In one layer, `Gamma_cap` is zero below ordinary capacity survival and redundant above it. | Classify separate-layer capacity optimization as exhausted; preserve #69--#70 only as a possible cross-layer interface. |
| 2026-07-29 | Property #70, candidate #24, and both catalogs now state that the capacity-only route has no new one-layer regime. Its only remaining value is a joint cross-layer restriction lowering the sum of separately sharp endpoint maxima. | Stop at the cross-layer checkpoint; reject further independent one-layer envelopes. |
| 2026-07-29 | Two fixed-string validations missed correct prose because of case and physical-line wrapping; exact-range reads passed. | Use exact-range reads for wrapped prose and keep fixed strings for formulas. |
| 2026-07-29 | Candidate #19 now records how its capacities feed properties #69--#70 while preserving its unchanged local-abundance boundary. All directly affected permanent artifacts are synchronized. | Run the final consistency audit and retain only the joint cross-layer CRT problem as the next useful #24 work. |
| 2026-07-29 | The final fixed-string catalog search mistakenly used a literal regex anchor; exact-range validation confirmed entries #69--#70 and `git diff --check` passed. | Record the validation misuse and stop without further search variants. |
| 2026-07-29 | The paired harmful-excess observables are exactly mean-zero and mutually orthogonal over the final CRT period, with norm `Rd_i(2/r_i)(1-2/r_i)`. Black-box Bessel yields `E_b<=LRd_m/(r_0-2)`, retaining the primorial-scale class count. | Promote the exact boundary and reject complete-period Bessel as the missing #24 estimate. |
| 2026-07-29 | The paired orthogonality theorem is now a standalone property. It proves the exact cross-layer geometry while classifying its direct Bessel use as quantitatively insufficient for a short safe window. | Register it as property #71 and narrow candidate #24's next theorem to localized interval correlations or actual-coefficient cancellation. |
| 2026-07-29 | The first candidate #24 synchronization patch made no change because its context assumed a prose wrap not present in the source. | Captured the exact numbered range; make one corrected patch using confirmed anchors. |
| 2026-07-29 | Property #71 is registered, and candidate #24 now rules out complete-period Bessel while requiring localized interval correlations or coefficient-sensitive cancellation. | Synchronize the candidate catalog and audit the resulting proof frontier. |
| 2026-07-29 | The catalog is synchronized. Using each prefix's native period gives a concrete hybrid: cancel complete `M_k` blocks and apply Bessel to layers `<k`, then use property #70's capacity envelope on layers `>=k`. The `k=0` cut recovers the all-capacity bound, so optimization cannot be worse. | Prove the exact hybrid formula and test its algebraic strength before proposing any new correlation hypothesis. |
| 2026-07-29 | The initial hybrid draft incorrectly charged the empty `k=0` prefix; the endpoint is now `B_0=0`. Combining prefix Bessel with each `b_i^2` capacity is a linear program whose ratios `M_kd_m/(r_i-2)` decrease with `i`, so greedy saturation gives the sharp combined envelope. | Promote the corrected sharp hybrid as a property, then compare it algebraically with the all-capacity bound. |
| 2026-07-29 | The sharp native-period/capacity hybrid is proved. It always improves or matches `U_cap`, improves strictly exactly when the normalized prefix capacity box exceeds the interval remainder `s_k`, and composes with `Gamma_cap` to give a terminal survival criterion. | Register as property #72 and synchronize candidate #24 and the catalogs. |
| 2026-07-29 | Property #72 is registered in the permanent property catalog. | Add its hybrid certificate and exact gain criterion to candidate #24. |
| 2026-07-29 | Candidate #24 now uses `U_hyb` as its strongest proved capacity/orthogonality envelope and preserves the universal threshold comparison as open. | Synchronize the candidate catalog and reassess the remaining algebraic obligation. |
| 2026-07-29 | Candidate #24 and both catalogs are synchronized after removing one stale `U_cap` target; the first cleanup patch missed a wrapped context, and the exact-range retry succeeded. The greedy hybrid rejects exactly the normalized overflow `e_k`, giving a prospective gain at least `M_kd_m e_k/(r_(k-1)-2)`. | Prove the scalar overflow-gain lemma and compose it with the extinction threshold. |
| 2026-07-29 | The scalar overflow theorem is proved: the exact hybrid gain lies between the smallest and largest prefix coefficient times `e_k`, yielding a simplified terminal certificate. | Register as property #73 and synchronize candidate #24 and the catalogs. |
| 2026-07-29 | Property #73 is registered in the permanent property catalog. | Add the overflow certificate and its open lower-bound obligation to candidate #24. |
| 2026-07-29 | Candidate #24 now states property #73's scalar overflow certificate and identifies a lower bound for `e_k` at the extinction-deficit scale as the next independent input. | Synchronize the candidate catalog and run the final consistency audit. |
| 2026-07-29 | Final audit passes: properties #71--#73, candidate #24, and both catalogs are synchronized; no stale `U_cap` target remains; Markdown is clean; the staged giant CSV is untouched. | Stop at the overflow checkpoint until an independent lower bound for `e_k` or stronger localized correlation input is available. |
| 2026-07-29 | Independent reviewer (separate agent) audited the full ~40 new properties per `TICKET_DISCIPLINE.md` §6. Stratified sample across 3 tiers (negative/insufficiency, load-bearing positive identities, heavy-machinery). | All checked notes are mathematically SOUND and carefully scoped. Net: the new work sharpens the wall (precise inventory of which standard tools fail, the one viable shape left) but does not escape it. Recorded as "Independent property-catalog audit" subsection in What is Learned. No corrections needed to the team's properties. |
