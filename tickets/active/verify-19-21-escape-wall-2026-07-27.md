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
component, or terminal consumer. Candidate #22 is the active path. Its class
counts are now exact translated interval sums of one prior-filter CRT word.

The finite-Fourier audit of candidate #22 is complete. Its remaining route is
a genuinely coefficient-weighted bilinear estimate using the CRT
coefficients, interval multipliers, or chain weights. Generic conductor
orthogonality is exactly false.

The immediate micro-goal is to hand active work to candidate #23 in a
dedicated ticket. Preserve #22 as an open analytic interface; do not retry
unweighted conductor rearrangements.

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
- Candidate #23 is only a precise interface so far. Neither a pointwise nor a
  weighted strike-density bound has been proved, and the exact immediate
  next-window strike formula does not automatically apply throughout a
  conditioned chain.
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

## Next Action

Create a dedicated active ticket for candidate #23. Seed it from this ticket's
proved properties #35--#39 and failed paths:

1. unsigned inclusion--exclusion is exponential;
2. the linear boundary telescope does not control weighted squares;
3. summation by parts has positive interior coefficients;
4. universal sign and sign preservation are refuted.

The new ticket's first mathematical action is to write the weakest
coefficient-weighted mean-square theorem for the signed Möbius boundary
sequence that fits `mathcal E_D`, and strength-test whether it is genuinely
weaker than a generic short-interval parity estimate. Do not collect more
data.

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
