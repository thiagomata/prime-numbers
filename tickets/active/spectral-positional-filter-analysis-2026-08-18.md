# Spectral / Positional Cross-Layer Filter Analysis

**Created:** 2026-08-18
**Updated:** 2026-08-18
**Status:** Plan phase
**Depends on:** none (hard). Uses existing datasets and the draft companion article.

## START HERE

Micro-goal 1 is COMPLETE and did not need new math: the intended pairwise
orthogonality lemma already exists in a stronger form as the Cross-Layer
CRT Orthogonality property (centered observables, exact norms, Bessel
bound), together with its proved limitation (the `LR` primorial
normalization obstruction). Read that property before any spectral work.

Micro-goal 2 (next): E1 — single-filter positional strike spectra from
`data/sieve-sequence/first_gaps_per_seq.csv`. The null and coordinate
contract are now filed: position-blind permutation band in index
coordinates (Position-Blind Index Spectrum property). Remaining design
step before code: fix the decoherence-band statistic and the windowing.

Do NOT start with a full-period cross-filter FFT expecting signal — it is
provably flat (see What is Learned #1). Do NOT re-measure per-layer aggregate
counts — they are already exactly predicted by proved CRT identities. Do
NOT chase pairwise cohort covariances — they are exactly determined by
destruction disjointness (What is Learned #7).

## Related Tickets

- `verify-real-two-gap-copy-survival-2026-08-14.md` — in progress; real-sieve
  copy law (two forbidden lift indices, `head - 2` survivors). Supplies the
  exact arithmetic backbone any positional strike analysis must agree with.
- `draft-mixed-adversarial-random-companion-2026-08-11.md` — tracks the
  companion article `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md`
  whose transfer blocker (§8–§10: availability, mixing, deterministic
  discrepancy bound) motivates this ticket.
- `lineage-experiment-2026-07-23.md` — generated the Reading A lineage data;
  its alignment lessons apply to any cross-layer coordinate comparison.
- `frontier-comparison-chart-2026-08-12.md` — per-transition destruction
  measurements (`window-measurements*.csv`); its positional summary columns
  (`max_cons_destroyed_run`, `residue_max_dev`, `endpoint_bias`) are
  single-number precursors of the full spectral analysis proposed here.
- `fixed-lineage-cumulative-hazard-chart-2026-08-12.md` — fixed-cohort hazard
  aggregates; E3 below upgrades these aggregates to per-individual fate.
- `companions-folder-properties-of-models-2026-08-12.md` — companion-model
  property catalog; the null models for spectral comparisons come from there.

## Goal

Locate the real sieve in the companion phase diagram *spectrally and
positionally*: measure whether the incoming filter's destruction pattern at
one layer predicts the pattern at the next layer, and at which spatial
frequency band and window scale positional structure decoheres. All analyses
are defined on positional patterns (per-index strike indicators), never on
per-layer aggregate sums, because the aggregates are already exactly
predicted by proved identities (full-cycle `f_r = 2/r`, accepted-strike count
`A(p,q)`) and carry no open information.

Deliverables:
1. Exact pairwise orthogonality lemma (math-only, no data).
2. Measured positional strike spectra per filter and cross-layer coherence,
   compared against an explicit thinned-wheel null (not Poisson).
3. A stated empirical answer: at which scales the real filter is
   random-like, and where (if anywhere) coherent CRT-coupled placement is
   visible — the empirical shadow of the §10 discrepancy premise.

## Strategy

Three nested scales, ordered by cost:

1. **Provable baseline first.** Establish exactly what any spectral
   experiment is guaranteed to see at the full-period scale: nothing beyond
   the random benchmark, because distinct-filter combs are CRT-orthogonal at
   every lag. This baseline is ALREADY PROVED and filed (Cross-Layer CRT
   Orthogonality, with its `LR` localization obstruction); the strategy step
   is to READ it, not reprove it. It localizes all open content to the
   sub-CRT scale (windows ≪ products of moduli) — where every existing
   dataset already lives.
2. **Positional spectra before cross-layer coherence (E1 → E2).** A single
   filter's strike pattern in the sequence's own coordinates is the simplest
   object with a nontrivial predicted spectrum (quasi-periodic lines from
   Beatty/wheel structure vs flat for the random companion). Measure it
   before attempting two-layer comparisons, because E2's null model depends
   on E1's answer.
3. **Lineage persistence last (E3).** Per-individual cohort fate is the
   direct operationalization of the "delayed adversary" mechanism (article
   §6.1) but requires re-running cohort tracking with per-individual output.

Chosen over (alternatives): circle-method-style analytic number theory
(major/minor arc machinery) — too heavy, and this ticket's purpose is to
measure, not prove; pure Monte Carlo companion simulation without real data
— already covered by the companion models; full-period DFT — provably flat
(see Failed Paths pre-emption #1).

## Current State

- CORRECTED 2026-08-18: complete-period spectral machinery DOES exist in
  `properties/sieve-sequence/` (the initial claim "no spectral analysis
  anywhere" came from a grep that missed that directory — see Failed Paths
  #3). Existing: Cross-Layer CRT Orthogonality (the intended P1, stronger,
  with the `LR` localization obstruction), Fourier Correlation Prefix Bound
  (exact conductor weights, prime inclusion probability exactly `2/p`),
  Localized Fourier Boundary, Conductor-Decay Destruction (localization
  concentrates fraction `1-1/p` of energy nontrivial at `p`), and the
  Ramanujan/phase Gram family.
- Genuinely new and now filed (2026-08-18):
  - `companions/properties/position-blind-index-spectrum.md` — proved null
    model: uniform size-`K` subset has expected spectrum exactly
    `K(N-K)/(N-1)` at every nonzero frequency; deterministic contrast
    (subgroup placement concentrates all power). Registry row added.
  - `candidates/sub-crt-strike-decoherence.md` — candidate #26 (two-body +
    frequency-resolved analogue of #10 on the mixing side), with the two
    reclassification facts (pairwise cohort covariances determined by
    disjointness; statement (A) equivalent to the article §10 premise in
    pair form). Registered in `candidates/README.md` (item 26, taxonomy
    row) and `candidates/INVESTIGATION_STATUS.md` (row 26).
  - `properties/sieve-sequence/layer-strike-innovation-orthogonality.md`
    — proved global innovation theorem (conditional mean zero, span
    orthogonality, adaptive Pythagoras), exact-rational validated on the
    `R=2310` chain including a load-bearing measurability negative
    control. Registry row added.
  - `candidates/window-innovation-orthogonality.md` — candidate #27
    (ALGEBRA-FIRST): the local window form; near-typical restricted Gram
    matrix ⇒ local approximate Pythagoras ⇒ the missing signed
    mean-square cancellation in the innovation basis. Registered in
    `candidates/README.md` (item 27, ALGEBRA-FIRST taxonomy) and
    `INVESTIGATION_STATUS.md` (row 27).
- Existing near-neighbors (positional summaries, not spectra):
  - `window-measurements.csv` / `-sparse.csv`: per-transition (p,q) with
    `max_cons_destroyed_run`, `max_cluster_in_width_p`, `residue_max_dev`,
    `endpoint_bias`.
  - View B in the companion article (shared-safe-2 alignment): a lag-0
    cross-correlation measurement already done — 118 zero-shifts and 81
    one-shifts across 199 transitions ⇒ near-rigid persistence of the safe
    prefix. This is the strongest existing evidence that consecutive layers
    ARE highly correlated in compressed coordinates.
  - `fixed-lineage-hazard-Q{17,101,251,503}.csv`: per-layer cohort
    aggregates (destroyed, `w_real`, hazard) — no per-individual fate.
- Data available for E1/E2 without new generation:
  `first_gaps_per_seq.csv` (first 100,000 gaps × 200 stages) gives survivor
  positions per stage by cumulative sum; strikes of the incoming filter p on
  stage-p survivors are exactly the multiples of p in that prefix
  (edge case: exclude the head value p itself).
- Next: E1 design (decoherence-band statistic, windowing), then code under
  `python/src/sieve_sequence/`.

## Expected State

- COMPLETED (no new file needed): the pairwise orthogonality baseline is
  the existing Cross-Layer CRT Orthogonality property; candidate #26 and
  the Position-Blind Index Spectrum property cite it as an established
  input.
- E1: a Python module under `python/src/sieve_sequence/` (e.g.
  `strike_spectrum.py`) + CSV output under `data/` + one chart under
  `charts/`, reporting per-stage periodograms of the strike indicator in
  survivor-index coordinates with a thinned-wheel null and permutation-based
  significance bands.
- E2: cross-layer coherence matrix (consecutive stages) in View-B-aligned
  compressed coordinates.
- E3 (optional, after E1/E2): per-individual fixed-cohort tracking output,
  delayed-adversary test statistic.
- All results reported with explicit caveats: finite-window evidence locates
  the real sieve in the phase diagram; it does not prove availability,
  mixing, or the discrepancy bound.

## What is Learned

1. **Pairwise CRT orthogonality (exact, no data needed).** For distinct
   primes r ≠ r', the strike combs `{n ≡ 0 mod r}` and `{n ≡ 0 mod r'}`
   have cross-correlation exactly (1/r)(1/r') at EVERY lag h over the common
   period rr' (each lag has exactly one CRT solution) — zero excess
   correlation. For the 2-gap strike events
   `E_r = {a ≡ 0 or −2 mod r}` (r > 2): `|E_r ∩ E_{r'}| = 4 = (2/r)(2/r')·rr'`
   exactly. The ONLY pairwise deviation is diagonal (same filter, distinct
   residues vs independent draws) — this is precisely why the
   Hardy–Littlewood twin-prime singular series factor is
   `Π_{p>2}(1 − 1/(p−1)²)`: corrections come from the diagonal alone.
   Consequence: the article's benchmark `Π(1 − 2/r)` already contains ALL
   pairwise inter-filter correlation content, exactly. Open content lives
   only in (i) higher-order joint structure and (ii) short-window
   discrepancy below the CRT scale.
2. **All available data lives far below the CRT scale.** The cycle period at
   head Q is the primorial `Π_{r<Q} r`, astronomically larger than the
   square window `[Q, Q²)` and than the 100k-gap prefixes. Every measurable
   object is in the regime where orthogonality has not averaged out — the
   only regime where positional signal can exist.
3. **Aggregate sums are exhausted information; positions are not.** Per-layer
   counts (destroyed, `f_r`, `A(p,q)`) are already exactly predicted. The
   user's framing is correct and is this ticket's design principle: analyze
   WHERE strikes land (per-index indicators), not HOW MANY.
4. **Predicted single-filter positional spectrum is NOT flat.** In
   survivor-index coordinates the strike indicator `d_p(i) = 1[p | s_i]` is
   a deterministic quasi-periodic sequence (circle-rotation / Beatty coding
   modulated by the wheel structure). Classical theory (Sturmian/Beatty
   coding, three-distance theorem) predicts a pure-point spectrum: sharp
   lines at the rotation frequency and its harmonics plus wheel harmonics
   (mod 6, 30, 210, …). The random companion predicts flat. Therefore the
   correct null model is a THINNED WHEEL (wheel positions with random
   thinning at rate 2/p), not Poisson. The measurable question is the
   decoherence scale: at which frequency band and window length do the
   deterministic lines smear into the null.
5. **View B is already a cross-layer correlation result.** The near-vertical
   green lines (118/199 zero drift) show consecutive stages' safe prefixes
   are nearly rigid copies in compressed coordinates. This is trivially
   explained below h² (nothing changed there except head advance) — the
   informative region is near and beyond the safe boundary, which E2 must
   target explicitly.
6. **Per-integer fate is exclusive across layers.** A fixed value n is
   removed by exactly one filter (its smallest prime factor ≥ the stage
   head). Cross-layer correlation therefore cannot be about the same integer
   being struck twice; it is about the joint geometry of two different
   combs' strike positions in the shared survivor coordinates.
7. **Pairwise cohort covariances are exactly determined (proved while
   filing candidate #26).** On one fixed window cohort, destruction sets of
   distinct layers are disjoint (Learning #6), so for centered residuals
   `e_r = d_r - K_r/N`: `sum_i e_r(i)e_r'(i) = -K_rK_r'/N` — minus the
   independent-product value. Pairwise cohort information is EXHAUSTED by
   this identity. Open positional content is only: single-layer placement
   SHAPE (one-body, frequency-resolved — E1), joints of 3+ layers, and
   cross-head agreement (disjoint value pairs, not subject to
   disjointness).
8. **Candidate #26 statement (A) is honestly equivalent to the article §10
   discrepancy premise**, because `sum_{P,Q} I_P I_Q = (sum_Q I_Q)^2` with
   `I_Q^2 = I_Q`. Its value is the pair-resolved decomposition it licenses,
   mirroring how candidate #10's review exposed its own one-sided form as a
   restatement of survival. Recorded in the candidate file to prevent
   circularity being mistaken for progress.
9. **Existing spectral properties reclassify this ticket's scope.** The
   complete-period frequency content of the 2-gap set is fully developed
   (conductor weights, fourth moments, Gram matrices, phase-operator
   bounds). What none of it covers: the survivor-INDEX coordinate frame
   (the sequence's own enumeration axis), where E1's quasi-periodicity
   question lives. That frame is this ticket's genuinely new territory.
10. **The innovation formulation (user-directed pivot to algebra-first,
    2026-08-18).** Each layer's centered strike observable has conditional
   expectation EXACTLY ZERO given the entire past
   (`E[g_i | a mod P_i] = 0` by CRT uniformity of the `r_i`-coordinate) —
   it is the innovation of the layer filtration. Hence: orthogonality to
   EVERY past-measurable function (span, not pairwise), annihilation of
   all distinct-innovation products, and an adaptive Pythagoras with
   past-measurable weights. Validated exactly on the `R=2310` chain (all
   246 conditional classes zero; span tests zero; adaptive Pythagoras
   exact; a weight peeking at `a mod r_i` BREAKS it — measurability is
   load-bearing). Filed as the Layer Innovation Orthogonality property.
   The local form (window typicality of the class `g_i·h`) is candidate
   #27 — this is the "signed mean-square / cross-layer cancellation" the
   investigation matrix names as the remaining frontier, stated in the
   basis where the global answer is exact.
11. **Past-span saturation (answered the user's shaping question,
    2026-08-18).** The full constraint family from all previous primes —
   orthogonality to the entire past span — is EXACTLY EQUIVALENT to the
   per-fiber quota "one lift lost per old survivor". The admissible
   placement space is `r^(phi(P))` points (real sieve = one, chosen by
   divisibility); every fiber-admissible placement satisfies every
   innovation identity (validated: an adversarial `(c^2+3) mod r` rule
   passes the complete identity battery on the 2310 chain; tiny chain
   enumerates exactly `5^2=25` admissible placements). CRT product
   structure makes placement permanently invisible to the past coordinate
   — more primes never help. Filed as the Past-Span Saturation property;
   sharpens #26/#27 Limitations with NECESSITY of the local form, and
   closes the "accumulate global constraints to force local behavior"
   strategy class.
12. **2-gap placement saturation (menu item #1, user-approved algebra-only
    2026-08-18).** The balanced two-class companion law (article §2) is
   EXACTLY a compatible-coloring condition on the 2-gap fiber graph
   (proper coloring on non-wrap step-2 edges; one forbidden difference on
   the wrap pair `(P−1,1)`); the real placement is the linear coloring
   `φ(c)=−cP⁻¹` with rigid harmful-class difference `Δ=2P⁻¹`; counts and
   marginal statistics are coloring-blind (next-period total `(r−2)G` for
   every compatible coloring; no-creation post-3 because among `m,m+1,m+2`
   the middle is `0 mod 3`); ≥`(r−2)^φ(P)` compatible placements exist.
   The FIRST placement-sensitive global 2-gap statistic is the
   separation-resolved pair count `r−4+|E₁∩E₂|`, rigid at `h≡0,±2 mod r`
   under the real rule — this is the precise, characterized home of the
   transfer obligation's "shared-value effects" bullet. Toy-chain
   derivation checks confirm counts-blind/positions-sensitive (3 vs 3
   with different sets; 4 = (r−1)G for a non-compatible coloring). Key
   correction during derivation: the 2-gap fiber graph is NOT a value-level
   matching — many 2-gaps share fiber pairs, and the constraint is a
   forbidden DIFFERENCE per fiber pair, not pair-free choice.
13. **Dream-sequence invariant (candidate #28, user-directed inversion
    2026-08-18).** Define a property set P that reproduces itself under
   the transition and forces safe-window 2-gaps; one seed + closure ⇒
   infinitely many twin primes (perpetuity theorem, proved as implication;
   nonemptiness explicitly not claimed). NEW PROVED FACT: the global 2-gap
   density relative to the Mertens benchmark is an EXACTLY CONSERVED
   quantity of the dynamics (validated stage-by-stage, ratio 1/6 on the
   post-3 chain) — the global band component is hereditary for free, for
   every placement. Open core = Lemma A: local spacing self-preservation
   at the Mertens scale; naive union-bound degradation diverges
   (Σ S/r over primes), and the only friendly arithmetic is the rigid kill
   geometry (elevated survival at h ≡ 0, ±2 mod r from the 2-gap
   saturation property). Mirror of the proved nightmare invariant
   (absence stability): absence preserves itself for free, presence needs
   surplus — that asymmetry IS the difficulty.
14. **Recurrence generalization (user-directed, 2026-08-18).** Direct
   heredity is `J={1}`; recurrence `P ⟹ ∃j≥1: P(seq_j)` gives perpetuity
   verbatim and weakens Lemma A to Lemma A′: INTEGRATED degradation vs.
   threshold growth (averaged — mean-square shaped) instead of per-layer
   worst case (divergent product). Structural constraint surfaced:
   2-gap-start spacing is monotone non-decreasing across layers (2-gaps
   only die, never born) — recovery can only run through scale-threshold
   growth (`log²Q` catching up), never through spacing shrinking. Full
   design rule for any strengthening invariant: scale-relative components
   only; decay-compatible; recurrence allowed.
15. **2-focused alternation law (user observation, 2026-08-18).** The
   user noted the 2-focused compression keeps the 2-gap share "around
   50%"; sharpened and proved: post-3 no two 2-gaps are adjacent (mod-3:
   among v, v+2, v+4 one is ≡ 0), so compressed cells strictly alternate
   and the share is EXACTLY 1/2 at every post-3 stage (validated: 3/6,
   15/30, 135/270). The Mertens decay relocates entirely into run values
   (average run = 1/density − 2). Filed as a property; registered as
   #28's Component 0 (perpetual presence, free); Lemma A′ restated as
   pure run-value control — the compressed frame is the dream's natural
   coordinate system, and the heatmap/View-B infrastructure already uses
   it.
16. **Lemma A′ calibration (deep dive, 2026-08-18).** (i) Post-2,
   consecutivity is automatic (v+1 always even/dead), so the 2-gap set IS
   the dimension-2 sifted set — runs = gaps of that set; its complete-
   period pair statistics already exact (Pair Local Factor property:
   local factor by `d ≡ 0, ±2 mod p`). (ii) Equivalence class: weak run
   law (infinitely many windows occupied) ⟺ infinitely many twin primes
   EXACTLY; strong form strictly stronger; the interface needs only the
   weak form — so proving Lemma A′(weak) IS proving twin primes; no
   cheaper lemma exists on this path. (iii) Dimension map: the
   dimension-1 sibling is solved classically (Jacobsthal bounds
   `j(n) ≪ ω(n)²log²ω(n)`; primorial ⇒ ≲ Q² — window scale) — Lemma A′
   is exactly one dimension above a solved problem: an infinitely-often,
   window-restricted, dimension-2 Jacobsthal bound.

## Approaches Considered

- **P1 — pairwise orthogonality lemma.** RESOLVED BY SEARCH: already proved
  as the Cross-Layer CRT Orthogonality property (centered observables,
  exact norms, Bessel bound, `LR` obstruction). No new file was written;
  candidate #26 records it as Fact 1.
- **E1 — single-filter positional strike spectra.** From
  `first_gaps_per_seq.csv`: stage-p survivors via cumulative sum; strike
  indicator on survivor indices; periodogram + thinned-wheel null +
  permutation bands. Risks: prefix windows are 100k gaps ≪ period —
  windowed estimation only, with leakage and boundary effects; the head
  value and the first-gap edge cases must be handled explicitly; strike
  density ≈ 1/p means few strike events per prefix at large p (power).
- **E2 — cross-layer coherence in aligned coordinates.** Consecutive-stage
  spectra compared under View-B alignment; report coherence per frequency
  band and per compressed-position region (safe prefix vs boundary).
  Risks: coordinate alignment beyond the safe prefix is exactly the open
  lineage problem; restrict claims to the aligned region.
- **E3 — lineage persistence (delayed-adversary test).** Re-run fixed-cohort
  tracking with per-individual output; statistic: does destruction at layer
  r′ correlate with the lineage's layer-r fate/position beyond the
  hypergeometric null. Risk: requires new data generation; interpretation
  must respect Learning #6 (exclusivity of per-integer fate).
- **E4 — layer-axis / 2D field analysis.** (layer r, survivor-index i)
  point field of strikes; 2D spectrum or per-layer position-histogram
  tracking. Risk: only ~187 measured transitions and ~95 layers for Q=503 —
  very low spectral resolution along the layer axis; treat as exploratory.
- **Rejected: full-period cross-filter FFT as an experiment.** Provably
  flat (Learning #1) — pre-empted, see Failed Paths.

## Failed Paths

1. **Full-period / raw-coordinate cross-filter FFT expecting signal.**
   Pre-empted before running (2026-08-18): provably zero excess correlation
   at every lag by CRT (Learning #1). Verdict would change only if the
   analysis target changed from distinct-filter pairs to same-filter or
   sub-period windows — i.e., the pre-emption is a redirection to E1/E2,
   not a closure of spectral work.
2. **Spectral analysis of per-layer aggregate counts (destroyed, f_r, D(Q)
   time series) as the primary object.** Pre-empted: aggregates are exactly
   predictable from proved identities (user framing, 2026-08-18: "not based
   on sum where is stable and 100% predictable but based on position").
   Layer-axis series may still be reported as context (E4) but never as the
   headline. Verdict would change if a proved identity failed to predict an
   aggregate — that would itself be a finding.
3. **"No spectral analysis exists in the repo" — a failed search, not a
   failed math attempt.** The initial repo-wide grep covered only
   `python/src`, `articles/draft`, and `LEARNINGS.md`; it missed
   `properties/sieve-sequence/`, which contains the full complete-period
   Fourier program (Cross-Layer CRT Orthogonality, Fourier Correlation
   Prefix Bound, Conductor-Decay Destruction, Ramanujan/phase family).
   Consequence: the planned P1 lemma was already proved in stronger form,
   and the ticket was re-scoped to the survivor-index frame and local
   decoherence. Verdict flip condition: none — this is a recorded process
   failure. Any future "X does not exist in the repo" claim must grep
   `properties/`, `candidates/`, `companions/`, and `articles/` before
   being asserted.
4. **"Accumulate enough global constraints to force local placement" —
   provably futile strategy class.** The Past-Span Saturation property
   proves the complete past-span constraint family is equivalent to the
   per-fiber quota; placement (`r^(phi(P))` choices) lives in the other
   CRT coordinate and is invisible to every period-summed statistic of
   the innovation class — at any depth of previous primes. Pre-empted
   before investing (2026-08-18). Verdict flip condition: an observable
   class NOT expressible as period sums of innovation/past-measurable
   functions — i.e., exactly the local/window observables of #26/#27.
   Within global algebra there is no flip; any re-attack must go local.

## Open Concerns

- **Null-model correctness is the load-bearing step.** The random companion
  in survivor-index coordinates is a thinned wheel, not Poisson; a wrong
  null makes "flat vs lined" comparisons meaningless. E1 must fix the null
  definition and validate it on a simulated companion before reading real
  data.
- **Coordinate choice must be fixed before cross-layer claims.** Raw
  position (n), survivor index at layer r (i), and compressed 2-gap index
  are three different axes; coherence claims are coordinate-dependent.
  Default: survivor-index per stage for E1; View-B-aligned compressed index
  for E2.
- **Power at large p.** Strike density ≈ 2/p over 100k-gap prefixes gives
  O(100000·2/p) events — adequate for small p, thin for large p; may need to
  pool stages or restrict to p ≤ some cutoff; state the cutoff.
- **What this cannot establish.** No finite experiment proves persistent
  availability, cross-layer mixing, or the §10 deterministic discrepancy
  bound. Outputs locate the real sieve in the phase diagram (article §11
  future-work directions 1 and 3) — they do not transfer almost-sure
  conclusions.
- **Article integration is a user decision.** The existing complete-period
  spectral properties are not yet reflected in the companion article's §8;
  if E1/E2 produce settled results, a compact subsection linking Cross-Layer
  CRT Orthogonality, candidate #26, and one figure could be added. Per
  `property-completeness` and `framing-integrity` rules this changes a draft
  article and needs explicit approval before editing.
- **Edge cases in E1 data extraction**: exclude the head value p (divisible
  by p by definition but never removed); confirm whether
  `first_gaps_per_seq.csv` stage rows start at the head gap or the first
  post-head gap before computing survivor positions.

## Next Action

ALGEBRA-FIRST (user direction, 2026-08-18: "even if it does it will not
proof anything... the algebra is weak"). Order:

1. **N3 — exact restricted Gram computation** (no sampling, exact
   arithmetic): for the measured heads/windows, compute
   `G^(W)_ij = sum_{n in W} g_i(n)g_j(n)`, the diagonals' ratio to the
   typical profile `L·(phi(P_i)/P_i)(r_i-1)/r_i^2`, and the
   off-diagonals' ratio to the conductor-factor prediction. Design
   decision needed first: which datasets give `g_i` on window values
   (survivor reconstruction from `first_gaps_per_seq.csv` vs. lineage
   cohort frames) and the exact class `H_past` to include.
2. **N1 — window span-regression falsifier** against the position-blind
   permutation band (null per the Position-Blind Index Spectrum property).
3. E1 spectra DEMOTED to context (one basis of the N1 regression);
   E2–E4 unchanged, later.

Prerequisite read before N3 code: the Layer Innovation Orthogonality
property and the Cross-Layer CRT Orthogonality property (exact norms
formula feeding the typical profile).

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-18 | Pairwise CRT orthogonality: distinct-filter strike combs are exactly uncorrelated at every lag; `|E_r ∩ E_{r'}| = 4` equals the independence prediction; only diagonal terms deviate (singular-series structure). The benchmark `Π(1−2/r)` already contains all pairwise content. | Pre-empted raw full-period FFT as an experiment; redirected to sub-CRT-scale positional analysis (P1, E1–E4). |
| 2026-08-18 | All repo data (100k-gap prefixes, windows [Q,Q²)) lives far below the CRT scale — the only regime where positional signal can exist. | Made "positional patterns, not aggregate sums" the ticket design principle. |
| 2026-08-18 | Single-filter strike indicator in survivor-index coordinates is quasi-periodic (Beatty/wheel) ⇒ predicted pure-point spectrum vs flat random companion; null must be thinned wheel, not Poisson. | Recorded as E1's central question: decoherence band and scale. |
| 2026-08-18 | View B alignment (118/199 zero drift) is already a lag-0 cross-correlation measurement showing near-rigid prefix persistence. | E2 scoped to target the safe-boundary region, where persistence is NOT trivially explained. |
| 2026-08-18 | Initial "no spectral work exists" grep missed `properties/sieve-sequence/`; the complete-period Fourier program already exists, including the intended P1 in stronger form (Cross-Layer CRT Orthogonality + `LR` obstruction) and the localization warning (Conductor-Decay Destruction: fraction `1-1/p`). | Re-scoped ticket; P1 dropped; recorded Failed Path #3 with the corrected grep rule. |
| 2026-08-18 | Fixed-cohort pairwise covariances are exactly `-K_rK_r'/N` by destruction disjointness — pairwise cohort information exhausted; candidate #26's (A) is equivalent to the article §10 premise in pair form (diagonal included). | Filed candidate #26 with honest equivalence note; redirected open content to shape/3+-layer/cross-head objects. |
| 2026-08-18 | Position-blind null proved and filed: uniform size-`K` subset ⇒ expected spectrum exactly `K(N-K)/(N-1)` at every nonzero frequency; subgroup placement concentrates all power (deterministic contrast). | Filed `companions/properties/position-blind-index-spectrum.md`; registry row added; E1's null fixed. |
| 2026-08-18 | User redirect: empirical "check if it seems to have something" proves nothing; the algebra is weak — pivot to algebra-first. Session insight: predictability is representation-relative (sin/cos are orthogonal in time, constants in frequency); the right probe is the frequency/span prism. | Rewired plan to N3 (exact restricted Gram) + N1 (span regression); spectra demoted to context. |
| 2026-08-18 | Innovation formulation proved and validated: `E[g_i \| a mod P_i]=0` exactly ⇒ span orthogonality, product annihilation, adaptive Pythagoras; measurability of weights is load-bearing (negative control breaks it). No prior martingale/innovation formulation existed in the repo (searched). | Filed Layer Innovation Orthogonality property; filed candidate #27 (window form) with proved cross-term reduction to local approximate Pythagoras; registries updated. |
| 2026-08-18 | Saturation (user's shaping question): full past-span constraints ≡ per-fiber quota; `r^(phi(P))` admissible placements, real sieve one point; adversarial one-per-fiber rule passes the ENTIRE identity battery (validated 2310 chain + tiny-chain enumeration); CRT product makes placement permanently past-invisible. | Filed Past-Span Saturation property; sharpened #26/#27 Limitations with necessity; recorded Failed Paths #4 closing the global-accumulation strategy class. |
| 2026-08-18 | Promotion pass (user-directed): durable lessons moved out of the ticket — LEARNINGS §17.4 (global accumulation provably cannot force placement) and §18.6 (search all doc roots before "does not exist" claims); transfer candidate's "What Does Not Resolve It" upgraded from assertion to theorem (saturation); innovation property now cites the Stainless-verified kernel `BezoutUtils.coprimeStepZeroOffset` behind its CRT step. OBJECTS.md confirmed Scala-only and correctly untouched. | Promotion complete; ticket remains the working memory for N3/N1 only. |
| 2026-08-18 | 2-gap saturation filed (user-approved, algebra-only; numerics restricted to derivation checks): balanced law ⟺ compatible coloring of the 2-gap fiber graph (forbidden-difference form, NOT a matching — corrected mid-derivation); counts/marginals coloring-blind; first placement-sensitive global statistic = separation-resolved pair count with rigid `h≡0,±2 mod r` arithmetic under the real rule. Transfer candidate's shared-value-effects bullet now characterized at complete-period level. | Filed `two-gap-placement-saturation.md` + registry row + cross-links; Learning #12 added. Remaining menu: exact-quota model.md (#4), article §8 (#5), variance audit (#6). |
| 2026-08-18 | User's inversion: define the self-propagating invariant instead of per-step hypotheses. Proved today within it: Mertens-ratio conservation (global density/benchmark exactly invariant under every transition, every placement — validated 1/6 across the post-3 chain). Perpetuity theorem filed as implication; Lemma A (spacing self-preservation at Mertens scale) isolated as the open core; seed explicitly not claimed. | Filed candidate #28 `dream-sequence-self-propagating-invariant.md`; registries (README item 28, ALGEBRA-FIRST row, matrix row 28); Learning #13. |
| 2026-08-18 | Follow-up ("so we could not define the dream yet"): the dream IS definable now — coinductively. `P* = νX.(C ∧ next⁻¹X)` ("every descendant certifies") and the weak twin `P∞` ("always eventually certifies"), hereditary by construction, `P∞` at a real stage ⟺ infinitely many twin primes. What is missing is the INTERFACE: a structural finitely-checkable strengthening invariant `P ⊆ P*` with proved closure — the verification-culture framing (invariant strengthening for a coinductive property). | Added the formal coinductive definition + strengthening-invariant framing to #28's Inversion section. Open items unchanged: Lemma A, P3 calibration, seed. |
| 2026-08-18 | User constraint (decay): 2-gap density falls forever by the exact factor `(r−2)/r` even as the count grows — the dream must never require density increase. Registered as a hard design constraint in #28: no absolute-density floors (zero-cost falsifier: every proposed invariant must survive the exact map `(N,Π) → ((r−2)N, rΠ)`); all quantities scale-relative (`κ` conserved, `S(Q)` grows ~log²); certificate engine = window growth `q²` outrunning spacing `log²q`, not density growth. | Added "Decay Compatibility" section + Limitation binding to #28. |
| 2026-08-18 | User relaxation (recurrence): direct parent→child heredity is only the `J={1}` case; `P ⟹ ∃j≥1 P(seq_j)` (recurrence) suffices for perpetuity verbatim. Gain: per-layer worst-case degradation (divergent product) weakens to INTEGRATED degradation vs. threshold growth — an averaged statement of the shape #27's mean-square machinery produces. Structural fact surfaced: 2-gap spacing is monotone non-decreasing across layers (2-gaps only die), so recovery must run through threshold growth (`log²Q` catching up), never through spacing shrinking. Design rule complete: every component scale-relative, none monotone-absolute. Matches the "infinitely many transitions" idiom #2/#10 already use. | Added "The Recurrent Generalization" to #28; Lemma A reframed as Lemma A′ (recurrent, preferred) with A as the blocked special case; Learning #14. |
| 2026-08-18 | User observation (2-focused compression keeps ~50% 2-gap share): sharpened to an exact law — post-3 strict alternation (no adjacent 2-gaps by mod-3), share exactly 1/2 at every stage, validated on three complete periods. Decay relocates into run values; Lemma A′ = max-run-value law; compressed frame = #28 Component 0. | Filed `two-focused-alternation-law.md` + registry row + #28 Component 0; Learning #15. |
| 2026-08-18 | Consolidated ledger (user's three facts): ALL counts exact (destroyed = 2N; remaining = (r−2)N; conserved κ; 50% share; 2N cells; mean run = 1/d − 2). Single unknown column: run-length distribution = placement. Twin primes = the tail of the run distribution (mean known, max open). Flag: whole-period max-run is the Jacobsthal-type condition #5 deliberately deferred as too strong; Lemma A′ needs the softer recurrent/safe-window form (runs exceeding window scale finitely often), not a global cyclic maximum. | Ledger recorded; connects #28 Lemma A′ ↔ #5's deferral classification. |
| 2026-08-18 | "One dream or many?" clarified and filed: exactly two canonical target properties (`P*`, `P∞` — greatest fixed points, not choices); MANY admissible interfaces forming a lattice under ∧/∨ (ours = Components 0+1+A′; #27-style or #24-style would be others — A′ failing sinks only one lattice element); witness sequences a constructible class (protective placement builds one by hand) — the open question is membership of the REAL chain, all-or-nothing: `P∞` at one real stage ⟺ at every stage ⟺ infinitely many twin primes. | Added "The Space Of Dreams" to #28. |
| 2026-08-18 | Closing synthesis (user's transform framing): the collapse-the-recursion-by-multiplying-a-known-sequence program is the right one and already succeeded in ONE variable (Euler product / Möbius inversion — why all counts are exact and κ conserved); it provably cannot extend to two variables because the entire arsenal is multiplicative and shift 2 is the minimal non-splitting correlation (Chowla-shaped). User's all-integers sieve failed for the cousin reason: additive schedule regularity never enters the multiplicative radical (dichotomy). Zhang/Maynard bought a collapse by widening the combination (tuple of shifts) — weakening the question; exact shift 2 has nothing to widen. Dream-conditioning is the fallback, narrower not easier. | Recorded strategic classification; session closed at the transform-vs-invariant fork with both branches mapped. |
