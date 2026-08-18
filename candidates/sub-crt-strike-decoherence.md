# Sub-CRT Strike Decoherence

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved (the chaining argument is
the deterministic discrepancy criterion of the phase-transition article's
§10; this candidate supplies its missing positional premise).

**Empirical status:** DEFERRED (UNMEASURED) — no strike-placement spectrum
or cross-head agreement count has been computed; the positional summaries
already recorded (`max_cons_destroyed_run`, `residue_max_dev`,
`endpoint_bias` in the window passes) are single-number precursors, not
spectra.

## Candidate Hypothesis

All quantities below are deterministic; no probability space is assumed for
the real sieve. Read placement in the population's own index coordinates.

Fix a prime head `Q` and its square window `W_Q=[Q,Q^2)`. Let `I_Q` be the
head indicator (`I_Q=1` iff the first gap after head `Q` equals `2`) and let
`rho_Q>0` be the companion reference weight defined by a below-frontier
cumulative hazard with
`R(X)=sum_{Q<=X prime} rho_Q -> infinity`, as in the phase-transition
article's §10.

The candidate asks for two nested statements.

**(A) Two-body head agreement.** The number of prime pairs whose heads both
carry a 2-gap matches the reference product form:

```math
\sum_{\substack{P,Q<=X\\P,Q\text{ prime}}}I_PI_Q
=
(1+o(1))\,R(X)^2.
```

**(B) Local placement decoherence.** For each installed filter `r<Q`, let
`d_r(i)` be the strike indicator on the fixed window cohort (the 2-gap
starts initially present in `W_Q`), indexed by cohort position `i`, with
`d_r(i)=1` iff that start is destroyed exactly at layer `r`. Writing
`e_r(i)=d_r(i)-K_r/N` for the centered placement residual (`N` the cohort
size, `K_r` the exact layer quota), the candidate asks that the placement
**shape** of every `d_r` — its periodogram along the index axis — lies
inside the position-blind permutation band at window scale `L`, at every
frequency above a decoherence band `B(L)` with `B(L)/L -> 0`, and that
joint residuals of three or more layers carry no persistent phase
structure beyond the two-body baseline.

Statement (B) is deliberately spectral and positional: it constrains
**where** strikes land, never **how many** — per-layer counts are exactly
determined by the accepted-strike law, and the full-period placement is
exactly determined by the CRT.

## Why It Is Sufficient

The article's §10 criterion is proved unconditionally as an implication:
if

```math
\sum_{\substack{Q<=X\\Q\text{ prime}}}(I_Q-rho_Q)=o(R(X)),
```

then `sum I_Q -> infinity`, and infinitely many distinct head 2-gaps follow
by the bounded-coverage argument (a fixed pair certifies only finitely many
heads), giving the twin-prime conclusion.

Statement (A) must be read honestly: because `I_Q^2=I_Q`, the double sum
with diagonal included is exactly the square of the single sum,

```math
\sum_{\substack{P,Q<=X\\P,Q\text{ prime}}}I_PI_Q
=
\left(\sum_{\substack{Q<=X\\Q\text{ prime}}}I_Q\right)^{\!2},
```

so (A) is *equivalent* to the §10 premise, not stronger — in the same way
candidate #10's one-sided form restates local survival. Its value is the
decomposition it licenses: (A) exposes the pair-resolved terms `I_PI_Q`,
one per prime pair, which cross-head and spectral analysis can attack
individually (matching each off-diagonal family against `rho_Prho_Q`
rather than the single global sum). Statement (B) is the genuinely finer
positional refinement; it implies (A) only through an unproved link and is
valued as the measurable shadow of it.

This candidate is the missing deterministic decorrelation premise named by
the article's §11 second future-work direction and by the
[CRT-coupled real-sieve transfer obligation](
../companions/candidates/crt-coupled-real-sieve-transfer.md).

## What Pairwise Information Is Already Exhausted

Two exact facts reclassify where the open content lives. They are recorded
here because they prune the search space of any attack.

**Fact 1 (complete periods).** On the complete final CRT period, the
centered layer observables of distinct filters are exactly orthogonal, with
exact norms and a Bessel consequence: the
[Cross-Layer CRT Orthogonality property](
../properties/sieve-sequence/accepted-strike-cross-layer-crt-orthogonality.md).
Its proved limitation is the normalization: the Bessel bound carries the
final primorial factor `R`, useless when the window length `L<<R`. The
candidate's statement (B) is precisely the local, window-normalized version
that the complete-period theorem cannot supply.

**Fact 2 (fixed cohort).** On one fixed window cohort, a member is
destroyed at exactly one layer (its first dividing filter) or survives all
layers, so the destruction sets of distinct layers are disjoint:

```math
\sum_i d_r(i)d_{r'}(i)=0
\qquad(r\ne r').
```

Consequently every **pairwise** centered covariance on the full cohort is
determined without any hypothesis:

```math
\sum_i e_r(i)e_{r'}(i)=-\frac{K_rK_{r'}}{N}
\qquad(r\ne r'),
```

by expanding the product and substituting the disjointness identity, the
exact marginals `sum_i d_r(i)=K_r`, and `delta_r=K_r/N`: the actual
covariance equals **minus** the independent-product value
`delta_rdelta_{r'}N` — disjointness flips its sign. **Pairwise cohort
covariances therefore carry no open information.** The open positional content is: (i) the shape spectrum of
single-layer placement (one-body, frequency-resolved), (ii) joint
structure of three or more layers, and (iii) cross-head agreement (A),
which concerns disjoint value pairs and is not subject to Fact 2.

## Established Inputs

- [Cross-Layer CRT Orthogonality](
  ../properties/sieve-sequence/accepted-strike-cross-layer-crt-orthogonality.md)
  — complete-period baseline and its `LR` localization obstruction.
- [Fourier bound for two-gap correlation prefixes](
  ../properties/sieve-sequence/fourier-two-gap-correlation-prefix-bound.md)
  — exact conductor weights with prime inclusion probability exactly `2/p`,
  and the proved one-dimensional prefix bound whose local (rectangle)
  extension is missing.
- [Short-interval localization destroys prime conductor decay](
  ../properties/sieve-sequence/short-interval-localization-destroys-prime-conductor-decay.md)
  — localized indicators concentrate the fraction `1-1/p` of energy in
  characters nontrivial at `p`: raw-coordinate spectra are never flat, so
  the comparison must fix the index-coordinate contract.
- [Position-blind index spectrum](
  ../companions/properties/position-blind-index-spectrum.md) — the flat
  expected spectrum `K(N-K)/(N-1)` of the position-blind null in index
  coordinates, and its deterministic contrast (subgroup placement
  concentrates all power; rotation coding concentrates on rotation
  harmonics).
- [Exact accepted local filter strikes](
  ../properties/sieve-sequence/exact-accepted-local-filter-strikes.md) —
  the per-layer quota `K_r` is exactly determined; this candidate constrains
  placement only.
- [Short-window discrepancy](short-window-discrepancy.md) (candidate #10) —
  the one-body marginal discrepancy for a single window; this candidate is
  its two-body and frequency-resolved analogue on the mixing side.

## Measurement Obligations

Design principle (recorded when this candidate was created): analyze
**positions, not sums**. Per-layer aggregate counts are exactly predicted;
only placement carries open information. The obligations, cheapest first:

1. **E1 — single-layer placement spectra.** From the per-stage gap prefixes
   (`data/sieve-sequence/first_gaps_per_seq.csv`), reconstruct survivor
   positions per stage by cumulative sums, extract each incoming filter's
   strike indicator `d_r(i)` in survivor-index coordinates (excluding the
   head value), and compute windowed periodograms against the
   position-blind permutation band. Prediction to discriminate: CRT
   placement is a rotation-coded, wheel-modulated quasi-periodic pattern
   with sharp lines; the null is flat. The decoherence band `B(L)` of
   statement (B) is the observable.
2. **E2 — cross-stage coherence in aligned coordinates.** Consecutive
   stages compared spectrally under the shared-safe-2 alignment; target the
   safe-boundary region, where View-B's near-rigid persistence is not
   trivially explained by head advance alone.
3. **E3 — lineage persistence (delayed-adversary test).** Per-individual
   fixed-cohort fate: whether destruction at layer `r'` correlates with
   layer-`r` position beyond the determined pairwise baseline of Fact 2.
4. **E4 — layer-axis field.** The (layer, position) strike point field and
   its spectra; exploratory given only ~187 measured transitions.

## Limitation

- **Necessity, not just difficulty.** The [Past-Span Saturation property](
  ../properties/sieve-sequence/past-span-saturation-does-not-determine-placement.md)
  proves that no amount of accumulated complete-period constraint can
  shape or determine strike placement — the entire past span is equivalent
  to the per-fiber quota, and placement lives in the other CRT coordinate
  permanently. The positional measurements and local theorems pursued here
  cannot be replaced by global identities.

- **No proof route is known** for either (A) or (B). The complete-period
  orthogonality cannot localize (the `LR` Bessel obstruction), the Fourier
  prefix bound needs an unproved rectangle-discrepancy extension, and
  localization provably concentrates raw-coordinate spectra. The candidate
  names the missing theorem; it does not supply a strategy for it.
- **Finite spectra cannot prove the asymptotic statements.** E1–E4 gather
  evidence about placement shape; they cannot establish (A) or the
  decoherence band limit. Their outcome can only locate the real sieve
  relative to the position-blind and structured extremes.
- **Coordinate dependence.** All placement-shape claims hold in index
  coordinates only, per the contract in the position-blind spectrum
  property; raw-coordinate spectra are dominated by wheel and localization
  effects for every placement family.
- **Head-availability is a separate premise.** Even with (A), the reference
  weights require the availability input; this candidate does not supply
  it.

## Related

- [Short-window discrepancy](short-window-discrepancy.md) — one-body window
  marginal (candidate #10).
- [Random-like merge survival](random-like-merge-survival.md) — the
  benchmark whose deterministic transference this candidate spectralizes
  (candidate #11).
- [CRT-coupled real-sieve transfer](
  ../companions/candidates/crt-coupled-real-sieve-transfer.md) — the
  transfer obligation this candidate serves.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §10–§11](
  ../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
  — the proved discrepancy criterion and the named future-work directions.
- Ticket `tickets/active/spectral-positional-filter-analysis-2026-08-18.md`
  — working memory for E1–E4.
