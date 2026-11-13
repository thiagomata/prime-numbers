# Rigid-Pair Shot Companion for Survival Frontiers

**Created:** 2026-09-21
**Updated:** 2026-10-07
**Status:** Plan phase
**Depends on:** none hard (builds on verified `SpecSieveSeqTwoGapProperties` lemmas and the coherent winding law notes in `backward-head-two-gap-bound-2026-08-29.md`)

## Related Tickets

- `backward-head-two-gap-bound-2026-08-29.md` — states the coherent winding law
  `k_(i+1) - k_i = -g_i * M^(-1) mod r`, the 2-gap corollary that the
  right-endpoint harmful class is always `k_i - 2*M^(-1) mod r`, and the
  circular phase law (one unwrapped parent period shifts the harmful phase by
  `-1 mod r`; a coherent adversary has at most `r` global phase choices rather
  than independent per-parent choices). The fixed-Δ statement this ticket
  needs already lives there as design notes — promote it, do not reprove it.
- `verify-real-two-gap-copy-survival-2026-08-14.md` — Stainless verification of
  the local copy law (`assertExactlyTwoDestroyedCopies`,
  `assertForbiddenLiftOffsetsDistinct`, `assertDestroyedCountEqualsEndpointCounts`).
  Its remaining work (cyclic aggregation including the wrap gap) overlaps this
  ticket's circular-correction item.
- `survival-frontiers-promotion-2026-09-13.md`,
  `survival-frontiers-article-review-2026-09-13.md` — the companion article
  that tightened models would feed back into. Any article content change
  triggers the `arxiv-sync` rule (survival-frontiers has an arXiv package).
- `companions-folder-properties-of-models-2026-08-12.md` — governance precedent
  for placing companion material (`companions/candidates/` for transfer notes,
  cf. `companions/candidates/crt-coupled-real-sieve-transfer.md`).

## Related Permanent Records

Properties (proved notes):

- `properties/sieve-sequence/copy-index-filter-frequency.md` — the exact
  copy-index law: two forbidden classes `j ≡ -a*M^(-1)` and
  `j ≡ -(a+2)*M^(-1) (mod r)`, their distinctness via `2*M^(-1) ≢ 0`, exactly
  2 destroyed / r-2 survivors per complete block. The fixed difference Δ is
  computed inside the distinctness proof but never isolated as a named theorem.
- `properties/sieve-sequence/coherent-head-suppression-is-shifted-prime-shot-coverage.md`
  — proved coherence statement (real shots are shifted residue classes; shot
  spacing, cyclic sums, shared endpoints, CRT compatibility automatic).
- `properties/sieve-sequence/two-gap-pair-local-factor-by-separation.md` —
  forbidden-translation count for two 2-gaps separated by d depends only on
  `p | d, d-2, d+2`.
- `properties/sieve-sequence/realized-filter-adversariality-score.md` —
  calibrates realized destruction against the `2/p` uniform benchmark (the
  existing real-vs-companion bridge).
- `properties/sieve-sequence/head-self-deletion-shot-chain.md` (untracked at
  ticket creation) — head self-deletion chain; closing gap of the head-anchored
  cycle is always the merged gap.
- Wrap/circular ingredients: `rotation-preserves-cyclic-gap-counts.md`,
  `exact-global-two-gap-count.md`, `absence-of-two-gaps-is-stable.md`
  (copy-or-merge), and `SieveUtils.assertWrapGapPositive`
  (`src/main/scala/v1/chapter6/sieve/seq/spec/SieveUtils.scala:565`).

Candidates:

- `candidates/hereditary-shot-spacing-capacity.md` — rigid cyclic shot geometry
  in numerical form (fixed shot count, periodic `Δ_i`, `Σ Δ_i = r*M_r`),
  used as "rigid capacity"; notes the geometry alone does not prove hereditary
  surplus.
- `candidates/infinite-perfect-scenario-property.md` — treats the derivation of
  the two forbidden copy classes per prime as an open obligation in the
  scenario setting.

Code:

- `src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala`
  — `assertForbiddenLiftOffsetsDistinct`, `assertExactlyTwoDestroyedCopies`,
  `assertExactlyHeadMinusTwoCopiesSurvive`, `assertDestroyedCountEqualsEndpointCounts`,
  `countDestroyedTwoGapCopies`.
- `src/main/scala/v1/chapter5/prime/BezoutUtils.scala` — `coprimeStepZeroOffset`
  (the `M^(-1)` machinery), `assertCoprimeStepAtMostOneZero`.

Articles (the models this ticket critiques):

- `articles/chapter7/survival-frontiers.md` + `articles/arxiv/survival-frontiers/`
  — Preliminaries define random / adversarial / protective parents where "each
  parent receives one of three policies" over two distinct harmful indices; the
  random parent draws the harmful pair uniformly from the two-element subsets
  of `Z/rZ`. Notation: `f_r`, `f̂_r`, `w_r = r*f_r/2`, `D(Q) = Σ -log(1-f_r)`.
- `articles/chapter6/gap-dynamics.md` §3.2 (+
  `articles/arxiv/gap-dynamics/sections/03-complete-period-two-gap-properties.tex`)
  — the copy-index law edition.

## Goal

Tighten the local-destruction calculation inside the survival-frontiers
companion framework so it matches the arithmetic reality of the sieve, by:

1. **Rigid-pair model** — replace the uniform 2-subset draw with a uniform
   random *translate* of the fixed difference Δ:
   `{j0, j0 + Δ} mod r`, `j0` uniform in `{0..r-1}`, where
   `Δ ≡ 2*M^(-1) (mod r)`.
2. **Circular correction** — carry an explicit wrap-around term when evaluating
   destruction in finite windows or near the head (the last gap of the old
   period is a potential merge point; a strike on it shifts all subsequent
   absolute positions).
3. **Empirical `ŵ_r`** — measure the hit rate of the two arithmetic residues on
   the real sequence data (globally and restricted to the square-safe prefix /
   first gaps after the head), yielding the true local destruction factor of
   the sieve rather than of a companion.

Done means: the fixed-Δ fact is an isolated verified lemma; the rigid-pair
companion exists as a candidate/companion note with its `f_r` (or its block
variant) computed by a modular arithmetic check; the circular correction and
the empirical `ŵ_r` method are documented; the survival-frontiers article
reflects the distinction honestly (framing-integrity) or an explicit decision
records why the article is left as an approximation.

## Strategy

Promote, then model, then measure — in that order, one verify cycle each where
verification applies. The fixed-Δ lemma first because every later item cites
it and it is a one-lemma change against existing machinery (`BezoutUtils`
inverse offsets + the two-gap endpoint divisibility already in
`SpecSieveSeqTwoGapProperties`). The companion model second, placed in
`companions/candidates/` (transfer-note precedent) to avoid prematurely
rewriting the article. The empirical measurement last since it needs no new
verification. Rationale for ordering: cheapest-and-foundational first, and the
`small-changes` rule forbids batching the lemma with anything else.

## Current State

Path A is complete. The fixed-distance lemma is verified, indexed in
`OBJECTS.md`, and promoted to `properties/sieve-sequence/fixed-shot-distance.md`.
The inventory above was assembled by a full search on
2026-09-21 (properties/, candidates/, src/main/scala, articles/, OBJECTS.md,
tickets/). On 2026-10-06 the working tree was clean and the Chapter 6 baseline
was green (`logs/verify-ch-6-v1-chapter6-_.log`: total 4593, valid 4593).
Key existing facts this ticket builds on:

- The two forbidden classes and their distinctness are Stainless-verified
  (`assertForbiddenLiftOffsetsDistinct` — phrased as "p cannot divide two
  values differing by 2", which is `Δ ≢ 0 mod r`).
- Exactly-2-destroyed / (r-2)-survivors per complete block verified.
- The global `2/r` average rate is model-independent (counting argument), so
  the rigid-pair change affects distributions/correlations, not the mean.
- The coherent winding law and circular phase law exist only as ticket notes
  (see Related Tickets), not as properties.
- `BezoutUtils.coprimeStepResidueOffset(step,p,target)` exposes the reusable
  inverse-step witness surface: it returns the unique offset in `[0,p)` with
  `mod(offset*step,p) == target`. This is likely a better proof target than
  introducing a separate inverse notation.
- New lemma `assertRightForbiddenLiftOffsetHasFixedSeparation` is focused-green
  (`just verify assertRightForbiddenLiftOffsetHasFixedSeparation`: total 98,
  valid 98). It states
  `leftOffset == mod(rightOffset + fixedSeparation, p)`, where
  `fixedSeparation` is the canonical offset with
  `mod(fixedSeparation * step, p) == 2`.
- Chapter 6 regression is green after the lemma:
  `just verify-ch 6` produced `total: 4691 valid: 4691`.
- Permanent records updated:
  `OBJECTS.md`, `properties/sieve-sequence/README.md`, and
  `properties/sieve-sequence/fixed-shot-distance.md`.
- (2026-10-07) Editorial pass over
  `articles/notes/drafts/cluster-exposure-frontiers.md`: every reported
  number was checked against the generated CSVs (all matched except one), and
  the fix set was applied — exact extinction count 39384 (was ~39387, a
  rounding slip), row-level direct/effective equality wording, relative SVG
  links, head-67 global-max adversariality 5.36 clarification, an
  aggregate-histogram mixture explanation, and a stride-1 overlap caveat in
  Limitations. Markdown-only; no runtime gates.

## Expected State

- New `.holds` lemma in `SpecSieveSeqTwoGapProperties.scala` (name TBD, e.g.
  `assertSecondOffsetIsFirstMinusTwoInverse`): for a 2-gap with left-endpoint
  harmful offset `k`, the right-endpoint harmful offset is
  `k - 2*M^(-1) mod r`. Exactly one new assertion; verification count +1 valid.
- New note `properties/sieve-sequence/fixed-shot-distance.md` (or candidate
  file, decided at promotion time) documenting the rigid translate pair.
- New `companions/candidates/rigid-pair-companion.md` defining the translate
  draw, its `f_r` for a distinguished index and for short consecutive blocks,
  and comparing against the uniform-2-subset companion.
- Circular-correction section (wrap term `O(1/r)` on average, head case) and
  the `ŵ_r` measurement recipe, either in the same companion note or a sibling.
- OBJECTS.md updated after the lemma verifies; no article edits before
  verification (rule: docs follow verification).

## The Proposal (mathematical content)

For an old 2-gap starting at residue `a`, old period `M`, incoming prime `r`
coprime to `M`, the two forbidden copy indices are

```text
j ≡ -a * M^(-1)   (mod r)
j ≡ -(a+2) * M^(-1)   (mod r)
```

so their difference is fixed:

```text
Δ ≡ 2 * M^(-1)   (mod r),   Δ ≢ 0 (mod r)  for r > 2.
```

Every parent experiences the same modular distance between its two harmful
children — the removals are a rigid translate pair, not an arbitrary pair.
Additionally the object is cyclic: gaps in one complete period sum exactly to
`M`, the wrap-around gap is special, and copy-or-merge at the boundary must
respect circular consistency (a strike on or straddling the boundary merges
pieces on either side of the cut).

The balanced companions ignore both constraints: a random parent draws a
uniform 2-element subset of `{0..r-1}` (all `C(r,2)` pairs, most with mutual
distance ≠ Δ); adversarial/protective parents place deletions freely; neither
is forced to keep the gap sum equal to the new period nor to treat the
wrap-around position differently. Hence the companion `f_r` / `w_r` is only an
approximation: the true conditional destruction rate for a tracked lineage is
the probability that one of two *specifically spaced* residues hits it,
subject to circular accounting. The mean is still exactly `2/r` (same counting
argument as `N_(k+1) = (r-2)*N_k`), but the distribution over lineages,
neighbour correlations, and head/period-boundary behavior differ.

Tightening mechanics:

1. **Rigid-pair draw** — `{j0, j0 + Δ} mod r`, `j0` uniform. Removes exactly
   two copies per parent, preserves the global count, matches the arithmetic
   geometry. The `r` translates are distinct as unordered sets because
   `2Δ ≢ 0`. The conditional `f_r` for a distinguished index (or a short
   consecutive block) becomes a single modular check instead of an average
   over all pairs.
2. **Circular term** — the last gap of the old period is always a potential
   merge point; a strike on it changes the closing-gap length and shifts
   absolute positions of subsequent residues by a multiple of the old period.
   `O(1/r)` on average, non-negligible at the extreme head position (see
   `head-self-deletion-shot-chain.md` Step 2: the closing gap is *always* the
   merged gap).
3. **Empirical `ŵ_r`** — the author's stage gap data suffice to measure the
   hit rate of the two arithmetic residues directly; this automatically
   incorporates Δ and circular merges.

## Approaches Considered

### Path A — Isolate the fixed-Δ lemma first

**Status:** RECOMMENDED

One `.holds` in `SpecSieveSeqTwoGapProperties.scala`: relate the second
forbidden lift offset to the first minus `2*M^(-1) mod r`, reusing
`coprimeStepZeroOffset` and the endpoint-divisibility predicates already in the
class.

**Strengths:** one small change; machinery exists; every later item cites it.
**Risks:** modular-inverse arithmetic in Stainless — must use `Calc.div` /
`Calc.mod`, never `%`; potential timeout if stated in fully general form.
**Fallback:** state it for the concrete witness form the existing lemmas use
(same shape as `assertForbiddenLiftOffsetsDistinct`) before generalizing.

### Path B — Rigid-pair companion candidate

**Status:** UNTESTED (after Path A)

`companions/candidates/rigid-pair-companion.md`: define the translate draw,
derive `f_r` for a single distinguished index (translation invariance gives
`2/r` exactly) and for a block of length `L < r` (depends on `L` and Δ via a
two-point hit probability), compare with the uniform-2-subset companion, and
record which article claims survive the change (the mean; the independence
assumptions do not).

**Strengths:** markdown-only at this stage; direct precedent in
`companions/candidates/`.
**Risks:** block-variant `f̂_r` may involve case analysis on `Δ` vs `L` that
wants its own candidate; scope creep into rewriting the article.
**Fallback:** record the single-index result and leave the block variant as an
open concern rather than forcing a complete treatment.

### Path C — Circular correction + empirical `ŵ_r`

**Status:** UNTESTED

Document the wrap term and the measurement recipe (data: existing stage gap
records; cf. candidate #14's empirical `destroyed = A(p,q) = 2` records and
`realized-filter-adversariality-score.md`).

**Strengths:** no verification burden; reuses existing data.
**Risks:** measurement restricted to small primes; must not be presented as
verification (label as empirical).
**Fallback:** keep as a documented method without running it in this ticket.

## Assumptions

- `r > 2` prime and `gcd(r, M) = 1`, so `M^(-1) mod r` exists (backed by
  `BezoutUtils.coprimeStepZeroOffset` / `assertCoprimeStepAtMostOneZero`).
- The two offsets are distinct (verified), hence the pair is genuinely
  2-pointed and the `r` translates are distinct sets.
- The global per-parent destruction count (2) and survivor count (r-2) are
  policy-invariant (verified for the real sieve; assumed for companion
  policies per the article's own framing).

## Risks

- Stainless modular arithmetic: `%` is forbidden; `Calc.mod` /
  `Calc.div` only. Distinctness proofs in this file already encode the needed
  shape, which lowers but does not eliminate timeout risk.
- Companion/article coupling: if the survival-frontiers article is edited to
  reflect the rigid-pair distinction, the `arxiv-sync` rule requires the LaTeX
  package update + green PDF rebuild + `just arxiv-parity` PASS in the same
  unit of work.
- Framing-integrity: the article currently presents companion `f_r` as an
  approximation implicitly; any tightening must not overclaim ("strictly
  tighter" needs the block-variant comparison to back it).

## Open Concerns

- Where the fixed-Δ note lands (`properties/` vs `candidates/`): it is
  mathematically forced by verified lemmas but not yet verified itself — if
  drafted before verification it must carry the draft-pending marking per
  `property-completeness` rule 8.
- The block-variant hit probability may depend on more than `(L, Δ)` once
  several filters compose (CRT coupling — cf.
  `crt-coupled-real-sieve-transfer.md`); single-layer scope is safer for a
  first result.
- Whether the empirical `ŵ_r` measurement belongs in this repo's data
  pipeline or as a documented recipe only — decide at Path C start.
- `head-self-deletion-shot-chain.md` is still untracked in git; this ticket
  references it and assumes it will be committed.

## Validation

- Path A: `just verify assertSecondOffsetIsFirstMinusTwoInverse` (or final
  name) for fast iteration, then `just verify-ch 6` chapter regression; total
  valid count must not decrease (`grep "total:" logs/verify.log` /
  `logs/verify-ch-*.log`).
- Paths B/C: markdown-only — no runtime gates unless executable instructions
  are added (`green-to-green`).
- Any article change: full `arxiv-sync` gate sequence (build clean,
  `just arxiv-parity survival-frontiers` PASS).

## Implementation Plan

1. Path A lemma — one new `.holds`, one verify cycle —
   `src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala`
2. Update OBJECTS.md (6.5.1 table) + promote the fixed-Δ note into
   `properties/sieve-sequence/` — docs after verification.
3. Path B candidate — `companions/candidates/rigid-pair-companion.md`.
4. Path C — circular-correction section + `ŵ_r` recipe (same or sibling note).
5. Decide (explicitly, recorded here) whether `survival-frontiers.md` gets a
   limitation/pointer; if yes, schedule as its own arxiv-sync unit of work.

## Fallback Options

- If the general fixed-Δ lemma times out: state the identity for the witness
  form used by `assertForbiddenLiftOffsetsDistinct` (fallback in Path A), or
  record the identity as a draft-pending property with the ticket-tracking
  required by `property-completeness` rule 8.
- If the block-variant derivation stalls: ship the single-index result and the
  circular term; leave blocks as an open concern (do not silently skip).
- If article coupling becomes large: keep the companion note self-contained
  and surface the article question to the user instead of improvising an
  article rewrite (stay-on-track).

## What is Learned

- (2026-09-21) The fixed-Δ fact is *used* in three places (distinctness proof
  in `copy-index-filter-frequency.md` + §3.2; the coherent winding law in
  `backward-head-two-gap-bound-2026-08-29.md`; implicitly in
  `assertDestroyedCountEqualsEndpointCounts`) but isolated nowhere — no
  `.holds` states `Δ ≡ 2*M^(-1) (mod r)` as a theorem.
- (2026-09-21) The coherent-vs-independent distinction (≤ r global phase
  choices) is the existing framing closest to "rigid pair vs arbitrary
  subset"; reuse its vocabulary.
- (2026-09-21) The mean `2/r` is model-invariant; only distributions,
  correlations, and boundary behavior distinguish the models — this bounds
  what the rigid-pair companion can improve.
- (2026-10-06) Chapter 6 baseline before Path A is green:
  `total: 4593 valid: 4593` in `logs/verify-ch-6-v1-chapter6-_.log`.
- (2026-10-06) Existing code has no isolated fixed-Δ lemma in
  `SpecSieveSeqTwoGapProperties` or `OBJECTS.md`; the closest reusable
  primitive is `BezoutUtils.coprimeStepResidueOffset`, whose postcondition
  gives `mod(offset * step, p) == target`.
- (2026-10-06) The solver accepted the fixed-separation form
  `leftOffset == mod(rightOffset + fixedSeparation, p)`. This orients the
  distance from the right endpoint's forbidden lift offset back to the left
  endpoint's forbidden lift offset, matching the equation
  `right = left + 2`.
- (2026-10-06) Path A documentation is now promoted: the fixed-distance fact
  has a property note and an `OBJECTS.md` entry. No article was edited, so
  `arxiv-sync` was not triggered.
- (2026-10-06) The fixed-distance property should be explained as object
  geometry as well as algebra: the two harmful lift indices are endpoint tests
  attached to one copied 2-gap object, so the object's internal length `2`
  forces the offset separation before any companion randomness is introduced.
- (2026-10-06) The richer cluster/forest question is a separate article idea,
  not a section to mix deeply into survival-frontiers. Drafted the concept at
  `articles/notes/drafts/cluster-exposure-local-extinction.md`.
- (2026-10-06) Added a Python empirical helper for the first generated
  sequences: `sieve_sequence.cluster_exposure_cli` reads
  `first_gaps_per_seq.csv`, slides fixed-size clusters over consecutive
  2-gap candidates, and writes an exposure curve plus per-stage summary stats.
- (2026-10-06) First empirical run over the first 20 generated sequences with
  prefix length 10000, cluster size 25, stride 1 produced 54056 clusters:
  exposure min 0, max 17, avg 5.78254, stddev 5.89357; adversariality min 0,
  max 5.36, avg 1.04205, stddev 0.607146. Outputs:
  `data/candidates/cluster-exposure-curve.csv`,
  `data/candidates/cluster-exposure-summary.csv`,
  `data/candidates/cluster-exposure-curve.svg`.
- (2026-10-06) Added a fixed-seed random baseline overlay to the cluster
  exposure curve. For the same first-20 run with seed 1, baseline exposure
  min 0, max 24, avg 5.74491, stddev 6.11429. The measured prefix curve and
  baseline curve now share `cluster-exposure-curve.csv` and the same SVG plot.
- (2026-10-06) Reworked the SVG from a bar histogram into distribution lines:
  one faint CDF line per stage, a thick aggregate measured-prefix CDF, and a
  dashed random baseline CDF.
- (2026-10-06) Renamed the empirical curve labels from "real" to "measured" /
  "prefix" to avoid overclaiming. The plot is a prefix-data measurement plus a
  random baseline, not the true underlying sieve law.
- (2026-10-06) Added a first post-merge effective survival metric: after
  deleting values divisible by the stage head, count 2-gaps remaining inside
  the same cluster value span. For the first-20 run, direct and effective
  survival rates coincide: min 0.32, max 1, avg 0.768698, stddev 0.235743.
  This suggests endpoint deletion removes original local 2-gaps but does not
  create replacement 2-gaps inside these measured spans.
- (2026-10-06) Added an aggression sweep for the random companion filter:
  keep the measured prefix curve fixed, then multiply the companion hit
  probability scale until local cluster extinction appears. For the first-20
  run with aggression max 20 and 40 steps, the midpoint threshold is
  `extinction_rate >= 0.5` at aggression `8.79487`; at aggression `20`, average
  survival is `0.0784061` and extinction rate is `0.728578`. Outputs:
  `data/candidates/cluster-exposure-aggression.csv` and
  `data/candidates/cluster-exposure-aggression.svg`. This is a pressure-test
  companion curve, not a claim that the deterministic sieve has been solved.
- (2026-10-06) Drafted an article-shaped note at
  `articles/notes/drafts/cluster-exposure-frontiers.md`, using the existing
  article structure: author/status metadata, abstract, introduction,
  preliminaries/evidence boundary, model definitions, empirical figures,
  limitations, conclusion, and reproducibility. It is intentionally framed as
  finite prefix measurement plus companion simulation, with no asymptotic claim
  for the real sieve.
- (2026-10-06) Refined the draft article to show the calculation process
  explicitly: row-level endpoint exposure, random mean, adversariality,
  direct/effective survival, histogram/CDF aggregation, mean/stddev formulas,
  and aggression-sweep survival/extinction calculations are now derived
  step-by-step instead of only reported as final numbers.
- (2026-10-06) Retuned the calculation sections toward the existing article
  proof style: prose prepares each math block, aligned equations carry
  bracketed right-side tags such as `[By Definition]`, `[Substitution]`, and
  `[Q.E.D.]`, and each block is followed by a short interpretation.

## Failed Paths

None yet. (Ticket created from a proposal; no attempts made.)

## Next Action

Path A, step 1: draft the single `.holds` lemma asserting the second forbidden
lift offset equals the first minus `2*M^(-1) (mod r)` for a 2-gap, modeled on
`assertForbiddenLiftOffsetsDistinct`'s witness form, and run
`just verify <name>`. Before writing: re-read
`SpecSieveSeqTwoGapProperties.scala` and `BezoutUtils.coprimeStepZeroOffset`
bodies (search-primacy), and confirm no equivalent lemma exists under another
name.

Micro-goal for the next step: start Path B by drafting
`companions/candidates/rigid-pair-companion.md`. Keep it markdown-only unless
an executable measurement recipe is added; derive the single-index `2/p`
result first and leave the short-block case explicitly bounded if it starts
to sprawl.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-21 | Ticket created from user proposal. Full inventory search done: ingredients proved (copy law, wrap lemmas, coherence), fixed-Δ never isolated, no rigid-pair companion exists, circular correction and empirical `ŵ_r` absent. | Start Path A: draft fixed-Δ `.holds` lemma. |
| 2026-10-06 | Re-read ticket discipline, LEARNINGS, `SpecSieveSeqTwoGapProperties`, `BezoutUtils.coprimeStepZeroOffset`, and searched for existing offset/mod lemmas. Baseline Chapter 6 is green at 4593/4593; no fixed-Δ theorem exists yet. | Add one lemma using `coprimeStepResidueOffset(step,p,2)` as the fixed separation witness, then verify only that lemma. |
| 2026-10-06 | Added `assertRightForbiddenLiftOffsetHasFixedSeparation`; focused verification passed (`total: 98 valid: 98`). | Run `just verify-ch 6` before updating docs. |
| 2026-10-06 | Chapter 6 regression passed (`total: 4691 valid: 4691`). Updated `OBJECTS.md`, the property README registry, and added `fixed-shot-distance.md`. | Start Path B rigid-pair companion candidate. |
| 2026-10-06 | Enriched `fixed-shot-distance.md` with the object-geometry framing: endpoint shots are coupled by one copied 2-gap object, and the algebra is the coordinate expression of that geometry. | Reuse this framing in Path B and any later article edit. |
| 2026-10-06 | Drafted a separate forest-level concept note for cluster exposure curves, extinction thresholds, and adversariality scores. | Keep survival-frontiers clear; use the draft as a later article seed. |
| 2026-10-06 | Implemented the first empirical cluster-exposure script and tests. The CLI generated curve, summary, and SVG outputs for the first 20 sequences; Python regression passed (`30 passed`). | Use the generated curve as the first empirical picture; next refinement would add effective post-merge exposure. |
| 2026-10-06 | Added the random baseline companion curve to the same CSV/SVG plot. Python regression passed (`32 passed`). | Compare real-vs-baseline tails before deciding whether to add merge-effective exposure. |
| 2026-10-06 | Corrected the visualization from a bar chart to multi-line distribution curves. Python regression still passes (`32 passed`). | Use the SVG as the visual comparison artifact. |
| 2026-10-06 | Corrected overconfident "real" labels to "measured prefix" / "prefix aggregate" in code, CSV, SVG, and tests. | Keep empirical language humble until an algebraic distribution law is proved. |
| 2026-10-06 | Added direct and effective post-filter survival rates. The first-20 run has identical direct/effective survival aggregates, and Python regression passed (`33 passed`). | Treat merge side effects as a boundary effect to inspect with wider spans/cyclic windows, not as a replacement-2-gap source in these prefix clusters. |
| 2026-10-06 | Added an aggression sweep that scales the random companion filter until cluster extinction becomes common. The first-20 run crosses 50% extinct clusters at aggression `8.79487`; at aggression `20`, average survival is about `7.84%` and extinction is about `72.86%`. Python regression passed (`35 passed`). | Use the aggression plot as the extinction-frontier baseline, then stratify by cluster density / average 2-gap spacing relative to `p` if we want to test the user's nearby-gap hypothesis. |
| 2026-10-06 | Drafted `cluster-exposure-frontiers.md` in the notes draft folder and tuned it toward the tone/structure of the existing articles. | Next article-level refinement is density stratification; no published chapter article was edited, so arXiv sync was not triggered. |
| 2026-10-06 | Added explicit step-by-step calculation blocks to the cluster exposure draft so the reported empirical numbers are reproducible from the definitions in the text. | Keep this style for later empirical articles: formulas first, rows/tables second, interpretation third. |
| 2026-10-06 | Adjusted the calculation blocks to match the house article rhythm: preparation prose, bracketed proof-step tags on the right, and a summary sentence after each block. | Use this as the style target before promoting the draft beyond `articles/notes/drafts/`. |
| 2026-10-07 | Verified all draft numbers against the cluster-exposure CSVs (all matched except the extinction count) and applied the editorial fix set: extinction count is exactly 39384 (old ~39387 came from multiplying by the rounded rate 0.7286), row-level direct/effective equality, relative SVG links, head-67 max adversariality 5.36, aggregate-histogram mixture explanation, stride-1 overlap caveat. | Density stratification remains the next measurement. Promotion beyond `notes/drafts/` would require dropping the `properties/` link per the no-internal-materials rule for articles. |
| 2026-10-07 | User call: image embeds stay absolute during draft editing. Relative image links are tied to git state — the drafts folder and the `data/candidates/cluster-exposure-*` outputs are untracked, and master does not have them — so the relative form would break as soon as the files move, and only works after commit + merge. | Keep `![...](/Users/...)` until the draft and its data are committed; convert to relative links in the same unit of work as the commit/promotion (tracked in the improvement-notes item 3). |
