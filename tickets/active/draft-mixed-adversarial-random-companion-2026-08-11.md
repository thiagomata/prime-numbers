# Draft Mixed Adversarial/Random 2-Gap Companion Article

## START HERE

The abstract's impersonal-voice edit is complete. Its two first-person clauses
were replaced with direct subject-led constructions without changing any
mathematical claim or qualification. Await user review.

## Goal

Create an honestly framed draft article explaining how much adversarial local
filter behavior the balanced 2-gap companion can tolerate while retaining
safe-window and head 2-gaps. The article is complete when it clearly separates
unconditional global persistence from conditional spatial conclusions, derives
the constant-mixture and varying-mixture thresholds, distinguishes adversarial
amount from targeting ability, covers both adversarial/random and
adversarial/protective mixtures,
links its source notes, and does not claim a theorem about the real deterministic
sieve.

## Strategy

Synthesize rather than invent. Use the exact `r-2` descendant law from the
balanced companion candidates, the mixture rate already recorded in
`realized-filter-adversariality-score.md`, and the uniform-position/Borel-Cantelli
conditional from the balanced randomized companion. Present the central
correction prominently: every fixed positive per-filter adversarial fraction
compounds quickly enough to defeat the growing square-window expectation.
Treat decaying adversarial schedules and the head separately because their
criteria are, respectively, a cumulative budget and a divergent occurrence
series. Extend the synthesis with an allocation axis: derive exact targeted,
uniform, and protective bounds before presenting assignment mechanisms or
simulation proposals.

The primary parametrization is now the realized segment destruction fraction
`f_r` relative to the shrinking random benchmark `2/r`, namely
`w_r=f_r/(2/r)`. Absolute adversarial shares `alpha_r` are retained only as a
specialization. This directly answers how much worse than random the filter can
be without inserting a trivial positive destruction floor.

## Current State

- User review found that the introduction's first sentence assumes the central
  vocabulary instead of establishing it. The opening must define the sieve's
  surviving numbers, gaps between consecutive survivors, the special role of
  gap 2, and its twin-prime significance before discussing survival regimes.
- The required foundation is confirmed in the published Gap Dynamics article:
  stage survivors avoid all smaller prime divisors, adjacent survivors define
  the cyclic gaps, a 2-gap has endpoints `(x,x+2)`, and a certified pair later
  appears as the first gap after head `x`.
- The introduction now presents that foundation before any survival taxonomy.
  It also replaces the category error “the head is a 2-gap” with the precise
  statement that the first gap after the distinguished head equals `2`.
- The user has made print-only self-containment the governing article standard.
  Repository links may provide verification, provenance, data, or reproducible
  calculations, but the reader must not need to follow them to understand the
  article's setting, problem, argument, results, limitations, or conclusion.
- `PROOF_GUIDE.md` now defines the four-part print-only test, and
  `LEARNINGS.md` §14.20 preserves it as a repository-wide editorial lesson.
- The rewritten introduction currently explains the periodic survivor object
  and now identifies it as the previously introduced Sieve Sequence, with an
  inline citation to `articles/chapter6/sieve-sequence.md` and a matching §12
  reference entry.
- Before normalization, §12 used bare Markdown bullets, whereas the finished
  articles use numbered HTML anchors and matching `[[n]](#refn)` body markers.
  The two sources are Mata (2026), *Formal Verification of Sieve Sequence Stages
  and Their Transitions*, and Mata (2026), *Structural Properties and Open
  Boundaries of 2-Gaps in Sieve Sequences*.
- §12 now uses the finished-series format: two uniquely anchored numbered
  entries with author, year, italicized exact title, and a resolving local-
  article link. Both scoped and repository-wide whitespace checks are green.
- The body now contains exactly one `ref1` marker for the Sieve Sequence source
  and six `ref2` markers for section-level Gap Dynamics sources. Both anchors
  are unique, both source targets exist, and scoped plus repository-wide diff
  checks are green.
- Independent review found eight publication blockers: the `c=1` window caption
  contradicts its formula and data; decreasing `L/N` does not alone imply
  crossover; mixing and deterministic transfer premises are not formally
  defined; exact-quota framing omits cumulative hypotheses; global persistence
  omits `N_0>0`; five images use stale paths; classical asymptotic sources are
  uncited; and the appendix/status language overstates proof completeness.
- The §3.4 prose and alt text now correctly put exact `c=1` on the failure side
  with `lambda_1(Q) ~ C/(log Q)^2 -> 0`; scoped and repository-wide Markdown
  diff checks pass.
- The phase-transition window generator and regenerated
  `charts/phase-transition-window.svg` now agree with the formula and article.
  The corrected annotation is present, all six plotted polylines remain intact,
  and the full Python suite passes 249/249.
- The body proof of global persistence now states the necessary premise
  `N_0>0` and cites it in the product-positivity step.
- Appendix A.1 now carries the same premise and correctly describes the result
  as unconditional with respect to allocation once the initial population is
  nonzero.
- Section 5.1 now derives eventual targeted-window capacity from the sufficient
  conditions `alpha>0` fixed and `L/N -> 0`, rather than from decrease alone.
- Appendix A.6 now preserves the same `L/N -> 0` premise in its closing
  capacity statement.
- The abstract now conditions the exact-quota frontiers on both the shared
  spatial premises and §7.1's cumulative quota/error bounds, and explicitly
  rejects inference from one retained CRT count.
- The conclusion now likewise separates the neutral exact-quota survival scale
  from the biased companion's effective-skew frontier and names their premises.
- The head phase-transition image link now resolves to the existing asset in
  `charts/`.
- The per-sequence frontier image link now also resolves to `charts/`.
- The per-transition frontier comparison image link now resolves to `charts/`.
- The full-cycle destruction image link now resolves to `charts/`.
- The full-cycle survival image link now resolves to `charts/`; all five stale
  figure paths identified by review are repaired.
- Section 2.1 now defines adequate cross-layer mixing by an explicit
  head-event intersection-sum asymptotic, with independence as a sufficient
  special case and the Kochen--Stone consequence stated.
- Section 10 now gives a precise deterministic transfer criterion using the
  real indicator `I_Q`, reference weights `rho_Q`, divergent mass `R(X)`, and
  an `o(R(X))` discrepancy bound; the real-sieve bound remains unproved.
- Section 8's transfer checklist now points to that deterministic discrepancy
  condition instead of reusing stochastic mixing language.
- The abstract's twin-prime implication now names persistent availability and
  the §10 deterministic discrepancy bound rather than stochastic mixing.
- Bibliography entry [3] now records Kochen and Stone's 1964 paper with its
  journal metadata and DOI.
- Section 2.1 now cites entry [3] at the Kochen--Stone recurrence step.
- Bibliography entry [4] now records the official sixth-edition Hardy--Wright
  source for the classical prime asymptotics.
- Section 3.3 now cites [4] for the Prime Number Theorem, prime harmonic
  estimate, and partial-summation consequences used throughout the article.
- Appendix A is now explicitly a selected set of six core proof records, not a
  claim to catalog every result in the body.
- The user clarified that this mathematical/probabilistic article contains no
  Scala or Stainless implementation and should not foreground tooling status.
- The eighteen-row verification-status table is removed; exactly one compact
  Stainless-pending scope sentence remains in the article.
- Before this edit, the abstract contained two first-person clauses: `We study`
  and `we compare`.
- The abstract now contains no first-person forms; it begins with `This article
  examines`, and the relative-hazard sentence makes the destruction fraction
  its subject.
- Final validation is green: 41 Markdown links have no missing local targets,
  15 internal references have no missing anchors, 372 fences are balanced,
  `git diff --check` passes, the chart module imports, and all 249 Python tests
  pass.
- The approved introductory figure is `charts/gap-heatmap-2focused.svg`, the
  non-staggered compression view. Its generator is
  `python/src/sieve_sequence/gap_heatmap.py`.
- The figure is now embedded in §1 before the central question. Its prose states
  the common 1,400-unit compressed prefix and links the 100,000-raw-gap-per-stage
  source dataset without implying that all sampled gaps appear in the display.
- Two reproducible charts are ready for §8.1. Across 188 fully covered
  per-sequence windows through head 1129, the empirical/random 2-gap count ratio
  averages 0.967 and ends at 0.947. Across 187 distinct measured transitions
  through filter 19429, 186 lie below the random destruction rate `2/p`, 95
  destroy no local 2-gap, and the maximum observed `w_p` from `p >= 1000` is
  0.0523.
- Both charts measure changing square windows. They do not follow one fixed
  cohort toward a head and therefore cannot establish the cumulative head
  hazard, persistent availability, mixing, or the `c=1/2` head frontier.
- The current draft is 2,711 lines and contains Appendix A.1--A.6 for global
  persistence, cumulative local hazard, fixed-factor survival, logarithmic
  worsening, the adversarial/random square-window boundary, and the local
  survivor allocation range. All six body citations resolve to explicit
  internal anchors.
- Mathematical citations now resolve only within the current article or to the
  published `articles/chapter6/gap-dynamics.md`. Links to companion, property,
  candidate, and learnings notes were removed from the article; generated
  figure assets remain as reproducibility evidence.
- `PROOF_GUIDE.md` now states the official authority hierarchy: an article may
  cite itself, one of its appendices, or another published article for
  mathematics. Repository files remain valid only as implementation,
  verification, calculation, data, or generation evidence.
- `PROOF_GUIDE.md` now requires English before mathematics for every property,
  documents the mathematical-draft exception, uses green-to-green
  chapter-by-chapter verification, and distinguishes matching the publication
  voice from merely copying its outline.
- The guide now preserves the durable editorial lessons from this draft:
  contribution-led abstracts, concrete examples before unfamiliar notation,
  one mathematical idea per subsection, concise comparison tables, direct
  language, and research protocols outside the proof narrative.
- Its title, author block, abstract, introduction, model definition, allocation
  mechanisms, conclusion, and future work follow the teaching voice and
  structure of the first four finished articles rather than the former
  research-protocol voice.
- The article opens with the construction before the hazard notation, includes
  a concrete `r=5` example, explains each main property before its mathematics,
  and uses concise tables for model and allocation comparisons. The large
  experiment grid and per-transition checklist were replaced by the essential
  comparison tuple and cumulative measurements.
- The final editorial audit found nineteen proof-completion markers across the
  body and appendices, one article-wide
  `not Stainless-verified` statement, balanced Markdown fences, resolving
  local links, no legacy sister/shot/optimistic vocabulary, no unsupported
  LaTeX, no article-to-ticket references, and a clean `git diff --check`.
- The active location is the main project folder on
  `feature/evaluate_candidates`; the former secondary worktree no longer
  exists and must not be used.
- The publication-style refactor is complete in the main project folder. The
  article now has twelve numbered chapters, preliminaries before results,
  thirteen body proof completions, six appendix proof records, compact
  mechanism labels,
  limitations, a conditional real-CRT transfer conclusion, future work, and
  references. Both phase-transition charts and all twelve mathematical results
  were preserved.
- The first refactor left a research-summary-sized and overly defensive
  abstract. It is now a 160-word contribution-led abstract: construction,
  cumulative-hazard/frontier result, and allocation/CRT significance. Scope is
  carried by one short companion-model qualifier, followed by the explicit
  conditional implication for the real sieve and the twin-prime conjecture.
- The article no longer uses good/bad sister terminology. It now distinguishes
  an allocator, which assigns policies to parents, from random, adversarial,
  and protective parents, whose policies choose exactly two harmful child
  indices. Headings, tables, prose, and mathematical superscripts use the same
  terminology.
- Related material exists in the balanced randomized and balanced adversarial
  candidate notes and in the mixture section of the realized adversariality
  score property.
- No dedicated article currently gives the mixed threshold high visibility.
- The ticket and draft article both exist in this worktree.
- The source audit invalidated the proposed constant-mixture headline. A
  per-filter adversarial share compounds once for every installed prime, so a
  fixed positive share is asymptotically fatal to the local random baseline.
  The correction was surfaced explicitly and the user confirmed that the
  corrected phase-transition draft should proceed.
- The draft article now exists at
  `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md`.
  Its source links and framing were audited, and `git diff --check` passes.
  The user-requested review addition is complete: §10.1 now makes the maximum
  fixed percentage and practical decaying percentage boundaries explicit,
  with representative values and cumulative-budget caveats.
- The user has now requested the full missing bad/good and allocation chapters.
  The expansion is complete. The 1,533-line draft now covers bad/random,
  bad/good, exact allocation bounds, assignment mechanisms, a targeting score,
  realized local hazard, and a two-axis experimental program. Final source,
  framing, numbering, comparison-format, and whitespace audits pass.
- The user correctly identified that a fixed absolute bad share is a trivial
  comparison because the random benchmark `2/r` shrinks. The revision is now
  implemented: `f_r`, `w_r`, and `D(Q)` are primary throughout the abstract,
  early theory, phase summary, practical interpretation, experiments,
  real-sieve comparison, and conclusion. Absolute-share results remain
  explicitly labeled specializations.
- The draft now contains ten uniquely numbered theorem-shaped properties. The
  new results show that every fixed finite factor `w` survives the stipulated
  model, while `w_r=1+c log(r)` has square-window threshold `c=1` and head
  threshold `c=1/2`, subject to the stated spatial and mixing premises.
- The final audit passes: 1,928 lines, balanced Markdown fences, ten unique
  property numbers, explicit evidence status, existing source-link targets, no
  article-to-ticket references, no emoji, consistent phase thresholds, and a
  clean `git diff --check`. Runtime gates are not applicable to this
  Markdown-only change.
- The user requested one further synthesis: retain the real CRT number of
  accepted filter shots but allocate their locations uniformly at random
  without replacement. This will become Property XI. Its head conclusion must
  be probability-one under explicit availability and cross-layer mixing, not
  a deterministic conclusion and not a claim about real CRT locations.
- Property XI is complete and surfaced throughout the article. The 2,148-line
  draft now has eleven unique properties and 256 balanced fences. It records
  the exact without-replacement factor, cumulative quota conditions,
  probability-one head recurrence with mixing, the stronger eventual-window
  result, experiment metrics, and the distinction between quota `J_r`, local
  maintained count `A(p,q)`, and adversarial hazard `A(Q)`. Final framing,
  link, overclaim, ticket-reference, emoji, numbering, and whitespace audits
  pass.
- The user requested the proportional bad-sister extension of Property XI:
  keep the exact quota but favor 2-gap endpoints. Property XII must distinguish
  raw endpoint weight from effective destruction skew, prove that every fixed
  finite effective skew retains head recurrence with mixing, and recover the
  logarithmic coefficient frontiers `c=1/2` for the head and `c=1` for square
  windows.
- Property XII is complete and fully surfaced. The 2,427-line draft now has
  twelve unique properties and 296 balanced fences. It distinguishes raw
  endpoint weight `beta_r` from quota-normalized effective skew `kappa_r`,
  proves survival for every fixed finite effective skew, derives the robust
  head coefficient `1/2` and square-window coefficient `1`, and makes the
  exact-equality lower-order caveat explicit. Final framing, numbering,
  evidence-status, overclaim, ticket-reference, emoji, fence, and whitespace
  audits pass.
- The draft now embeds both phase-transition charts: the square-window chart in
  §5.1 (Property III) and the head-recurrence chart in §5.2 (Property IV),
  each with lead-in prose following the chapter6 figure convention. The charts
  share a unified style, and their SVGs and generators were updated so the
  colored version is B&W-safe (boundary solid black in both, every other
  series a distinct dash pattern). `git diff --check` passes and fences remain
  balanced.

## Alternatives Considered

- Expand `learnings-capacity-argument.md`: rejected because the result would
  remain buried in an already long historical ledger.
- Expand only `realized-filter-adversariality-score.md`: rejected because that
  note's mixture is tied to a fixed anchored cohort and explicitly warns
  against extending it beyond its certification boundary.
- Present the result as a verified property: rejected because spatial
  uniformity and cross-layer mixing remain premises, not verified facts.

## Risks, Assumptions, And Hypotheses

- The safe-window conclusion assumes uniformly distributed surviving starts.
- The head conclusion additionally assumes independence or adequate weak
  mixing across layers.
- A constant adversarial fraction and a whole-filter adversarial coin are
  different models and must not be conflated.
- A global bad percentage does not determine local harm. Which parents receive
  bad labels can change the outcome from full protection to total local
  extinction, so allocation must be modeled separately.
- The model concerns 2-gap descendants, not a coherent randomized integer
  sieve and not the real deterministic sieve.
- The asymptotic constant in the 2-gap density is positive but need not be
  numerically fixed for the threshold argument.

## Validation Plan

- Re-derive every displayed formula from the definitions in the source notes.
- Check that fixed `alpha < 1`, varying `alpha_Q`, safe-window, and head claims
  use the correct quantifiers and probability assumptions.
- Cross-reference the draft against `PROOF_GUIDE.md` and finished article
  structure, while marking conditional/unverified claims explicitly.
- Run Markdown searches for overclaims such as unconditional `proved`, claims
  about the real sieve, or conflation of global and local extinction.
- Runtime validation is not required because the change is Markdown-only and
  does not alter executable instructions.

## What is Learned

- The exact `c=1` square-window curve is a slowly declining failure-side
  boundary, not a surviving curve. When a rasterizer renders an SVG
  unreliably, validate both the visible annotation and the underlying plotted
  elements before judging the asset.
- A product of positive transition factors proves persistence only from a
  positive initial population. When a proof is repeated in the body and an
  appendix record, both copies must state that seed premise.
- “Unconditional” must name the axis being varied: this theorem is independent
  of allocation, while still requiring a nonempty initial population.
- A decreasing relevant fraction need not approach zero. An eventual capacity
  claim requires either `L/N -> 0` or the eventual inequality
  `L/N <= alpha` itself.
- When an asymptotic theorem is restated in an appendix, its limiting premise
  must be preserved rather than weakened to a qualitative trend.
- An exact strike count is a one-layer constraint; matching a cumulative
  frontier additionally requires cumulative rate/error control and the
  relevant spatial premises.
- Summary framing must distinguish the neutral quota result from the biased
  effective-skew result; they recover related scales under different premises.
- From `articles/draft/`, repository chart assets resolve through
  `../../charts/`; retired presentation-output paths are not stable sources.
- Divergence of marginal head probabilities is insufficient by itself; the
  recurrence step needs explicit control of joint events, such as the stated
  intersection-sum condition.
- A deterministic arithmetic sequence does not literally have stochastic
  head events. Its transfer premise must compare actual counts with reference
  weights through a discrepancy bound.
- Authoritative external sources selected for the remaining classical steps
  are Kochen and Stone (1964), DOI `10.1215/ijm/1256059668`, and Hardy and
  Wright's sixth edition, OUP DOI `10.1093/oso/9780199219858.001.0001`.
- An appendix containing selected proof records must say so explicitly; its
  heading must not imply that omitted body theorems lack proof records or that
  the selection is exhaustive.
- Verification metadata should not dominate an article whose contribution is
  mathematical and whose machine encoding is outside scope; one scope sentence
  is enough.
- An explicit verification boundary can be one sentence; it does not need to
  become a per-result catalog when no machine implementation is presented.
- An impersonal abstract can remain direct by making the article or the
  mathematical quantity the grammatical subject rather than adding passive
  filler.
- Impersonal academic voice does not require indirect prose: explicit subjects
  preserve clarity while removing author-centered phrasing.
- Publication review must combine logical-premise checks with asset, link,
  source, and verification-status audits; any one of those alone can miss a
  print-breaking or claim-breaking defect.

- A zero-prior-knowledge introduction cannot open with ambiguity inside the
  phrase “2-gap survival.” It must first establish what survives, what a gap is,
  and why the value 2 is the article's distinguished case.
- The published foundation supplies a clean explanatory order: prime filters
  produce periodic survivor sequences; adjacent differences produce gaps;
  distance 2 is the smallest post-filter-2 gap; square-window certification
  connects surviving 2-gaps to twin primes and eventual head 2-gaps.
- Introducing the stage head `Q` before the square-safe window makes the
  least-prime-divisor certification self-contained for a new reader.
- Self-containment is stronger than link correctness: the article must remain
  intelligible and complete after all repository navigation is removed, as if
  the Markdown were printed and mailed by itself.
- The four-part audit—context, challenge, work, conclusion—is now a shared
  publication standard rather than a one-off repair for this draft.
- Self-containment and scholarly provenance are complementary. The article must
  restate enough to stand alone while still naming and citing the prior source
  that introduced and formally verified the reused mathematical object.
- The reusable editorial pattern is define first, cite second: the printed text
  carries the meaning, while the citation carries provenance and the full
  earlier development.
- Publication-style references require both halves of the convention: anchored,
  numbered bibliography entries and matching numbered markers at the relevant
  body citations. Bare bullets match neither the visual style nor navigation of
  the finished articles.
- A subsection-level citation can cover an immediately following list of
  results from the same source; repeating `[[2]]` on all three §2.2 bullets
  would add visual noise without improving provenance.
- The finished-series reference style is now restored end to end: source claims
  navigate to numbered bibliography anchors, while each bibliography entry
  carries full author/year/title metadata and a resolving article link.
- At the exact relative-factor boundary `c=1`, quadratic supply cancels the
  `Q^{-2}` hazard term but the residual `(log Q)^{-2}` remains, so expected
  occupancy tends to zero. It is a boundary curve on the failure side, not a
  slow surviving curve.
- A monotone decrease of `L/N` need not cross a fixed `alpha`; the valid
  condition is `L/N <= alpha` eventually, with `L/N -> 0` as a convenient
  sufficient hypothesis.
- “Adequate mixing” is not a mathematical premise until a second-
  Borel–Cantelli correlation condition is stated. Deterministic transfer needs
  its own indicator-versus-predicted-weight discrepancy condition rather than
  stochastic terminology alone.
- An introductory empirical figure needs a local reading key and evidence
  boundary: rows are real Sieve Sequence stages, green cells are 2-gaps, colored
  cells collapse the non-2 distance to the next 2-gap, and the texture motivates
  the placement challenge without proving a survival frontier.
- The precise encoding is slightly subtler at row boundaries: every maximal
  non-2 run becomes one colored cell, while only an internal colored cell lies
  between two displayed 2-gaps. The chart preserves every 2-gap only inside its
  common displayed prefix, not across all 100,000 sampled raw gaps.
- The random/adversarial mixture already has the one-step destruction rate
  `f_alpha(r) = alpha + (1-alpha) * 2/r` in equivalent score notation.
- The fixed-window compounding trajectory is not the growing-window process;
  the new article must keep them separate.
- Global persistence is deterministic for every mixture because every parent
  retains exactly `r-2` descendants.
- If `alpha_r` is the adversarial share at filter `r`, a locally relevant
  lineage has mixed survival factor
  `(1-alpha_r)(1-2/r)`. Therefore the growing-window expectation is the random
  baseline multiplied by `prod_{r<Q}(1-alpha_r)`, not merely by one final
  factor `1-alpha_Q`.
- For constant `alpha>0`, `(1-alpha)^{pi(Q)}` decays faster than the quadratic
  window grows, so the mixed local expectation tends to zero. The previous
  fixed-percentage conclusion had applied the mixture only once.
- The cumulative budget `A(Q)=sum_{r<Q}-log(1-alpha_r)` governs the phase
  transition. The square-window expectation is proportional to
  `Q^2 exp(-A(Q)) / log(Q)^2`.
- For `alpha_r ~ c log(r)/r`, the conditional safe-window threshold is `c=2`
  and the conditional head-recurrence threshold is `c=1`. The intermediate
  range `1<=c<2` separates window abundance from head recurrence.
- For `alpha_r ~ c/r`, both square-window abundance and the divergent
  head-occurrence series survive for every fixed finite `c`, under the stated
  spatial/mixing premises.
- In practical percentage form, the maximum sustainable fixed per-filter share
  is `0%`; the asymptotic boundary curves are `200 log(r)/r %` for square
  windows and `100 log(r)/r %` for head recurrence, both requiring a strict
  margin and cumulative interpretation.
- For `N` total parents, `L` locally relevant parents, and `K` bad labels, the
  exact local survivor bounds are `max(0,L-K)` when targeted,
  `L(1-K/N)` in expectation when uniform, and `min(L,N-K)` when protective.
- The balanced good sister can preserve one target child while still removing
  exactly two copies because `r>=5` leaves at least four non-target choices.
- Under bad/good position-blind mixing, a fixed cohort has binomial survival
  probability `exp(-A(Q))`; growing protective square supply has expectation
  `C_0 Q^2 exp(-A(Q))`.
- For `alpha_r ~ c log(r)/r`, bad/good square windows have the leading `c=2`
  threshold and bad/good head recurrence includes `c=1` under protective
  availability and adequate mixing. Bad/random head recurrence excludes it.
- Percentage and allocation are separate axes. The normalized targeting score
  compares realized hits with protective, uniform, and targeted endpoints;
  realized local hazard can greatly exceed the global bad share.
- If `f_r=(2/r)w_r`, every fixed finite `w_r=w` gives cumulative survival of
  order `1/log(Q)^(2w)`, so quadratic windows grow and the prime-head occurrence
  series diverges under mixing.
- If `w_r ~ c log(r)`, the robust square-window regime is `c<1` and the robust
  head-recurrence regime is `c<1/2`; boundary cases depend on lower-order
  logarithmic factors.

## Failed Paths

- **Indefinitely extending one fixed-window projection.** This fails because a
  fixed window stops receiving filters after its certification boundary. Retry
  only for a genuinely growing family of windows indexed by `Q`.
- **Calling the companion a random sieve sequence.** This fails because it does
  not construct a coherent survivor sequence or preserve cross-gap CRT
  correlations. Retry only if a full constrained random integer process is
  defined.
- **Treating a repeated constant adversarial share as one final dilution.** The
  calculation `lambda_Q^(alpha)=(1-alpha)lambda_Q` omits one factor
  `1-alpha` for every earlier filter. Under a per-filter mixture the correct
  factor is `prod_{r<Q}(1-alpha_r)`; for constant positive `alpha` this drives
  the local expectation to zero. Retry the one-factor formula only for a model
  that explicitly makes a single mixture decision after all random filtering.
- **Final ticket update against stale patch context.** The first update failed
  because its expected lines did not match the ticket's wrapped current text;
  no file changed. It succeeded after rereading the exact target. Retry direct
  context patches only after refreshing the target when earlier edits may have
  changed line wrapping.
- **Broad precision patch against stale article context.** One final precision
  patch made no change because a paragraph's wrapping differed from the
  expected context. The same scoped corrections succeeded after reading the
  exact snippets. Future multi-location prose patches should refresh all
  contexts immediately before application.
- **Experiment reframing patch against one stale wrapped paragraph.** The
  first multi-hunk patch made no change because one §18 paragraph differed at
  its line wrap. The same semantic edit succeeded after rereading and applying
  exact localized hunks.
- **Conclusion and framing patches against stale context.** Each first attempt
  made no change because the expected text differed from the current article;
  exact-context retries succeeded. These were separate micro-goals and neither
  exceeded the stop-and-ask threshold.
- **Link audit from the wrong directory and zsh `path` shadowing.** The first
  read-only link check used repository-relative paths from `articles/`, and a
  later loop variable named `path` temporarily hid executables in that shell.
  Neither changed files. The audit succeeded from the worktree root using a
  non-special loop variable.
- **Raw JavaScript template for a Markdown-fence patch.** The correction did
  not execute because backtick fences terminated the JavaScript template. No
  file changed. Ordinary escaped strings succeeded; do not embed fenced
  Markdown in a raw backtick template.
- **Property-XI framing patch against a mid-line abstract anchor.** The first
  multi-hunk framing patch made no change because its expected abstract
  sentence began midway through the real line. Exact local anchors succeeded
  on retry.
- **Reading the deleted secondary worktree.** The initial audit targeted the
  former Claude worktree, which no longer existed, so the process was rejected
  before reading or changing a file. The task resumed from the authoritative
  main project folder on `feature/evaluate_candidates`.
- **Editorial patches against stale wrapped sentences.** The first redundant-
  disclaimer removal and Future Work insertion each made no change because one
  expected paragraph had different wrapping. Both succeeded after rereading
  the exact current context; no partial article edit occurred.
- **Global-persistence patch with incomplete LaTeX context.** The first patch
  was an atomic no-op because its expected proof label omitted one ampersand.
  Rereading the exact lines and retrying the same scoped change succeeded.

## Open Concerns

- Spatial uniformity, protective quadratic supply, protective head availability,
  and cross-layer mixing remain premises rather than real-sieve theorems.
- The exact-quota, delayed, block-balanced, and noisy-ranking experiments are
  designed in the article but not implemented.
- No Scala/Stainless representation encodes the new stochastic or asymptotic
  properties.
- Transferring either cumulative budget or targeting-score bounds to the real
  CRT-coupled filter remains open.

## Next Action

Done — return the impersonal abstract for user review.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-11 | Existing notes contain the ingredients, but no dedicated growing-window mixture article. | Created this ticket and scoped a synthesis draft rather than a new theorem. |
| 2026-08-11 | A per-filter adversarial fraction compounds over all primes; the earlier one-factor dilution was a category error. | Stopped before drafting, recorded the failed path, and reframed the candidate around a decaying-adversariality phase threshold. |
| 2026-08-11 | The user approved proceeding with the corrected phase-transition article. | Resumed with one draft article as the next micro-goal. |
| 2026-08-11 | The corrected article derives the cumulative budget and the distinct `c=2` safe-window and `c=1` head thresholds without claiming transfer to the real sieve. | Created and audited the 657-line draft; left surrounding indexes unchanged pending review. |
| 2026-08-11 | A final ticket patch used stale context and made no change. | Re-read the ticket, corrected the context, and recorded the mechanical failure to prevent repetition. |
| 2026-08-11 | The phase diagram contains the result but does not yet state it in practical percentage language. | Began one requested subsection making the maximum fixed and decaying percentages explicit. |
| 2026-08-11 | The practical maximum is now explicit without treating pointwise boundary values as resettable allowances. | Added and audited §10.1, including four representative filter-prime rows. |
| 2026-08-11 | Percentage alone is insufficient: parent allocation and targeting knowledge are a second axis. | Expanded the requested article scope to the complete bad/good allocation analysis. |
| 2026-08-11 | The complete article now separates bad budget, allocation, protective supply, and targeting information across eight theorem-shaped properties and a reproducible experiment design. | Added §§12–18, broadened the framing, revised limitations/conclusion, and completed all Markdown audits. |
| 2026-08-12 | Fixed absolute bad share is a trivial floor; the meaningful quantity is realized destruction divided by the shrinking random rate `2/r`. | Reopened the draft for a relative-to-random reframing while retaining absolute-share results as special cases. |
| 2026-08-12 | There is no finite constant-factor maximum worse than random; the nontrivial window/head thresholds appear when the factor grows logarithmically. | Added the general hazard law, fixed-factor theorem, logarithmic thresholds, relative phase table, and aligned all principal framing and experiment sections. |
| 2026-08-12 | Total local destruction and bad-label hits coincide for bad/good but not for bad/random, which also contains the random baseline. | Split experiment observables into bad-label hits `H`, total target destruction `T`, relative damage `w`, and targeting `theta`. |
| 2026-08-12 | The completed relative-hazard framing is internally consistent and all linked evidence exists. | Finished the formula, status, numbering, link, overclaim, ticket-reference, emoji, fence, and whitespace audits; marked the draft ready for review. |
| 2026-08-12 | Exact CRT shot counts and random shot locations define a sharper sister than independent Bernoulli deletion. Exact quotas preserve the one-point survival asymptotic, but infinitely many head hits still require availability and cross-layer mixing. | Reopened the draft for a separately scoped Property XI with explicit without-replacement and evidence-status premises. |
| 2026-08-12 | Uniform without-replacement allocation gives the exact pair-survival factor `choose(N-2,J)/choose(N,J)`; CRT-rate cumulative quotas recover `1/log(Q)^2`, whose prime-head series diverges. | Added Property XI, surfaced it throughout the framing and experiment program, separated quota notation from existing hazards, and completed all Markdown audits. |
| 2026-08-12 | The neutral exact-quota model and the earlier relative-hazard model predict the same skew frontier. Raw preference weights require quota normalization, but effective skew has head coefficient `1/2` and square-window coefficient `1`. | Reopened the draft for Property XII, with the exact boundary and lower-order caveat explicitly scoped. |
| 2026-08-12 | The biased exact-quota derivation independently recovers the earlier relative-hazard frontier: all fixed finite skew survives, while logarithmic effective skew separates head recurrence at coefficient `1/2` from square-window occupancy at coefficient `1`. | Added Property XII, aligned all principal framing and experiment sections, and completed the twelve-property Markdown audit. |
| 2026-08-12 | The two phase-transition charts (window: fixed factors survive + c=1 frontier; head: c=1/2 Borel-Cantelli sum) now render with a unified style and B&W-safe dash patterns. | Added the window chart to §5.1 (Property III) and the head chart to §5.2 (Property IV) with lead-in prose, following the chapter6 figure-embed convention. |
| 2026-08-12 | A detailed research analysis can match the publication series without discarding its depth when recurring notation precedes results, theorem evidence is standardized, related properties share chapters, and mechanism catalogs do not dominate the table of contents. | Refactored the current 2,450-line source in place into twelve chapters, preserved both charts and every result, restored the explicit conditional real-CRT transfer conclusion, and passed structure, link, fence, comparison, emoji, ticket-reference, and whitespace audits. |
| 2026-08-12 | Structural conformity is not sufficient if the abstract still reproduces secondary models, formulas, experiments, and allocation details. | Replaced the roughly 450-word abstract with a 160-word statement of the invariant, principal frontiers, allocation insight, and real-sieve limitation. |
| 2026-08-12 | “Good sister” and “bad sister” obscure the actual sampling unit: the allocator selects parents, and each selected parent policy chooses two harmful child indices. | Replaced the informal vocabulary with random, adversarial, and protective parents throughout headings, prose, tables, and formulas; verified that no legacy term remains in the article. |
| 2026-08-12 | “Protective” is more precise than “optimistic”: it names the policy's observable action of moving deletions away from the target rather than an analytical attitude. | Replaced optimistic parent with protective parent throughout the article and ticket, including prose, headings, tables, and mathematical identifiers. |
| 2026-08-12 | An abstract can be concise yet still undersell the work if its final paragraph is dominated by non-results. | Reframed the abstract around the constructed process, exact hazard law, sharp logarithmic frontiers, allocation theorem, and CRT comparison; retained only one compact scope qualifier. |
| 2026-08-12 | The practical significance is stronger than “a frontier for comparison”: random-like real filtering, or adversarially biased filtering below the head-survival frontier with the required availability and mixing, implies infinitely recurring head 2-gaps. | Stated the conditional twin-prime implication directly in the abstract while keeping it at 160 words. |
| 2026-08-12 | The alternation examples retained an undefined `O` from the former optimistic-parent terminology. | Defined `P` as protective parent and `A` as adversarial parent before first use, then updated both alternation and cyclic-mask patterns. |
| 2026-08-12 | `VOCABULARY.md` treats shot and strike as synonyms but prefers accepted strike and harmful strike in algebraic arguments; the draft mixed both terms. | Removed all 22 shot occurrences from the draft, using strike generally, accepted strike for values surviving earlier filters, harmful strike for endpoint damage, and `struck` as the endpoint participle. |
| 2026-08-12 | The article introduced reusable distinctions not yet captured by the shared vocabulary: parent policies versus allocators, adversarial share versus targeting strength, and exact strike quota versus strike locations. | Extended `VOCABULARY.md` with preferred strike terminology, exact-count strike terms, random/adversarial/protective parent policies, allocator semantics, and the separation between parent-policy allocation and strike-set allocation. |
| 2026-08-12 | Structural compliance did not make the draft sound like the opening articles: the title and abstract began with derived jargon, the model lacked a concrete example, and the experiment section read as an execution protocol. | Reworked the front matter and model explanation, added the five-copy example, converted sampling and allocation mechanisms to explanatory tables, reduced the experiment checklist to its mathematical observables, removed research-note jargon, and repeated the full link, fence, vocabulary, LaTeX, and whitespace audits. |
| 2026-08-12 | `PROOF_GUIDE.md` captured first-person voice but still contradicted mandatory three-representation and chapter-regression rules, and did not explain how to preserve the series voice beyond structure. | Reopened the editorial task for a consistency and publication-voice update to the shared guide. |
| 2026-08-12 | Publication consistency requires both rule correctness and authorial continuity: prose-before-math, a compact contribution-led opening, concrete construction examples, and separation of theorem narrative from experiment protocol. | Updated `PROOF_GUIDE.md`, added the unverified mathematical-draft exception, corrected green-to-green verification commands, and passed the final documentation audit. |
| 2026-08-12 | The allocation theorem was correct but hid its simple capacity crossover behind set-intersection notation: a target-aware allocator clears a tracked window exactly when `K >= L`, equivalently `alpha >= L/N`. | Rewrote §5.1 to lead with the crossover, then derive the sharp bounds, and explicitly separated immediate head suppression, later sparse-window wipeout, and continued complete-period growth. |
| 2026-08-12 | Official articles should not outsource mathematical authority to internal property, companion, candidate, or learnings notes. Mathematics belongs in the article, an appendix, or another published article; repository artifacts may support code or calculations. | Added Appendix A.1--A.6, redirected all companion theorem citations internally, cited the published Gap Dynamics article for prior sieve results, removed working-note references, and codified the authority hierarchy in `PROOF_GUIDE.md`. |
| 2026-08-12 | The supplied charts measure two compatible square-window observables but not one fixed head lineage: per-sequence population tracks random, while one-step destruction is below random. | Added §8.1 with both charts, exact finite summaries, calculation/data evidence links, the explanation reconciling the two views, and explicit exclusion of a cumulative `c=1/2` head inference; surfaced the result in §9 and §10. |
| 2026-08-14 | The introduction invokes “2-gap survival” before telling a new reader what the gaps are gaps between or why 2 is special. | Reopened only the introduction's opening for a zero-prior-knowledge rewrite grounded in the published gap definitions. |
| 2026-08-14 | Gap Dynamics confirms the complete foundation needed by the rewrite: filtered survivors, adjacent differences, minimal gap 2, square-window prime certification, and eventual first-gap placement at a matching head. | Fixed the article-edit micro-goal to three introductory paragraphs followed by the existing three-way distinction. |
| 2026-08-14 | The zero-prior-knowledge order is now explicit, and “first gap after the head” is the precise object—not “the head is a gap.” | Rewrote §1's opening, preserved the later scope and contribution summary, and passed scoped review plus `git diff --check`. |
| 2026-08-14 | An article is not self-contained merely because its links resolve: a print-only reader must understand its context, challenge, work, and conclusion without the repository. | Made print-only self-containment the governing review test and selected the shared proof guide as the durable home for the rule. |
| 2026-08-14 | The print-only test must govern all articles, not live only in one active ticket. | Added the four-part rule and repository-link boundary to `PROOF_GUIDE.md` and promoted the concise lesson to `LEARNINGS.md` §14.20. |
| 2026-08-14 | The self-contained rewrite explains the object but currently omits attribution to the earlier article that introduced and verified the Sieve Sequence. | Scoped one provenance sentence and matching reference entry without outsourcing the definition to that citation. |
| 2026-08-14 | Self-containment does not replace provenance; the strongest introduction defines the Sieve Sequence locally and then cites its earlier formal development. | Added the inline attribution and matching §12 reference, verified the target, and passed `git diff --check`. |
| 2026-08-14 | The non-staggered 2-focused heatmap can visually bridge the three survival scales to the local-placement challenge if its encoding and empirical status are explicit. | User approved adding it to the introduction; scoped one figure insertion with a self-contained reading key and threshold-evidence caveat. |
| 2026-08-14 | The heatmap shows a common 1,400-unit compressed prefix, not all 100,000 sampled raw gaps; maximal non-2 boundary runs also become colored cells. | Added the corrected figure explanation, empirical-only caveat, generator and data provenance, verified every target, and passed `git diff --check`. |
| 2026-08-14 | The draft's two bare reference bullets do not match the numbered anchored bibliography and body-marker convention used by the finished articles. | Scoped the bibliography conversion first and the matching body citations as a separate checked edit. |
| 2026-08-14 | §12 now matches the finished bibliography style with unique `ref1`/`ref2` anchors, exact titles, and resolving local links. | Kept body-marker normalization separate and scoped it to one Sieve Sequence citation plus six section-level Gap Dynamics citations. |
| 2026-08-14 | The article now matches the finished-series reference convention end to end: one `ref1` marker, six section-level `ref2` markers, and two anchored full entries. | Verified counts, anchors, local targets, and both scoped and repository-wide Markdown diffs, then returned the draft to user review. |
| 2026-08-14 | Independent review found a concentrated set of repairable blockers rather than a failure of the central framework; most importantly, the exact `c=1` window curve tends to zero and cannot be called surviving. | Reopened the article for ordered green-to-green corrections, beginning with the article caption before its generator and asset. |
| 2026-08-14 | §3.4 now agrees with its own asymptotic formula: exact `c=1` is a slowly declining failure-boundary curve, not the slowest surviving curve. | Passed scoped and repository-wide Markdown checks and moved the next isolated correction to the chart generator text. |
| 2026-08-14 | The chart generator now describes exact `c=1` as a logarithmically slow decline to zero, and all 249 Python tests pass. | Kept asset regeneration separate and scoped the next action to the single window SVG. |
| 2026-08-14 | The regenerated window SVG now labels exact `c=1` as a slowly declining failure-side boundary; all six polylines remain structurally intact. | Validated the asset alongside the green 249/249 Python suite and moved to the missing `N_0>0` proof premise. |
| 2026-08-14 | Global persistence requires a positive initial 2-gap population in addition to positive transition factors. | Added `N_0>0` to §3.1 and scoped the matching Appendix A.1 correction next. |
| 2026-08-14 | The global theorem is unconditional only along the allocation axis once `N_0>0` is assumed. | Mirrored the seed premise in Appendix A.1 and qualified its opening claim. |
| 2026-08-14 | Merely decreasing `L/N` does not ensure that every fixed positive share crosses it. | Required `L/N -> 0` in §5.1 and scoped the matching Appendix A.6 correction next. |
| 2026-08-14 | The capacity crossover needs the same limiting premise in its body proof and appendix record. | Updated Appendix A.6 to require `L/N -> 0` and moved to exact-quota framing. |
| 2026-08-14 | Exact quota preservation at one layer does not by itself determine an asymptotic frontier. | Qualified the abstract by the spatial and cumulative §7.1 premises and moved to the matching conclusion correction. |
| 2026-08-14 | Neutral exact quotas and biased exact quotas reach related frontiers through different hypotheses. | Made the conclusion premise-complete and moved to the first stale image link. |
| 2026-08-14 | The first stale figure was an obsolete presentation-output path, not a missing asset. | Pointed the head-transition figure to `charts/phase-transition-head.svg` and scoped the next link. |
| 2026-08-14 | The per-sequence frontier asset also already existed under `charts/`. | Repaired its article path and scoped the per-transition comparison link next. |
| 2026-08-14 | The per-transition frontier comparison was the third obsolete presentation path. | Pointed it to `charts/frontier-comparison-stages.svg` and scoped the destruction chart next. |
| 2026-08-14 | The full-cycle destruction asset was present under `charts/`. | Repaired its article path and scoped the final stale survival-chart link. |
| 2026-08-14 | All five reviewed figure failures were stale paths to assets already present under `charts/`. | Repaired the final survival-chart path and moved to formalizing the mixing premise. |
| 2026-08-14 | A divergent head-event sum becomes almost-sure recurrence only with explicit joint-event control. | Defined adequate cross-layer mixing by a Kochen--Stone sufficient condition and moved to deterministic transfer. |
| 2026-08-14 | Stochastic mixing and deterministic transfer are different kinds of premises. | Replaced the vague real-sieve mixing implication with an explicit count-discrepancy criterion and scoped the §8 alignment next. |
| 2026-08-14 | The real-sieve transfer checklist must use the deterministic criterion, not stochastic event language. | Aligned §8 with §10 and scoped the abstract's final implication next. |
| 2026-08-14 | The abstract must use the same deterministic transfer premise as §10. | Aligned it and selected authoritative probability and number-theory sources for the remaining citations. |
| 2026-08-14 | The Kochen--Stone sufficient condition now has an authoritative bibliography entry. | Added numbered reference [3] and scoped its body marker separately. |
| 2026-08-14 | The probability theorem now has a matching inline marker and anchored source. | Linked §2.1 to [3] and scoped the classical number-theory bibliography entry next. |
| 2026-08-14 | The classical prime asymptotics now have an official external bibliography source. | Added Hardy--Wright as [4] and scoped one section-level body marker. |
| 2026-08-14 | The PNT, prime harmonic, weighted prime-sum, and Borel--Cantelli steps now have anchored external sources. | Completed the citation markers and moved to correcting the appendix's scope label. |
| 2026-08-14 | Appendix A contains six selected records rather than every body theorem. | Renamed and reworded it honestly, then scoped explicit per-result verification status. |
| 2026-08-14 | A general draft disclaimer did not make each theorem's verification boundary explicit. | Added an eighteen-row per-result status table and moved to final audits. |
| 2026-08-14 | The repaired article passes structural, source, asset, and Python regression gates. | Recorded 41/41 resolving links, 15/15 resolving anchors, 372 balanced fences, clean whitespace, successful import, and 249/249 tests; returned it for review. |
| 2026-08-14 | The article has no Scala/Stainless implementation, so an eighteen-row tooling-status table distracts from the mathematics. | Reopened the draft to replace that apparatus with one scope sentence. |
| 2026-08-14 | The repository requires the pending verification boundary to remain explicit, but it need not dominate the article. | Removed the full status table and retained one compact §1.1 sentence. |
| 2026-08-14 | The abstract's only first-person language is concentrated in two clauses. | Reopened the draft for a narrowly scoped impersonal-voice edit. |
| 2026-08-14 | Direct subject-led constructions make the abstract impersonal without making it vague. | Replaced both first-person clauses, preserved all claims, and passed scoped whitespace checks. |
