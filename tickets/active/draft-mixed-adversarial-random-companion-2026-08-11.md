# Draft Mixed Adversarial/Random 2-Gap Companion Article

## START HERE

The finite real-versus-random comparison is integrated into §8.1, §9, and the
conclusion. The next action is user review.

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

The self-contained publication-voice draft and shared guide update are ready
for user review. Further work should be a separately scoped mathematical
correction, promotion decision, experiment implementation, or Stainless model;
no Stainless result is implied by this documentation-only refactor.

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
