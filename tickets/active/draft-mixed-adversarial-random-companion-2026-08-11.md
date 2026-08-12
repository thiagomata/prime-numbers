# Draft Mixed Adversarial/Random 2-Gap Companion Article

## START HERE

Extend the balanced 2-gap companion article with a biased exact-CRT-quota
sister. The next micro-goal is one theorem-shaped chapter deriving its
effective-skew frontier for square windows and head recurrence.

## Goal

Create an honestly framed draft article explaining how much adversarial local
filter behavior the balanced 2-gap companion can tolerate while retaining
safe-window and head 2-gaps. The article is complete when it clearly separates
unconditional global persistence from conditional spatial conclusions, derives
the constant-mixture and varying-mixture thresholds, distinguishes adversarial
amount from targeting ability, covers both bad/random and bad/good mixtures,
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
uniform, and optimistic bounds before presenting assignment mechanisms or
simulation proposals.

The primary parametrization is now the realized segment destruction fraction
`f_r` relative to the shrinking random benchmark `2/r`, namely
`w_r=f_r/(2/r)`. Absolute bad shares `alpha_r` are retained only as a
specialization. This directly answers how much worse than random the filter can
be without inserting a trivial positive destruction floor.

## Current State

- The worktree is on `worktree-idempotent-crunching-graham`; this task adds the
  untracked draft article and this active ticket.
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
  `L(1-K/N)` in expectation when uniform, and `min(L,N-K)` when optimistic.
- The balanced good sister can preserve one target child while still removing
  exactly two copies because `r>=5` leaves at least four non-target choices.
- Under bad/good position-blind mixing, a fixed cohort has binomial survival
  probability `exp(-A(Q))`; growing optimistic square supply has expectation
  `C_0 Q^2 exp(-A(Q))`.
- For `alpha_r ~ c log(r)/r`, bad/good square windows have the leading `c=2`
  threshold and bad/good head recurrence includes `c=1` under optimistic
  availability and adequate mixing. Bad/random head recurrence excludes it.
- Percentage and allocation are separate axes. The normalized targeting score
  compares realized hits with optimistic, uniform, and targeted endpoints;
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

## Open Concerns

- Spatial uniformity, optimistic quadratic supply, optimistic head availability,
  and cross-layer mixing remain premises rather than real-sieve theorems.
- The exact-quota, delayed, block-balanced, and noisy-ranking experiments are
  designed in the article but not implemented.
- No Scala/Stainless representation encodes the new stochastic or asymptotic
  properties.
- Transferring either cumulative budget or targeting-score bounds to the real
  CRT-coupled filter remains open.

## Next Action

The expanded draft is ready for user review. Further work is editorial or
experimental implementation only if requested; no Stainless result is implied
by this article-only extension.

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
| 2026-08-11 | The complete article now separates bad budget, allocation, optimistic supply, and targeting information across eight theorem-shaped properties and a reproducible experiment design. | Added §§12–18, broadened the framing, revised limitations/conclusion, and completed all Markdown audits. |
| 2026-08-12 | Fixed absolute bad share is a trivial floor; the meaningful quantity is realized destruction divided by the shrinking random rate `2/r`. | Reopened the draft for a relative-to-random reframing while retaining absolute-share results as special cases. |
| 2026-08-12 | There is no finite constant-factor maximum worse than random; the nontrivial window/head thresholds appear when the factor grows logarithmically. | Added the general hazard law, fixed-factor theorem, logarithmic thresholds, relative phase table, and aligned all principal framing and experiment sections. |
| 2026-08-12 | Total local destruction and bad-label hits coincide for bad/good but not for bad/random, which also contains the random baseline. | Split experiment observables into bad-label hits `H`, total target destruction `T`, relative damage `w`, and targeting `theta`. |
| 2026-08-12 | The completed relative-hazard framing is internally consistent and all linked evidence exists. | Finished the formula, status, numbering, link, overclaim, ticket-reference, emoji, fence, and whitespace audits; marked the draft ready for review. |
| 2026-08-12 | Exact CRT shot counts and random shot locations define a sharper sister than independent Bernoulli deletion. Exact quotas preserve the one-point survival asymptotic, but infinitely many head hits still require availability and cross-layer mixing. | Reopened the draft for a separately scoped Property XI with explicit without-replacement and evidence-status premises. |
| 2026-08-12 | Uniform without-replacement allocation gives the exact pair-survival factor `choose(N-2,J)/choose(N,J)`; CRT-rate cumulative quotas recover `1/log(Q)^2`, whose prime-head series diverges. | Added Property XI, surfaced it throughout the framing and experiment program, separated quota notation from existing hazards, and completed all Markdown audits. |
| 2026-08-12 | The neutral exact-quota model and the earlier relative-hazard model predict the same skew frontier. Raw preference weights require quota normalization, but effective skew has head coefficient `1/2` and square-window coefficient `1`. | Reopened the draft for Property XII, with the exact boundary and lower-order caveat explicitly scoped. |
| 2026-08-12 | The biased exact-quota derivation independently recovers the earlier relative-hazard frontier: all fixed finite skew survives, while logarithmic effective skew separates head recurrence at coefficient `1/2` from square-window occupancy at coefficient `1`. | Added Property XII, aligned all principal framing and experiment sections, and completed the twelve-property Markdown audit. |
