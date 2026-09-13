# Survival Frontiers — correctness and article revision

## START HERE

Review and revise `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md` into a coherent mathematical article without overstating its proof status.

## Goal

Deliver a deep review of correctness, impact, structure, flow, and clarity, and implement justified article improvements. Distinguish finite identities, conditional probability theorems, empirical observations, and open real-sieve transfer obligations.

## Strategy

Audit the arguments against definitions and sources before editing. Use independent Critic and Monitor reviews under AGENTS.md. Make focused Markdown changes; preserve unrelated work. Prefer a coherent mathematical exposition over cosmetic promotion from the draft folder. No Scala changes are planned; absent Stainless proofs remain explicitly pending.

Related work:
- [Companion model organization](companions-folder-properties-of-models-2026-08-12.md)
- [Earlier draft corrections](draft-articles-round2-fixes-2026-08-15.md)
- [Positional analysis](spectral-positional-filter-analysis-2026-08-18.md)
- [Previous review](../../articles/notes/review-draft-adversariality-phase-transition-2-gap-companions.md)

Validate mathematical assumptions by checking the actual models and rederiving implications; verify external mathematical attributions using primary sources where needed. Validate final Markdown links, math delimiters, claim consistency, and diff scope. Markdown-only changes require no runtime gates.

## Current State

User priority: repair the companion property files first, then propagate their
corrected assumptions and conclusions into related articles. Earlier article
corrections are retained; catalog notes still contain the old hazards,
critical-schedule, and independence errors. The exact-quota catalog also
incorrectly groups global quota sampling with exact-two-per-parent balance.

The mathematical audit corrected the main claim-scope defects in the draft. The article now distinguishes conditional lineage hazards from observed fixed-cohort fractions; uses exact eventual schedules for critical boundaries; states the protective complement and the full-history independence needed for binomial claims; corrects the exact-quota endpoint density; and treats the real-sieve discrepancy relation as an unproved sufficient counting criterion. The property catalog now carries the same conditions and distinguishes global fixed-quota sampling from the balanced per-parent recurrence. The draft's abstract, model definition, and quota section state that exact quota is a separate conditional random-location experiment. Markdown post-checks passed. The remaining work is editorial consolidation, link repair, and a final publication-status decision.

Pre-existing modifications: `articles/chapter6/gap-dynamics.md`, `properties/sieve-sequence/README.md`, and `tickets/active/gap-dynamics-arxiv-latex-completion-2026-09-12.md`.

## What is Learned

- The current draft already states a blind-placement empty-window bound and a Kochen–Stone mixing premise; these must be audited as assumptions, not counted as proved model properties.
- The appendix repeats several body proofs. The distinction between realized finite-population fractions and conditional lineage probabilities needs particular scrutiny.
- The schedule $\alpha_r\sim c\log r/r$ does not decide critical cases. Exact eventual schedules, or equivalent bounded cumulative remainders, are required.
- Among accepted sieve survivors, 2-gap endpoint density is $\Theta(1/\log r)$, not $\Theta(1/(\log r)^2)$. A logarithmic raw quota preference can therefore change the leading effective-skew coefficient.
- Full-cycle identities explain a finite cohort deviation's origin but do not control its localization or make it harmless.

## Failed Paths

- Two broad `apply_patch` attempts failed because their context lines did not match the current document. They made no repository changes; narrower patches then applied the reviewed corrections. This is a tooling-context failure, not a failed mathematical path.
- The initial Monitor pre-gate misread a proposed replacement as a claim that the replacement was already present. A fresh, explicit pre-gate approved the unchanged proposed correction before execution.

## Open Concerns

- Expected population growth alone does not imply eventual almost-sure occupancy.
- A local realized fraction is not automatically a lineage survival probability.
- Exact-quota and independently balanced models have different dependence structures.
- Publication status must remain honest about pending Stainless verification.
- Empirical figures and citations may contain stale paths or claims.

## Next Action

The affected article and dated review now use the corrected taxonomy. Make a
final publication-status recommendation after any separately requested
structural edit; the manuscript remains a conditional draft with Stainless
verification pending. Internal section links in Survival Frontiers already
passed inspection.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-09-13 | User explicitly requests property-first corrections followed by article propagation. A global exact quota does not impose exactly two losses per parent. | Reordered the active work; retained prior article edits and assigned independent Critic/Monitor review. |
| 2026-09-13 | User requests substantive conversion, including correctness and impact. Draft and earlier reviews located; unrelated work identified. | Opened persistent review ticket and assigned independent read-only audits. |
| 2026-09-13 | Independent audits found invalid critical-boundary deductions from asymptotic equivalence, observed/probabilistic hazard conflation, unjustified binomial independence, and an eligible-density denominator error. Main empirical statistics were recomputed and confirmed by Monitor. | Applied the first semantic correction: conditional hazards distinguished from fixed-cohort observed fractions, explicit marginal hypotheses and nonlethal cutoff added. Remaining corrections are queued. |
| 2026-09-13 | Critical schedules, allocation hypotheses, exact-quota normalization, empirical notation, and real-sieve transfer language were corrected and reviewed. | Moved the manuscript from mathematically unsafe to a conditional companion-process article with explicit open transfer assumptions; began final editorial consolidation. |
| 2026-09-13 | The property-first audit found one residual spectrum overclaim and a model-scope mismatch: global exact quota is not two losses per parent. | Repaired the spectrum wording; updated the catalog, draft abstract, §2, and §7 to separate the conditional quota shuffle from the balanced $r-2$ recurrence. Independent Monitor post-check and `git diff --check` passed. |
| 2026-09-13 | A repository-wide article search found one directly affected historical review summary and no other article that grouped quota sampling with the balanced recurrence. | Corrected that review's taxonomy and obtained a second independent Markdown post-check. |
