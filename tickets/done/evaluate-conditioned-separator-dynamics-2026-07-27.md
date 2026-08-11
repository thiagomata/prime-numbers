# Evaluate Conditioned 2-Gap Separator Dynamics

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete

**Related work:**

- `tickets/done/prove-capacity-floor-algebra-2026-07-27.md`
- `tickets/done/review-presentation-gap-csv-insights-2026-07-27.md`
- `tickets/done/analyze-capacity-density-candidates-2026-07-27.md`
- `candidates/redundant-close-pair-capacity.md`
- `candidates/balanced-spacers.md`

## START HERE

Formalize the true compressed separator between consecutive 2-gap starts,
recompute it independently on the fixed-future-window populations, and test
transition-level reconstruction hypotheses. Update candidates #18 and #7.
Create a new candidate only if a distinct, falsifiable reconstruction law
survives the data.

## Goal

Turn the presentation branch's 2-focused visualization idea into independently
defined candidate observables, empirical falsifiers, and sound algebraic
relationships without importing its chart labels or prefix assumptions.

## Strategy

1. Read `TICKET_DISCIPLINE.md`, the relevant `LEARNINGS.md` sections, related
   tickets, and all existing separator/matching properties.
2. Prove in candidate #18 that, for consecutive 2-gap starts,
   `R_i=x_{i+1}-x_i-2` and the close-pair condition is exactly
   `R_i<2r-4`.
3. Clarify candidate #7: prefix/local separator quantiles do not measure its
   complete-period cyclic maximum.
4. Recompute every separator from the fixed-window lineage populations over
   the existing 53 heads and 1,837 layers.
5. Measure threshold mass, normalized quantiles, maxima, destroyed starts,
   matching attrition, and newly qualifying/reconstructed edges.
6. Search for counterexamples before proposing a transition law.
7. Create candidate #19 only if the surviving law is not equivalent to #18's
   existing fixed-fraction or unbounded-matching forms.
8. Promote the two surviving attrition lemmas separately, one property per
   change: raw qualifying edges first, disjoint matchings second.

## Current State

- Candidate #18 already defines qualifying adjacent starts and proves a
  density-to-matching lower bound. It now includes the compressed separator
  definition and exact equivalence `P=#{i:R_i<2r-4}`.
- Candidate #7 concerns a complete-period cyclic maximum and is still
  unmeasured. It now explicitly states that local separator distributions and
  fixed prefixes do not measure its cyclic maximum.
- The presentation branch has a correct `compress_around_two` implementation,
  but its cluster-size line chart measures raw non-2 gaps rather than the
  compressed sums described by its prose.
- Separator distributions and transition reconstruction are independently
  measured. The strong monotone recurrences fail; the coefficient-2 raw and
  coefficient-1 matching attrition bounds survive.
- The full candidate/property/`.holds` search found no existing compressed
  separator theorem or transition matching-attrition theorem.
- A second targeted search before drafting the attrition theorem confirms the
  static matching property is the only related result; no deletion-bound
  theorem exists.
- No candidate #19 was created: the natural short-separator form duplicates
  #18, while the distinct monotone reconstruction forms are refuted.
- The independent sweep now covers 53 heads, 1,837 layers, and 1,784
  consecutive-layer transitions.

## What is Learned

- If `R_i` is the sum of the non-2 gaps after one 2-gap and before the next,
  then consecutive start separation is `R_i+2`.
- Therefore the existing qualifying-edge predicate should be exactly
  `R_i<2r-4`; this is a definition bridge, not an empirical conjecture.
- More explicitly, the first 2-gap moves from `x_i` to `x_i+2`, the intervening
  non-2 gaps sum to `R_i`, and the next start is
  `x_{i+1}=x_i+2+R_i`. Its enclosing length from `x_i` through
  `x_{i+1}+2` is `R_i+4`.
- Hand-pattern boundary checks pass for `[2,4,2]` at `r=5` and the strict
  equality case `[2,4,6,2]` at `r=7`.
- Both candidate edits pass Markdown and link checks; neither changes an
  empirical status beyond what has actually been measured.
- Local prefix statistics cannot establish a cyclic complete-period maximum.
- `P=count(R_i<2r-4)` and the retained/reconstructed/threshold-expanded edge
  decomposition have zero failures.
- The minimum measured short-separator mass is `0.307692`.
- Strong monotonic reconstruction is false: `P_next>=P_old` fails on 1,639
  transitions and `D_next>=D_old` fails on 1,685 transitions.
- Even `P_next>=P_old-H` fails on 385 transitions.
- The weaker bounds `P_next>=P_old-2H` and `D_next>=D_old-H` have zero
  failures and admit direct path-graph proofs.
- The raw attrition theorem now exists at
  `properties/sieve-sequence/filtering-attrition-bound-raw-close-pairs.md`.
  It passed 559,860 exhaustive finite subsequence cases, including its sharp
  coefficient-2 example.
- The matching attrition theorem now exists at
  `properties/sieve-sequence/filtering-attrition-bound-close-pair-matching.md`.
  It passed 559,860 exhaustive finite subsequence cases, including its sharp
  coefficient-1 example.
- The two attrition properties are cataloged as established properties 20 and
  21.
- Candidate #18 now includes the separator equivalence, both sharp attrition
  bounds, and the measured refutations of stronger monotone recurrences.
- The independent separator distributions, transition decomposition, raw
  totals, and recurrence falsifiers are promoted into
  `empirical/sieve-sequence/capacity-density-candidates.md`.
- The candidate catalog now states #7's local-versus-cyclic scope and #18's
  proved separator/attrition results plus refuted monotone forms.
- The unchanged repository-local lineage regression suite passes completely.
- Final validation passes across all eight touched Markdown files: no trailing
  whitespace, every local link resolves, and the candidate/property statuses
  are consistent.
- The proof requires only three structural inputs: the new starts form a
  subset of the old starts, the next qualifying threshold is no smaller, and
  an old adjacent pair whose endpoints survive remains adjacent.
- Reconstruction across deleted starts occurs on 1,652 transitions and
  threshold expansion creates additional qualifying edges on 906 transitions,
  but together they fully offset lost old qualifying edges on only 145
  transitions.

## Failed Paths

- **Using the presentation cluster-size chart as separator evidence.** Its
  implementation filters individual `g!=2` values and does not call the
  compressed-run function. Do not cite its `4 -> 14` or `114+` values as
  separator statistics.
- **Creating a duplicate short-separator candidate.** The statement
  `#{i:R_i<2r-4} >= c G_r(W_Q)` is exactly candidate #18's fixed-fraction
  form because the left side is `P(Q,r)`. Do not create #19 for that.
- **Monotone raw short-edge reconstruction.** `P_next>=P_old` fails on 1,639
  of 1,784 transitions. First failure: `Q=17`, `r=5 -> 7`, `P:44 -> 8`.
  Retry only with an explicit attrition term.
- **Monotone disjoint matching.** `D_next>=D_old` fails on 1,685 transitions.
  First failure: `Q=17`, `r=5 -> 7`, `D:22 -> 8`. Do not create a monotone
  matching candidate.
- **One-hit raw attrition.** `P_next>=P_old-H` fails on 385 transitions
  because one deleted start can remove its two incident qualifying edges.
  Retry only with the sharp coefficient `2`, or with an independent recovery
  term that is not defined tautologically from the output.

## Open Concerns

- The giant CSV uses fixed-length prefixes, not guaranteed complete
  `[Q,Q^2)` windows.
- A transition may lose old qualifying edges while gaining new ones because
  the incoming threshold increases. These effects must be counted separately.
- A measured recurrence may be tautological if its “reconstruction” term is
  defined from the observed output rather than bounded by an independent
  input.
- The worktree contains unrelated changes; preserve them.

## Next Action

None. This ticket is complete. The remaining work is candidate #18's existing
uniform or unbounded conditioned-density lower envelope, not a separate
separator candidate.

## Validation

- Search before every new lemma or candidate.
- One conceptual Markdown change per gate.
- Algebraically cross-check separator identities on hand patterns.
- Enforce `P == count(R_i<2r-4)` on every measured layer.
- Enforce matching and population transition identities.
- Record the first counterexample to every proposed recurrence.
- Run the unchanged lineage tests after documentation changes.
- Since planned repository changes are Markdown-only, Stainless verification
  is not required unless a non-Markdown file changes.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | The true compressed separator is directly equivalent to #18's qualifying-edge observable; the presentation chart currently measures a different quantity. | Opened this ticket to formalize the bridge and independently test transition dynamics before considering #19. |
| 2026-07-27 | Discipline, learnings, the existing matching proof, and the full candidate/property search reveal no duplicate separator theorem. Endpoint accounting gives `x_(i+1)=x_i+2+R_i` and enclosure `R_i+4`. | Add the algebraic equivalence to #18 before measuring its distribution. |
| 2026-07-27 | Candidate #18 now contains the complete separator equivalence; strict-boundary hand patterns and Markdown checks pass. | Clarify #7's local-versus-cyclic measurement boundary without changing its hypothesis. |
| 2026-07-27 | Candidate #7 now distinguishes local compressed separators from its complete-period cyclic maximum; #7 and #18 pass documentation checks. | Independently sweep separator distributions and transition reconstruction, hunting failures before proposing #19. |
| 2026-07-27 | The 53-head sweep validates the separator/decomposition identities but refutes monotone `P`, monotone `D`, and coefficient-1 raw attrition. Coefficient-2 raw attrition and coefficient-1 matching attrition pass every transition and have direct graph proofs. | Do not create #19. Promote the sound attrition bounds as an established property, then update #18 and empirical evidence. |
| 2026-07-27 | A second targeted search found no existing transition deletion bound. The theorem needs only subset preservation, nondecreasing threshold, and adjacency preservation for surviving old edges. | Add the standalone algebraic attrition property. |
| 2026-07-27 | The planned attrition note contained two independent lemmas, conflicting with the one-lemma-per-change rule. | Split promotion into raw-edge and matching property files, validating between them. |
| 2026-07-27 | Added the raw close-pair attrition theorem. It passed 559,860 exhaustive finite subsequence cases and its coefficient `2` is attained by the stated strict-threshold example. | Proceed to the separate matching attrition lemma. |
| 2026-07-27 | Added the disjoint matching attrition theorem. It passed 559,860 exhaustive finite subsequence cases and its coefficient `1` is sharp. | Catalog both green properties, then align #18 and empirical evidence. |
| 2026-07-27 | Cataloged the raw and matching attrition theorems as established properties 20 and 21. | Add their exact implications and the failed stronger recurrences to candidate #18. |
| 2026-07-27 | Candidate #18 now contains the true compressed-separator observable, proved sharp transition bounds, and explicit finite counterexamples to monotone reconstruction. Formula/link/framing checks pass. | Promote the independently recomputed separator and transition measurements into the empirical note. |
| 2026-07-27 | Promoted the full independent separator/reconstruction sweep into the empirical note. Numerical, formula, local-scope, and link checks pass. | Align the candidate catalog, then run final regression and static validation. |
| 2026-07-27 | Candidate catalog now distinguishes #7's unmeasured cyclic maximum from #18's local separators and reports the sharp attrition bounds plus monotonicity failures. | Run final regression and static checks, then close the ticket. |
| 2026-07-27 | The unchanged lineage regression suite passes every check (`RESULT: PASS`). | Complete explicit-file static validation and close the ticket if green. |
| 2026-07-27 | Final validation passed: eight touched Markdown files have no trailing whitespace, all local links resolve, regression is green, and no source/article file changed. | Marked the ticket complete and moved it to `tickets/done/`. |
