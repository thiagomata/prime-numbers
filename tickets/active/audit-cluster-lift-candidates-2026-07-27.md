# Audit Cluster-Lift Ideas Against the Candidate Set

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete
**Depends on:** `develop-admissible-shot-spacing-candidate-2026-07-27.md`

## Related Tickets

- `prove-hereditary-shot-spacing-2026-07-23.md` — separates global spacing
  capacity from the missing square-window localization theorem.
- `develop-admissible-shot-spacing-candidate-2026-07-27.md` — proves the
  complete-period length-8 two-gap cluster but leaves absolute placement open.
- `document-2-gap-merge-survival-candidates-2026-07-23.md` — introduced the
  protected-cluster candidate and its one-filter survival condition.
- `tickets/future/sieve-property-landscape.md` — records exact lifted-copy
  uniformity, complete-block decomposition, and the boundary-only obstruction.

## Goal

Audit every substantive idea developed in the current conversation against
`candidates/`. Ensure all genuinely conjectural mechanisms are represented
without moving proved algebra back into candidates. The ideas to classify are:

1. exact complete-cycle growth of `(2,4,2)` clusters by `r-4`;
2. lifted danger-zone copy orbits;
3. survival by subtracting the maximum capacity of the added region;
4. a copy-index branch that grows slowly enough to re-enter a square
   certification horizon;
5. the distinction between perfect copy-index distribution and unproved
   distribution inside one short absolute window.

## Strategy

Read the three closest candidates and the established copy/filter properties
in full. Build a coverage map with one of three outcomes per idea:

- already present accurately;
- proved and therefore belongs in `properties/`, with only its conjectural
  application linked from candidates;
- missing conjectural mechanism that should be added to the narrowest existing
  candidate or, if no existing candidate owns it, a new candidate.

Prefer strengthening candidate #14 or #15 over creating overlapping files.
Keep global algebra and local square-window conclusions explicitly separate.

## Current State

- Initial search found the one-filter target-versus-shot argument in
  `protected-cluster.md`.
- Candidate #14 contains the hereditary interval-capacity premise.
- Candidate #15 contains complete-period cluster existence and identifies
  copy-index localization as missing.
- The future landscape records exact full-block behavior and boundary-only
  uncertainty, but future tickets are not a substitute for candidate coverage.
- No initial-search hit states the exact `(2,4,2)` cluster recurrence, the
  expanded-minus-outside capacity inequality, or the slow-branch formulation.
- Full reads confirm:
  - candidates #3 and #14 already own the one-filter target-versus-shot
    implication;
  - candidate #9 owns forbidden copy-index runs but only hints at moving seeds
    or mesoscopic aggregation;
  - candidate #15 owns the exact shot-spacing profile, not localization;
  - exact individual and batched 2-gap lift counts already live in properties.
- The missing conjectural ideas fit one new localization candidate with two
  sufficient routes:
  1. an exactly countable superset whose surviving total exceeds the maximum
     outside capacity;
  2. a safe copy-index branch whose numerical position remains inside a later
     square-certification horizon.
- The exact `(2,4,2)` recurrence should first be promoted as a property and
  then cited as an established global input by the new candidate.
- `properties/sieve-sequence/exact-global-two-gap-cluster-count.md` now proves
  `C_{rM}=(r-4)C_M` and the closed product
  `C(P)=product_{p in P,p>=5}(p-4)`.
- Direct complete-cycle enumeration independently matched the recurrence at
  moduli `6,30,210,2310,30030`, with counts `1,1,3,21,189`.
- `candidates/expanded-zone-exterior-capacity.md` now records:
  - the positive exterior-subtracted surplus criterion;
  - the exact implication from `L_q>U_q` to a square-safe 2-gap;
  - the failed naive complete-lift comparison;
  - the alternative slow square-safe copy-branch hypothesis;
  - the distinction between perfect copy-index distribution and unproved
    short-position distribution.
- Both new artifacts are indexed:
  - the cluster recurrence is item 2 in the sieve-sequence property catalog;
  - expanded-zone localization is candidate #16 and is classified as
    deferred/unmeasured.
- Final link, terminology, trailing-whitespace, and `git diff --check` audits
  pass.

## What is Learned

- The exact recurrence `C_next=(r-4)C`, if its no-new-cluster premise is
  checked, is mathematical property material rather than a candidate.
- The expanded-zone subtraction step is a general deterministic implication:
  a local result still needs an upper bound on the outside capacity strong
  enough to make the difference positive.
- Complete copy-orbit survival alone does not select the designated square
  window.
- After filter `3`, filtering cannot create a new gap `2`. It also cannot
  create a new gap `4`: a merged gap of size `4` would have to be `2+2`, but
  consecutive 2-gaps are forbidden modulo `3`. Hence a post-filter
  `(2,4,2)` word is exactly a surviving copied occurrence.
- For an incoming prime `r>=5`, the four cluster endpoints
  `{0,2,6,8}` occupy distinct residues modulo `r`. Each old cluster therefore
  has exactly `r-4` surviving copies, giving an exact complete-cycle
  recurrence.

## Failed Paths

- **Treat future-ticket coverage as candidate coverage.** Rejected because the
  user explicitly asked whether the ideas are discoverable in `candidates/`.
  Retry only if the repository convention changes to catalog future research
  directly from the candidate index.
- **Use a complete `r`-copy lift to force a survivor into one designated
  component by count alone.** An old 2-gap has `r-2` surviving copies, while
  the other `r-1` components can hold all of them. The corresponding cluster
  inequality is `r-4<=r-1`. Retry only with a smaller exactly countable
  expansion, a stronger outside-capacity bound, or copy-phase information
  selecting the real component.
- **Two ticket synchronizations were executed before their visible
  pre-execution gate.** Both edits were Markdown-only and content-correct, but
  the required protocol order was missed. The omissions were reported
  immediately and no third occurrence happened. Retry condition is simply to
  emit the complete Worker/Critic/Monitor gate before every future modifying
  action.

## Open Concerns

- No coverage concern remains for the ideas developed in this conversation.
- Candidate #16 remains unproved and unmeasured by design; its first meaningful
  experiment is the exterior-subtracted margin, not another global count.
- Unrelated shared-worktree changes remain outside this audit and were
  preserved.

## Next Action

Done. A future focused ticket may construct finite exactly countable
expansions and measure `L_q-U_q`, or search the safe copy tree for its minimum
branch position relative to the square horizon.

## Validation

- Every thread idea has an explicit destination and status.
- Candidate prose does not claim the square-window placement theorem.
- Proved facts remain in `properties/`; empirical facts remain in
  `empirical/`.
- All Markdown links resolve and `git diff --check` passes.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-27 | Initial search found partial but incomplete candidate coverage; full-block ideas exist only in a future landscape note. | Opened focused audit ticket and selected a proof/candidate boundary review before edits. |
| 2026-07-27 | Full audit separated already-covered one-layer capacity from three missing pieces: exact cluster growth, exterior subtraction, and slow square-safe branches. The naive complete-lift pigeonhole fails because all survivors can fit outside the designated component. | Selected property promotion for the recurrence and one new localization candidate for the two conjectural routes. |
| 2026-07-27 | Proved exact complete-cycle `(2,4,2)` growth by `r-4`; independent counts through modulus `30030` match the closed product. | Promoted the fact to properties and advanced to the missing localization candidate. |
| 2026-07-27 | Added the expanded-zone candidate with both localization routes and the exact complete-lift falsifier. | Advanced to catalog and cross-link alignment. |
| 2026-07-27 | Cataloged the exact cluster recurrence and candidate #16; final searches confirm every thread idea is now discoverable from `candidates/`. | Marked the audit complete and left finite exterior-margin measurement as the next separate research task. |
