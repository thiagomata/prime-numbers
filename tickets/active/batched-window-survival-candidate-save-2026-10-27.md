# Batched window survival — candidate save

## START HERE

Micro-goal: save the user's generic batch-survival proposal in a dedicated
candidate note and link it from the candidate catalog.

## Goal

Preserve the proposed uniform lower bound, its exact nonrecursive setup, the
proved conditional counting identities, and the user's corrections to earlier
objections. This is documentation, not a claimed proof or experiment.

## Strategy

Create `candidates/batched-window-survival.md`, then add an exploratory catalog
link. Keep the existing exact batch property established; keep the positive
local-survival assertion explicitly open. No articles or source code change.

## Current State

Documentation save complete. The candidate note is saved and linked in the
exploratory catalog. Critic semantic post-check and Monitor post-checks passed
for the note and index. Relative links, balanced fences, whitespace, and
git diff --check passed. Subsequent finite audits and analytical proofs are
indexed in [current work](batched-survival-margin-renewal-2026-10-27.md):
actual N/J bounds and B/F->0 are proved; positive reserve renewal remains open.
The original generic lower-bound candidate remains open.

## Related Work

- [Batch identity save](batched-sequence-jump-save-2026-10-26.md): exact later
  sequence reconstruction, already saved in the established property note.
- [Fixed-window shot budgets](fixed-window-shot-budget-2026-10-26.md): finite
  certificates, not measurements of the generic square-jump proposal.
- `candidates/local-surplus.md`: related single-transition surplus condition;
  its q is consecutive to p, unlike the destination here.

## What is Learned

- Deletion is a union independent of filter order; distinct removal counts are
  also order independent. Static sums can count incidences repeatedly.
- For p>=5, old candidate pairs have disjoint endpoints, giving D<=T.
- Slow exact calculations remain mathematically valid. Loose estimates may
  waste destructive capacity, which is a different issue from runtime cost.
- A generic eventual positive lower bound supplies recurrence itself.
- The saved formulation fixes q as the first prime above p squared and keeps
  complete-period counts distinct from the desired local window guarantee.

## Alternatives, Assumptions, and Risks

A new unnumbered candidate keeps the unproved local claim separate from the
existing proved full-period property and avoids changing the numbered catalog.
Assume q is the first prime above p^2, the old cycle is complete, and old filters
are exactly primes below p. Main risks: confusing total and local populations,
consecutive and batched q, or measured seeds with proof of universal bounds.
Validate by checking definitions, quantifiers, disjoint endpoints, prime
certification below q^2, and increasing window starts in the implication.

## Validation

Markdown-only prose and math; no runtime gates. Check relative links, balanced
fences, whitespace, exact filter range, proof status, and independent reviews.

## Failed Paths

Earlier objections based on filter-order dependence or computational slowness
do not defeat the proposed exact construction; they are not retained as blockers.
Incidence overcount matters only for a chosen additive estimate. Revisit such
an estimate only if its loss is quantified rather than attributed to batching.

## Open Concerns

No X, Y, or p0 has been established. No new empirical data or Stainless proof
is added. Full-period counts do not alone supply the desired local lower bound.

## Next Action

None for this documentation save. Proving or testing the generic bound would
be separate research; no such result is claimed by completion of this ticket.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-27 | The user requests a generic threshold theorem, not an inference from isolated finite successes. | Critic PASS; Monitor bootstrap PASS; created save ticket. |
| 2026-10-27 | Exact batch definitions, order-independent deletion, and the conditional survival certificate can be stated without assuming a local lower bound. | Saved candidate; Critic and Monitor post-checks PASS; links/fences/whitespace PASS. |
| 2026-10-27 | Catalog notation must distinguish the square-jump destination from its usual consecutive head. | Added exploratory link with explicit scope; Monitor post-check PASS; documentation complete, research claim open. |
