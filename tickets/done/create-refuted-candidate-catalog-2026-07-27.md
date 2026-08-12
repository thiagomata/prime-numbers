# Create Refuted Candidate Catalog

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete

**Related work:**

- `tickets/done/evaluate-conditioned-separator-dynamics-2026-07-27.md` — established the separator observable, proved the sharp attrition bounds, and recorded exact finite counterexamples to stronger monotone subclaims.
- `tickets/done/prove-capacity-floor-algebra-2026-07-27.md` — aligned the candidate catalog after new algebraic results and is the most recent status-language precedent for #17 and #18.
- `tickets/active/document-2-gap-merge-survival-candidates-2026-07-23.md` — original creation of the candidate folder and its distinction from established properties.
- `candidates/README.md` — current status taxonomy and candidate index that must stay honest after adding a refuted-subclaims area.

## START HERE

Create a durable home for statements that are genuinely false without implying
that any numbered candidate note has been globally refuted. Start with the
monotone separator-reconstruction family already falsified by the exact 53-head
sweep.

## Goal

Add a refuted-candidate catalog under `candidates/` so false subclaims are
easy to find and are not retried later, while preserving the current truthful
statement that no numbered candidate note has been fully refuted.

## Strategy

Use the existing candidate taxonomy and separator-dynamics ticket as the source
of truth. Record only exact universal statements defeated by explicit finite
counterexamples. Keep failed proof approaches in tickets, not in the refuted
catalog. Update the top-level candidate README so it distinguishes
"no numbered candidate fully refuted" from "some proposed subclaims are
refuted."

## Current State

- `candidates/README.md` no longer needs to imply "nothing false exists";
  it should distinguish fully refuted numbered candidates from refuted
  subclaims.
- The same README already states under candidate #18 that monotone `P` and
  monotone `D` are empirically refuted.
- The completed separator-dynamics ticket records exact first counterexamples:
  `Q=17`, `r=5 -> 7`, with `P:44 -> 8`, `D:22 -> 8`, and `H=18`.
- `candidates/refuted/README.md` now exists and defines the admission rule for
  genuinely false statements.
- `candidates/refuted/monotone-separator-reconstruction.md` now records the
  first refuted subclaim family and its exact first counterexample.
- `candidates/README.md` now points the `REFUTED` taxonomy row to the new
  catalog and states explicitly that no numbered candidate note is fully
  refuted.
- Repository verify log is green (`total: 30, valid: 30, invalid: 0, unknown: 0`).

## What is Learned

- The project now has a real distinction between a candidate note remaining
  open and some stronger auxiliary formulation being false.
- Refuted universal subclaims are durable research results and should be
  discoverable outside tickets.
- The right scope for the first refuted note is the monotone
  separator-reconstruction family attached to candidate #18, not candidate #18
  itself.

## Failed Paths

- **Using the top-level `REFUTED` row as "nothing false exists."** This would
  now be misleading because some transition laws are explicitly falsified.
  Retry only if the row is reworded to mean "no numbered candidate fully
  refuted."
- **Marking candidate #18 itself as refuted.** The false statements are
  stronger monotone recurrences, while the candidate's proved density
  conversion and open lower-envelope target remain intact. Retry only if a
  counterexample defeats candidate #18's actual stated hypothesis.

## Open Concerns

- The catalog language must not conflict with existing candidate status tags.
- Relative links from tickets and candidate notes should keep working after the
  new folder is added.
- This should remain Markdown-only; no source or article files should change.

## Next Action

None. This ticket is complete.

## Validation

- Keep all changes under `candidates/` and `tickets/`.
- Check local links for the touched Markdown files.
- Check for trailing whitespace in the touched Markdown files.
- Re-read the top-level status summary to ensure it says both:
  "no numbered candidate fully refuted" and "see refuted subclaims catalog."

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | The catalog already contains explicit refutation language for stronger separator recurrences, but there is no durable index for those false statements. | Opened this ticket to add a refuted-subclaims catalog without mislabeling any numbered candidate as globally refuted. |
| 2026-07-27 | A dedicated `candidates/refuted/` folder is now in place, with admission rules and a first note for the monotone separator-reconstruction family. | Update the top-level candidate README so its status taxonomy points to the new catalog. |
| 2026-07-27 | Final read-only validation passed: touched Markdown files have no trailing whitespace, all local links resolve, and the status taxonomy now preserves the distinction between refuted subclaims and open numbered candidates. | Mark the ticket complete and move it to `tickets/done/`. |
