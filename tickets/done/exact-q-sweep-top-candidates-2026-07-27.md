# Exact Q-Sweep for Top Candidates

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete

**Related work:**

- `tickets/active/prove-hereditary-shot-spacing-2026-07-23.md` — candidate
  #14 remains open on square-window placement and conditioned population
  control; it already records that a broader Q-sweep is the next empirical
  falsifier hunt.
- `tickets/active/lineage-experiment-2026-07-23.md` — built the exact
  fixed-future-window lineage measurement and validated the Q17 and Q101
  chains.
- `tickets/done/prove-local-count-forces-shot-capacity-2026-07-27.md` —
  proved the local count threshold that turns a close pair into candidate
  #14's `k=2` interval premise.
- `tickets/done/analyze-capacity-density-candidates-2026-07-27.md` — created
  candidates #17 and #18 as the capacity-density route supporting #14.
- `tickets/done/prove-capacity-floor-algebra-2026-07-27.md` — proved the
  exact seven-layer floor and the local-density-to-matching conversion for
  candidates #17 and #18.
- `candidates/README.md` — current priority order says the next cross-cutting
  empirical step is a Q-sweep on the reinforced candidates, hunting for a
  failing layer.

## START HERE

Use the existing exact lineage tooling to sweep a broader set of prime heads
and record, at minimum:

1. whether candidate #14's exact `k=2` interval premise ever fails;
2. whether candidate #2's local surplus ever goes non-positive;
3. whether the already measured candidate #12 and #13 margins stay positive.

Do not invent new proxy metrics. Prefer exact existing observables already
named in the current candidate notes and lineage ticket.

## Goal

Run the exact falsifier-oriented Q-sweep recommended by the candidate catalog
for the strongest open candidates, then promote the finite result into durable
candidate and empirical notes without overstating what it proves.

## Strategy

This is a read-first, measure-second ticket. The top candidates now split into
two groups:

- #17 and #18 already have their capacity-specific 53-head exact sweep.
- #14, and with it #2/#12/#13 as side outputs, still need the broader exact
  Q-sweep named in `candidates/README.md`.

So the through-line is:

1. re-read the exact lineage tooling and its documented observables;
2. run the sweep on a broader head set using only exact metrics;
3. search first for failures, not trends;
4. only if the sweep is clean, update the top-candidate notes and catalog to
   reflect the new finite scope.

## Current State

- The latest repository verify log is green: `total: 30, valid: 30, invalid: 0,
  unknown: 0`.
- Candidate #14 now has exact finite `k=2` certificates at 4/4 defined Q17
  layers, 23/23 defined Q101 layers, and 1,837/1,837 defined layers across the
  expanded 53-head sweep.
- Candidate #15's follow-on ticket already completed an exact `k=2` sweep over
  53 heads and 1,837 layers with no interval-premise failure, but that result
  has now been propagated into candidate #14 and the top-level candidate
  catalog.
- Candidate #17 and #18 already have their exact 53-head capacity sweep and do
  not need a duplicate run here.
- An in-memory sweep with the exact lineage library now shows candidate #12's
  margin positive at 1,890/1,890 measured layers, with minimum `+12` at
  `Q=17`, `r=13`.
- The same sweep shows candidate #13's one-sided margin positive at
  1,890/1,890 measured layers, with minimum approximately `+15.9851` at
  `Q=19`, `r=17`.
- The candidate catalog has been updated so the remaining cross-cutting work is
  no longer "run the sweep" for #14/#12/#13, but decide whether any further
  empirical pass adds more than the current proof program.

## What is Learned

- The best next empirical step is not another capacity experiment; that part is
  already complete for #17 and #18.
- The exact falsifier hunt for #14/#12/#13 on the 53-head footprint is now
  complete and clean.
- A clean finite sweep strengthens the proof target; a single valid failure
  would immediately refute the universal form being tested.
- The layer-count conventions differ by candidate: #14's premise is undefined
  at the layer installing `3`, while #12 and #13 are measured there. Hence
  #14 reports 1,837 defined layers on this footprint, while #12/#13 report
  1,890 measured layers.

## Failed Paths

- **Repeating the #17/#18 capacity sweep as if it advanced the top-candidate
  frontier.** That work is already complete. Retry only if a genuinely new
  capacity observable is identified.
- **Using proxy-only or whole-window waste metrics for #14 when exact lineage
  observables already exist.** This would regress to a weaker test. Retry only
  if the exact tooling is unavailable for a clearly documented reason.

## Open Concerns

- The candidate catalog wording must distinguish newly completed finite sweeps
  from actual proofs.
- The worktree is dirty; preserve unrelated edits.
- Candidate #2's strongest empirical evidence still comes from the window-pass
  transition sweep rather than the fixed-window lineage family.

## Next Action

None. This scoped sweep-and-propagation ticket is complete. The next work
should be a proof-facing follow-on for either #11's deterministic transference
target or the bounded-family reformulation of #12/#13.

## Validation

- Use only exact named observables from the lineage machinery.
- Record the first failure to any universal claim before any trend summary.
- Keep Markdown-only updates separate from read-only measurement work.
- Run read-only checks on touched Markdown files before closing the ticket.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | The current top-candidate frontier is asymmetric: #17 and #18 already have their exact broad sweep, while #14 and the #2/#12/#13 side outputs still need the cross-cutting Q-sweep named in the catalog. | Opened this ticket and began by auditing the exact lineage tooling and existing sweep artifacts before running anything redundant. |
| 2026-07-27 | The exact 53-head / 1,837-layer `k=2` sweep for #14 was already complete in the empirical artifacts; the live issue was stale propagation into candidate #14 and the top-level README. | Updated the two top-candidate documents so #14's finite scope is current while its universal proof obligation remains explicit. |
| 2026-07-27 | The same exact lineage library runs #12 and #13 without code changes. On the 53-head footprint it found no failures: `c12_margin>0` at 1,890/1,890 measured layers, minimum `+12`; `c13_margin>0` at 1,890/1,890 measured layers, minimum about `+15.9851`. | Updated candidates #12/#13 and the candidate catalog with the stronger finite scope; finish read-only validation and close the ticket if green. |
| 2026-07-27 | Final read-only validation passed: touched Markdown files have no trailing whitespace, normalized local links resolve, and the candidate taxonomy now reflects the 53-head exact lineage scope for #12/#13/#14. | Marked the ticket complete and ready to move to `tickets/done/`. |
