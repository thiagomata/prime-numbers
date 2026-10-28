# Cumulative Max-Shot Survival Proposal

Created: 2026-10-23
Status: Candidate reviewed; cumulative abundance remains open

## START HERE

Evaluate whether the observed growth of 2-gaps can be combined with the
existing per-filter maximum-shot bounds to force surviving 2-gaps in square
windows, and determine exactly where the argument fails if it is too strong.

## Goal

Produce a precise candidate inequality connecting a local 2-gap population to
the cumulative capacity of incoming filters. Preserve the proposal even if
review shows that its hypotheses are not currently proved.

## Strategy

Search existing max-shot, local-count, global-count, isolation, and square-safe
properties first. State the strongest valid one-transition capacity inequality,
then test whether summing it across filters preserves the required changing
population and window. Adversarially check overlap, double counting,
complete-period versus local-window counts, and the distinction between a
candidate survivor and a certified twin pair.

## Related Work

- `properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md`
- `properties/sieve-sequence/local-count-forces-k2-shot-capacity.md`
- `properties/sieve-sequence/global-count-forcing-local-survival.md`
- `properties/sieve-sequence/exact-global-two-gap-count.md`
- `properties/sieve-sequence/filtering-attrition-bound-close-pair-matching.md`
- `tickets/future/sieve-property-landscape.md` items 17, 18, and 22

## Current State

Existing notes already prove one-transition lower bounds from a local count and
an exact accepted-shot count. The complete-period product count does not locate
2-gaps in a square window. The cumulative proposal is recorded in
`properties/sieve-sequence/cumulative-max-shot-survival-proposal.md` as a
candidate with an explicit adversarial review.

## What Is Learned

The natural candidate is `local population > cumulative maximum shots`, but
existing work warns that complete-period abundance does not imply local
abundance. The per-filter population changes after each deletion, so a naive
sum must be checked against the actual conditioned sets.

## Failed Paths

None for this ticket yet. Record every invalid cumulative step here with its
counterexample or missing hypothesis.

## Open Concerns

- Whether max-shot bounds count accepted strikes or raw multiples.
- Whether a filter can destroy one or more 2-gaps through shared endpoints.
- Whether local counts refer to the same window at every stage.
- Whether cumulative subtraction double-counts or undercounts destruction.
- Whether the resulting survivor is below the square-certification boundary.

## Validation

Read the cited property bodies, derive the candidate inequality, construct
small finite counterexamples where possible, and run Markdown/link checks only
after the proposal is written. No Scala/Stainless gate applies unless source
code is changed.

## Next Action

The proposal and adversarial verdict are now in the standalone mathematical
note. The exact boundary is recorded: one-transition capacity is proved under
local hypotheses; cumulative local abundance is open.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-23 | Existing local-capacity notes are directly relevant and already warn that global counts do not locate local gaps. | Opened this ticket before drafting the cumulative proposal. |
| 2026-10-23 | The one-transition max-shot subtraction is valid under same-window and isolation hypotheses; naive cumulative subtraction lacks nested conditioned populations and local abundance. | Added the standalone proposal and registered it in the property index with explicit failure modes. |
| 2026-10-23 | Adversarial review found no contradiction in the conditional mechanism, but rejected global-count substitution and unqualified cumulative summation. | Kept the proposal as an open research target rather than promoting it as a theorem. |
