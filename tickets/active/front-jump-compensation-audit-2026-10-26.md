# Bounded front-jump compensation audit

Created: 2026-10-26
Status: Bounded audit complete; compensation remains unproved

## START HERE

Test the accepted idea that a large first-candidate jump forces smaller
advances at following filters. Use actual arithmetic filters, distinguish fixed
anchors from moving heads, and do not create another candidate from a formula.

## Goal

A bounded reproducible check of a precise immediate-compensation statement,
with actual candidate traces and an honest boundary on any conclusion.

## Strategy

For a fixed absolute anchor X, define A_p(X) as the first start at least X
surviving all primes below p. For consecutive heads p<q<r compare jumps
J_p=A_q-A_p and J_q=A_r-A_q against q^2-p^2 and r^2-q^2. Search incoming
primes7..47 with all candidate endpoints at most200000. A strict excess at
both steps refutes universal immediate frontier-scale compensation at arbitrary
anchors; non-detection proves nothing beyond the search.

## Related Work

- [Reverse-history audit](reverse-rejection-history-audit-2026-10-25.md).
- [Backward-head investigation](backward-head-two-gap-bound-2026-08-29.md).
- [Distinguished spacer](../../candidates/distinguished-head-spacer.md).
- [Dream invariant](../../candidates/dream-sequence-self-propagating-invariant.md).
- [Focused bad separators](../../properties/sieve-sequence/two-focused-bad-separator-deletion-bound.md).

## Current State

Read existing spacer/recurrence notes. Critic and Monitor approved the bounded
test and file-free diagnostic. Primary search found zero strict double-frontier
excesses, with13 large-first representative-anchor cases and3 censored cases.
Secondary check found exact successive jumps12,12 at fixed anchor1097 for
filters7,11. Critic and Monitor approved the qualified research write-up.
Saved the research note and reran its exact embedded diagnostic successfully:
table reproduced,13 distinct (p,a,b,c) trigger tuples confirmed, both witness
chains independently verified,3 censored cases confirmed. Both Markdown files
pass links/fences/whitespace. Critic semantic post-review and Monitor actual
content post-review both passed. Research path:
properties/sieve-sequence/research/front-jump-compensation-audit.md.

## What is Learned

Existing notes already separate absolute degradation from recovery through
growth of the threshold. At actual early heads the first candidate may already
be twin prime, so jumps caused by advancing the head must not be mistaken for
composite rejection. Fixed anchors above tested heads isolate filter deletion.
Strict decrease fails at the exact12,12 example. Primary non-detection has
only13 distinct triggering representative starts and is not a compensation
theorem; even no consecutive excesses would not imply cumulative catching.

## Failed Paths

Pre-empted: infer compensation from the complete-period average separator.
The head-selected runs need not be representative. Retry only with a proven
localized restriction or quantitative conditional estimate.
Mandatory strict decrease of successive positive jumps fails at1097,1109,1121.
Retry with a different explicitly stated compensation law; equal jumps do not
refute nonincrease or long-horizon compensation. Initial diagnostic output
omitted the yielded session handle; reran the same read-only calculation with
handle retained. Passive process inspection was unavailable in the sandbox
and was unnecessary; no escalation or file change was required. One atomic
ticket-patch context mismatch changed no files; corrected the exact hunk.

## Open Concerns

Arbitrary fixed-anchor examples do not refute a relation specifically anchored
to hypothetical last primes or the genuine moving head. Consecutive failures
do not exclude compensation over longer horizons. Missing minima at the
finite boundary are censored, not infinite jumps.

## Assumptions and Validation

All old primes are installed, X>r excludes self-head deletion, and all three
minima must have both endpoints in the computed domain. Use only stdlib in a
read-only python -B diagnostic, with division-equality divisibility tests.
Check witness minima independently by trial scanning with gcd, record the exact
algorithm and scope, and validate Markdown links/fences/whitespace. No new
runtime source, articles, candidates, charts or data files are in scope.

## Next Action

No work remains in this bounded audit. Any next mathematical claim requires a
specified cumulative or last-pair-anchored mechanism; no compensation theorem
or new candidate follows from these finite results.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-26 | A compensation statement needs explicit jump scale, filter sequence, anchor and finite-boundary rules. | Opened this scoped audit with strict frontier-scale comparison and independent witness checks. |
| 2026-10-26 | Consecutive equal positive jumps occur; zero strict double-frontier excesses were found with only13 triggering first starts. | Kept primary non-detection and the exploratory strict-decrease counterexample separate; obtained content review approval. |
| 2026-10-26 | The exact saved diagnostic reproduces the table and independently checks both illustrated chains; set dedup confirms13 distinct representative trigger tuples. | Saved the research audit and passed scoped Markdown checks; requested independent post-review. |
| 2026-10-26 | Critic and Monitor actual post-reviews passed without mathematical concerns. | Completed the bounded audit with its negative shortcut result and limited primary non-detection explicit. |
