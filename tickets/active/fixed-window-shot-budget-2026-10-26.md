# Candidate population versus fixed-window shot budgets

Created: 2026-10-26
Status: Bounded shot-budget check complete

## START HERE

User asks whether candidate populations can exceed the total available filter
shots even though some fixed fences empty. Calculate that exact inequality in
the five previous windows; do not assume universal fence persistence.

## Goal

Record conservative finite surplus certificates, failures to certify, and
actual accepted shots for comparison. Preserve a reproducible arithmetic check.

## Strategy

Reuse closed endpoint windows [10,50],[100,150],[155,175],[200,250],[1000,1100]
with initial filters 2, 3, 5. Let G0 be initial pair count. T counts all actually
accepted values removed by subsequent primes through sqrt(hi), not just
harmful endpoints. U sums those primes' multiple counts among initial accepted
values and safely overcounts T. At each intermediate stage, recompute G_t and
remaining U_t from the current accepted values without consulting final pairs.
Strict G_t>U_t certifies at least one survivor. Check independently at the end.

## Related Work

- [Fixed-window contacts](fixed-window-contact-check-2026-10-26.md).
- [Earlier cumulative proposal](cumulative-max-shot-survival-proposal-2026-10-23.md).
- [Local survival threshold](../../properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md).
- [Endpoint isolation](../../properties/sieve-sequence/two-gap-isolation-after-filter-three.md).

## Current State

Critic approved arithmetic and Monitor approved bootstrap/diagnostic. Parent
diagnostic exactly matched the independent reviewer: (G0,U,T,Gfinal) equals
(5,1,1,4),(5,4,4,3),(2,2,2,0),(4,5,5,2),(11,14,12,5).
The first two fences certify at stage 5; after filter 7 the fourth certifies
4>3 and the fifth 9>8. All budget, nestedness and primality controls passed.
Saved the scoped research note with conservative budget proof, tables and
read-only reproduction. Embedded rerun and both Markdown checks pass.
Critic and Monitor actual post-reviews passed; both independently reproduced
the arithmetic. Readability cleanup changes no mathematical or executable text.

## What is Learned

Post-3 endpoint disjointness permits at most one destroyed pair per accepted
shot. Static remaining capacities can be computed from the current accepted
values without selecting a future survivor. Summing safe maxima may fail to
certify actual twins because it wastes shots or double-counts possible hits.
The user's strict surplus does occur before all relevant filters have run.
It can certify an unidentified survivor using only current accepted values
and future multiple capacities; it is not universal and fails in the empty fence.

## Failed Paths

Pre-empted: using only the number of actually destroyed pairs as the alleged
independent budget; that restates the final survivor count. Use all accepted
value strikes and conservative precomputed future-multiple budgets instead.
Retry a sharper endpoint-aware bound only with its independent derivation.

## Open Concerns

Finite surplus certificates do not prove recurring surplus or twin infinitude.
U is deliberately an overcount; U>=G is inconclusive, not extinction evidence.
Current populations and remaining budgets must use the same fixed window.

## Assumptions and Validation

All endpoints lie inside each closed window, all values exceed all tested
filters. Nested accepted sets, exact strike removals, U>=T, stagewise survivor
bounds, independent final trial primality, and reported earliest certificates
must be checked. Save only this ticket and a research note, rerun its embedded
stdlib python -B diagnostic, validate links/fences/whitespace. No source,
articles, PDFs, packages or new candidate files are affected.

## Next Action

No work remains in this bounded check. Report finite conservative certificates;
recurring surplus at unbounded ranges remains open.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-26 | Empty fixed fences do not refute independent candidate-versus-capacity certificates in other fences. | Scoped same-window conservative budgets with all accepted shots retained. |
| 2026-10-26 | Conservative strict surplus holds at stage 5 or 7 in all four positive fences, while the negative control never passes. | Parent diagnostic matched independent arithmetic and passed every control; prepared the scoped research write-up. |
| 2026-10-26 | Saved reproduction and scoped Markdown checks passed; Critic and Monitor post-reviews confirmed all tables and early certificates. | Completed the finite check without claiming a recurring-surplus theorem. |
