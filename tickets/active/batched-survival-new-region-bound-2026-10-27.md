# New-region contribution in square-destination transitions

## START HERE

Micro-goal: prove a finite absolute bound for actual N, then its eventual
smallness relative to F; identify precisely what this proves about survival.

## Goal

Save a reviewed analytical bound on the remaining signed new-region term.
Distinguish actual term estimates from assumptions about actual positive L.

## Strategy

First bound the number and cubic weights of fresh starts. Separately use
quantitative classical PNT to compare their total contribution with F.
Finally state the one-step consequence and the missing infinite invariant.
Prefer these unconditional bounds to assuming N is positive. No executable,
Scala, article, PDF, or empirical changes are planned.

## Current State

Finite, asymptotic and conditional one-step proofs saved in
`properties/sieve-sequence/research/batched-survival-new-region-bound.md`;
each addition received exact-text Critic and Monitor post-PASS. Quantitative
PNT verified in Evertse's Leiden notes ant18-1.pdf, printed p.53 equation(1.1),
attributed there to de la Vallée Poussin (1899). Candidate, component and
shared-region notes now link the result and consistently leave the actual
positive reserve open. Five affected files passed links/fences/whitespace
checks; git diff --check PASS. Scope-sync final Critic and Monitor reviews
PASS; scoped mathematical work is complete.

Documentation synchronization and continued actual-margin renewal work are
tracked in [the successor ticket](batched-survival-margin-renewal-2026-10-27.md).

## Related Work

- [Shared-region J bound](batched-survival-filtered-shot-bound-2026-10-27.md).
- [R component bound](batched-survival-easy-term-bounds-2026-10-27.md).
- [Exact transport](batched-survival-propagation-check-2026-10-27.md).
- [Density benchmark](batched-survival-analytic-bound-2026-10-27.md).

## What is Learned

For p>=5, s next prime, q first prime above p^2, t first above s^2,
fresh starts number at most (t^2-q^2)/6; each has weight between -35 and 1.
The saved proof establishes |N|<=35(t^2-q^2)/6. Quantitative PNT gives
|N|/F->0. Hence B=|N|+Rcap+J is nonnegative and B/F->0 for actual
square transitions, with Lnext>=Lcurrent-B. For every fixed eta>0,
sufficiently late transitions with Lcurrent>=eta*F have Lnext>=eta*F/2>0
in old F units. This premise has not been proved eventually or reproduced.
An abstract oscillating scalar example demonstrates why small per-step
changes alone do not ensure indefinite positivity; it is not sieve data.

## Alternatives, Assumptions and Validation

Qualitative PNT alone gives window growth o(p^4), insufficient to compare
with F of order p^4/log^2(p). Check a primary quantitative-PNT source and
derive the needed interval estimate explicitly. Validate each mathematical
addition through independent Critic and Monitor review, then local links,
fences, whitespace and git diff --check. Runtime gates do not apply.

## Failed Paths

No executed proof attempt failed. Pre-empted shortcut: infer an infinite
positive invariant from per-step o(F) losses. The losses can accumulate;
retry only with a proved lower reserve or compensation estimate that closes
the recurrence. Do not claim N>=0 from an absolute bound.

## Open Concerns

F is a positive density benchmark, not a proved lower bound for actual L.
Even an eventual one-step implication L>=eta*F implies next L>=eta*F/2
does not reproduce its own hypothesis. Infinite positive survival remains open.

## Next Action

None within this completed proof scope.
Future analytical target: a bound retaining/replenishing actual positive L,
or forcing recurring positive certificates. Do not repeat loss smallness
as though it proved that missing condition. Articles are unchanged; promoting
these research results to the article would require its MD/LaTeX/PDF gates.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-27 | Critic checked square-window geometry, cubic weight constant and proposed asymptotic route. | Bootstrap Critic and Monitor PASS; persistent ticket created. |
| 2026-10-27 | Actual finite N bound established; primary quantitative PNT source verified, with fixed-m thresholds. | Finite proof reviewed green; asymptotic addition approved separately. |
| 2026-10-27 | Quantitative PNT proves actual absolute N divided by F tends to zero; all three loss terms now have negligible combined upper budget. | Asymptotic and one-step sections saved and independently reviewed PASS. |
| 2026-10-27 | A halved reserve in old F units is not a closed induction; actual margin remains the open condition. | Candidate/component/shared-region scope synchronized; all five Markdown and diff checks PASS; final scope review requested. |
| 2026-10-27 | Exact final scope review confirms proved actual loss bounds and missing margin invariant are distinguished. | Critic and Monitor PASS; table formatting corrected; scoped proof complete. |
