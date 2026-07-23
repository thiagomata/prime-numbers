# Base One-Prime Spec/Filter Equivalence

**Created:** 2026-07-14
**Status:** Active
**Owner:** Proof bridge for the smallest spec/filter case

## START HERE

Micro-goal: prove the smallest useful equivalence between a one-prime
`SpecSieveSequence` filter decision and a one-prime `filterList`/coprime
decision, without attempting the full `nextFiltered` size theorem.

## Goal

Start from the smallest `SpecSieveSequence` case currently representable by the
class: a stage with one active filter prime. The true sieve seed has
`AllPrimesSoFarList([2])`, but `SpecSieveSequence` currently requires
`primes.size > 1`, so that seed is represented by `CycleSieveSequence.S_0()`,
not by this spec class.

For the first spec-representable filtered stage, prove that the spec's one-prime
filter decision and the concrete modulo filter accept exactly the same values.

Expected theorem shape:

```text
Spec filter values == List(p)
value >= spec.head.value
--------------------------------
spec.accepts(value) == (Calc.mod(value, p) != 0)
```

or, preferably for avoiding lower-bound obligations:

```text
Spec filter values == List(p)
--------------------------------
spec.passesFilter(value) == (Calc.mod(value, p) != 0)
```

## Current State

- `logs/verify.log` is green after the first code change: `14002 valid`,
  `0 invalid`, `0 unknown`.
- Existing guidance in `LEARNINGS.md` says to prefer `passesFilter` over
  `accepts` when only the filter predicate is needed, because `accepts` carries
  a lower-bound precondition.
- Existing private `filterList` membership helpers in
  `SpecCycleSieveEquivalence` already bridge list membership and
  `Calc.mod(value, divisor) != 0`.
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md` warns not to
  pursue the broad `nextFiltered`/sorting route for the full size theorem.
- User correction: the mathematical base stage is `S_0` with all-primes-so-far
  list `[2]`, empty tail filters, modulus `1`, and gap `[1]`. Do not call the
  `[3,2]` one-filter spec stage the seed.
- `SpecSieveSequence.sameHeadSurvivorCount(period)` is the relevant spec-side
  count wrapper once a non-seed spec stage exists. It packages
  `assertSameHeadExtendedFilterCount(period)` rather than proving list/pipeline
  equality directly.

## Similar Tickets

- `tickets/done/spec-same-head-filter-density.md`
  - Proved the spec-local same-head count theorem.
  - Relevant because this task should reuse predicate/count ideas rather than
    re-proving global list equality.
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md`
  - Records the full `M`-interval density goal and prior route corrections.
  - Relevant warning: do not broaden this base case into the full pipeline size
    theorem in one step.
- `tickets/trash/superseded/v0-v2-apply-equivalence.md`
  - Contains older base-case and pipeline-equivalence notes.
  - Use only as an idea bank; verify all names and bodies against current
    source before relying on them.

## Plan

1. Read the current bodies of `passesFilter`, `accepts`, and the list/coprime
   helpers before editing.
2. Prefer a single small `.holds` lemma, likely in `SpecSieveSequence`, that
   exposes one-prime filter equivalence for `passesFilter`.
3. Verify the single focused function first.
4. If green, run full `just verify`.
5. Update this ticket with the exact outcome and any next theorem shape.

## Risks

- Using `accepts` too early may trigger avoidable lower-bound proof work.
- Proving list equality is likely broader than needed and may recreate old
  failures.
- The one-prime theorem may need a reusable singleton-list coprime lemma from
  `SieveUtils` or `CoprimeUtils`; search before writing a new helper.

## Validation

- Focused validation: `just verify <newFunctionName>`.
- Final validation after code changes: `just verify`.

## Learning Log

- 2026-07-14: Ticket created. Baseline green from `logs/verify.log`: `14000
  valid`, `0 invalid`, `0 unknown`.
- 2026-07-14: Added `SpecSieveSequence.assertSingletonFilterDecision(value,p)`.
  Focused verification passed: `2 valid`, `0 invalid`, `0 unknown`. Full
  verification passed: `14002 valid`, `0 invalid`, `0 unknown`.
- 2026-07-14: User corrected the base-case framing. The true seed is
  `AllPrimesSoFarList([2])` / `CycleSieveSequence.S_0()`, while
  `SpecSieveSequence` excludes that seed with `require(primes.size > 1)`. The
  verified singleton-filter lemma is therefore an `S_1`-style bridge, not the
  seed-stage proof.
- 2026-07-14: Added
  `SpecSieveSequence.assertNextAcceptsMatchesHeadFilterForAcceptedValue(v)`.
  Focused verification passed: `28 valid`, `0 invalid`, `0 unknown`. Full
  verification passed: `14030 valid`, `0 invalid`, `0 unknown`. This is a
  verified leaf predicate bridge only. User corrected the next target: the main
  construction invariant should be `repeat -> filter -> rotate` produces the
  same result as `rotate -> repeat -> filter`.
