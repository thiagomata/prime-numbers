# Check Project Guidance Docs

## Goal

Review project guidance and use it to implement `SpecSieveSequence` as a simple infinite generator over numbers accepted by `primes.tail`.

## Current State

The user asked to check the project guidance files before proceeding with implementation work around `SpecSieveSequence`.

## Expected State
c
The relevant guidance is read and summarized, then `SpecSieveSequence` gains a simple verified foundation for enumerating values `>= head` that are not multiples of the primes in `primes.tail`.

## Alternatives Considered

- Rely only on the pasted `AGENTS.md` text. Risk: missing local updates or related guidance from the other files.
- Read only the files directly relevant to proofs. Risk: missing contribution or ticket workflow rules.

## Risks

- Missing a rule that affects verification order or allowed edits.
- Over-reading unrelated files and drifting from the requested task.

## Assumptions

- The requested files exist at the repository root.
- Markdown-only ticket updates do not require Stainless verification.

## Hypotheses

- `OBJECTS.md` lists proof objects and properties that affect `SpecSieveSequence`.
- `PROOF_GUIDE.md` defines required article/proof presentation style.
- `CONTRIBUTING.md` contains workflow rules that complement `AGENTS.md`.
- The first implementation step should avoid primality entirely and define only the tail-filter acceptance predicate.
- A bounded linear search can terminate if its upper bound is proven to pass the tail filter.

## Validation Plan

- Search `tickets/` for similar guidance or `SpecSieveSequence` tickets.
- Read the four requested files.
- Summarize the constraints that matter for upcoming implementation.
- Before Scala changes, run `just verify`.
- After each Scala change, run sieve tests and `just verify`.
- Keep each Scala edit to one small lemma/require/assertion-level step.

## Similar Tickets

- `tickets/complete-prime-prefix-sieve-cycle.md`: discusses `SpecSieveSequence` as an attractive search-style shape and notes the finite-witness/bound challenge.
- `tickets/sieve-properties-step5-coprime-to-modulus.md`: records proof workflow lessons, including one assertion per verify cycle, composing `.holds` lemmas via `assert`, and using `Calc.mod`.
- `tickets/article-consolidation.md`: records article completeness and three-representation rules now reflected in `AGENTS.md`.
- `tickets/article-evaluation-2026-06-15.md`: explicitly uses `AGENTS.md`, `PROOF_GUIDE.md`, and `OBJECTS.md` as publication criteria.

## Progress Log

- 2026-06-17: Ticket created before reading the requested guidance files.
- 2026-06-17: Searched `tickets/` for similar guidance and linked the relevant prior tickets.
- 2026-06-17: Read `AGENTS.md`, `CONTRIBUTING.md`, `PROOF_GUIDE.md`, and the sieve/prime portions of `OBJECTS.md`.
- 2026-06-17: User provided `/Users/thiagomata/Documents/chat.txt` as historical background for the `SpecSieveSequence` ticket. Treat it as useful context to extract hypotheses from, not as binding design.

## Lessons Learned

- Implementation work must run `just verify` before and after code changes; markdown-only changes are exempt.
- Proof/code changes must be split into one assertion, requirement, or lemma per verification cycle.
- `Calc.mod` and `Calc.div` are mandatory; the `%` operator is prohibited.
- `@extern` must not be introduced without explicit instruction.
- `MemCycle`, `ModCycle`, and `CycleIntegral` must not be modified.
- Existing useful facts for `SpecSieveSequence` bounded search are likely `SieveUtils.isCoprime`, `PrimeUtils.primorial`, `PrimeUtils.primorialPositive`, and `PrimeProperties.primorialPlusOneModAny`.
- Prior tickets already identify the search-style `SpecSieveSequence` shape as promising, with the hard part being a finite witness or bound.
- Historical chat insight: `SpecSieveSequence` should be understood as an infinite generator of natural numbers accepted by `primes.tail`, not primarily as a `next()` prime finder.
- Historical chat insight: soundness, completeness, and strict monotonicity follow naturally if `apply(k)` enumerates consecutive natural numbers from `head` and keeps exactly those passing the filter.
- Historical chat caveat: a fixed `primorial(filters) + 1` witness is insufficient for arbitrary later searches because it may be below the current search point. The usable bound must be shifted/aligned above `current`, while preserving the proof that it passes every filter prime.
- Historical chat caveat: stride-based walking by the primorial was discussed, but the current ticket strategy intentionally keeps a simple consecutive linear scan.
- User correction: generated values do not need to be prime. The only acceptance condition is not being a multiple of primes in `primes.tail`; the head is not part of the filter.

## Implementation Plan

1. Inspect current `SpecSieveSequence`, `AllPrimesSoFarList`, `SieveUtils`, `PrimeUtils`, and Euclid lemmas.
2. Run baseline `just verify` before Scala changes.
3. Make the smallest first Scala change that clarifies the V0 acceptance predicate over `primes.tail` only.
4. Add concrete examples and unit tests before deeper proof work.
5. Run sieve tests and `just verify`.
6. Continue only if green; otherwise record the exact failure and stop after at most three failed attempts.

## Expected Examples

These examples are the direction markers for the implementation. Values are accepted only when they are not multiples of the primes in the tail; they are not required to be prime.

| Prime list | Head | Filter tail | Expected generated values |
|------------|------|-------------|---------------------------|
| `[3, 2]` | `3` | `[2]` | `3, 5, 7, 9, 11, 13, 15, ...` |
| `[5, 3, 2]` | `5` | `[3, 2]` | `5, 7, 11, 13, 17, 19, 23, 25, 29, 31, ...` |
| `[7, 5, 3, 2]` | `7` | `[5, 3, 2]` | `7, 11, 13, 17, 19, 23, 29, 31, 37, 41, ...` |

Rejected examples:

- For `[3, 2]`, reject `4, 6, 8, 10, ...` because they are multiples of `2`.
- For `[5, 3, 2]`, reject `6, 8, 9, 10, 12, 14, 15, 16, 18, ...` because they are multiples of `2` or `3`.
- For `[7, 5, 3, 2]`, reject `10, 12, 14, 15, 18, 20, 21, 22, 24, 25, ...` because they are multiples of `2`, `3`, or `5`.

## Implementation Progress

- 2026-06-17: User confirmed generated values are not required to be prime; they only need to avoid multiples of `primes.tail`.
- 2026-06-17: Baseline `just verify` passed before Scala changes: `5499 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Updated `SpecSieveSequence` to use `AllPrimesSoFarList`, with `head` and `filterPrimes` accessors. Sieve tests passed: 9 tests. Post-change `just verify` passed: `5501 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added concrete examples and rejected examples to keep implementation and tests aligned with the tail-only filter semantics.
- 2026-06-17: Added V0 unit tests for `head` and `filterPrimes`. Sieve tests passed: 11 tests. Post-test `just verify` passed: `5501 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added `accepts(value)` as the V0 tail-filter predicate. Sieve tests passed: 11 tests. Post-change `just verify` passed: `5502 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added concrete accepted/rejected unit tests for `[3, 2]`, `[5, 3, 2]`, and `[7, 5, 3, 2]`. Fixed the ScalaTest helper return type after one compile failure. Sieve tests passed: 13 tests. Post-test `just verify` passed: `5502 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added `filterModulus`, the positive primorial of the tail filters, as the named period for the future bounded witness. Sieve tests passed: 13 tests. Post-change `just verify` passed: `5503 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: User clarified that `apply(k)` remains the key method and must be implemented next. The next implementation loop should add concrete `apply` examples, then the smallest bounded linear search that can verify.
- 2026-06-17: Added `passesFilter(value)` to separate tail-filter survival from the head lower-bound condition in `accepts`. Sieve tests passed: 13 tests. Post-change `just verify` passed: `5503 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: User provided the termination hint `n * product(primes.tail) + primes.head + 1`. Interpret this as an exclusive upper bound: `n * product(tail) + head` is the guaranteed accepted witness, and `+ 1` keeps the linear search window open through that witness.
- 2026-06-17: Added the constructor invariant that `head` itself passes the tail-only filter. Sieve tests passed: 13 tests. Post-change `just verify` passed: `5506 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: User noted the `+ 1` may not be needed. Current working interpretation: use `head + n * product(tail)` as an inclusive accepted witness, and only use `+ 1` if a helper wants an exclusive bound.
- 2026-06-17: Added `filterValues` as the named numeric bridge from `List[Prime]` tail filters to `List[BigInt]` arithmetic lemmas. Sieve tests passed: 13 tests. Post-change `just verify` passed: `5506 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Tried redefining `filterModulus` as `SieveUtils.product(filterValues)` to match `SieveUtils.assertExpandedCoprime` directly. Sieve tests passed, but Stainless timed out proving the positivity postcondition: `5505 valid`, `1 unknown`. Reverted by patch to the previously verified `PrimeUtils.primorial(filterPrimes)` implementation; post-revert sieve tests passed and `just verify` returned `5506 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added a concrete unit test for the termination hint on `[5, 3, 2]`: `head + k * filterModulus` passes the tail filter for checked `k = 0..3`. Sieve tests passed: 14 tests. Post-test `just verify` passed: `5506 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added `searchBound(k) = head + k * filterModulus` as the named inclusive bound candidate for the future linear search. Sieve tests passed: 14 tests. Post-change `just verify` passed: `5507 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added `primorialMatchesSieveProduct`, a bridge lemma proving `PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))`. Sieve tests passed: 14 tests. Post-change `just verify` passed: `5512 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Tried adding `searchBoundPassesFilter(k)` by calling `SieveUtils.assertExpandedCoprime` and returning `passesFilter(searchBound(k))`. Sieve tests passed, but `just verify` failed with one unknown on that final postcondition: Stainless did not retain enough from the helper's internal assertions to expose the final `isCoprime(head + k * filterModulus, filterValues)` fact. Removed that failed lemma and restored green: sieve tests passed and `just verify` passed with `5512 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added `expandedCoprimePreservesFilter`, an explicit local lemma whose returned Boolean is `SieveUtils.isCoprime(r + i * modulus, values)`. This exposes the result needed by `SpecSieveSequence` instead of relying on helper-internal assertions. Sieve tests passed: 14 tests. Post-change `just verify` passed: `5562 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Re-added `searchBoundPassesFilter(k)` using the explicit local preservation lemma. This proves the inclusive bound `head + k * filterModulus` passes the tail-only filter and can serve as the finite witness for the future bounded scan. Post-change `just verify` passed: `5572 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added `searchNext(current, upper)`, the bounded consecutive scan helper. It checks each natural number in order and terminates with measure `upper - current`, relying on the caller's proof that `upper` is accepted. Sieve tests passed: 14 tests. Post-change `just verify` passed: `5584 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Implemented `apply(k)` as the simple infinite generator: `apply(0) = head`, and each later index searches consecutive natural numbers from the previous result plus one up to the verified accepted `searchBound(k)`. Sieve tests passed: 14 tests. Post-change `just verify` passed: `5609 valid`, `0 invalid`, `0 unknown`.
- 2026-06-17: Added concrete unit tests for `apply` prefixes on `[3, 2]`, `[5, 3, 2]`, and `[7, 5, 3, 2]`, including composite accepted values such as `9` and `25`. Sieve tests passed: 15 tests. Post-test `just verify` passed: `5609 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Added `noAcceptedBetween(from, until)` as the half-open interval predicate for completeness: it means there is no accepted value in `[from, until)`. Sieve tests passed: 15 tests. Post-change `just verify` passed: `5614 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Strengthened `searchNext(current, upper)` so it proves the returned accepted value is the first accepted value in the bounded search window: `noAcceptedBetween(current, res)`. Sieve tests passed: 15 tests. Post-change `just verify` passed: `5623 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Added `noAcceptedBetweenRejects(from, until, value)`, which extracts `!accepts(value)` for any `value` inside a skipped half-open interval. Sieve tests passed: 15 tests. Post-change `just verify` passed: `5643 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Added `applySkipsNoAcceptedBetween(k)`, which lifts the first-hit property from `searchNext` to `apply(k)` for every nonzero index. Sieve tests passed: 15 tests. Post-change `just verify` passed: `5663 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Added `nextDoesNotPassAcceptedValue(k, value)`, proving that if an accepted `value` is greater than `apply(k)`, then `apply(k + 1)` cannot overshoot it. Sieve tests passed: 15 tests. Post-change `just verify` passed: `5685 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Added `applyStrictlyIncreases(k)` as an internal progress lemma for the future completeness witness recursion. This is not being treated as a public monotonicity deliverable yet; it exists to prove the recursive search measure decreases. Sieve tests passed: 15 tests. Post-change `just verify` passed: `5704 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Added `findIndexForAcceptedFrom(value, k)`, the private constructive completeness witness. Starting from any index whose generated value is at or below an accepted target, it recursively advances until it returns an index whose `apply` value is exactly the target. Sieve tests passed: 15 tests. Post-change `just verify` passed: `5733 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Added public `indexOfAccepted(value)` with postcondition `res >= 0 && apply(res) == value`, exposing the completeness proof for every accepted value at or above `head`. Sieve tests passed: 15 tests. Post-change `just verify` passed: `5744 valid`, `0 invalid`, `0 unknown`.
- 2026-06-18: Added concrete unit coverage showing accepted values, including composites accepted by the tail-only filter, round-trip through `indexOfAccepted` and `apply`. One ScalaTest return-type compile issue was fixed by ending the test with `succeed`. Sieve tests passed: 16 tests. Final `just verify` passed: `5744 valid`, `0 invalid`, `0 unknown`.
