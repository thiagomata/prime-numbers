# Verify timeout in assertExpandedResiduesRepresentPeriod

## Goal

Resolve the Stainless timeout/UNKNOWN at `SpecCycleSieveEquivalence.scala:947` for the precondition call to `assertModPreservesCoprime` inside `assertExpandedResiduesRepresentPeriod`.

## Current State

`just verify` reports UNKNOWN for the VC proving the precondition of:

```scala
assert(assertModPreservesCoprime(value, seq.modulus, seq.primesTailValues))
```

The VC includes facts about `value`, `head(seq) * modulus(seq)`, expanded residues, and a solved `DivMod(value, modulus(seq), 0, value)`, but Stainless times out or cannot discharge the requirement that `modulus(seq) == product(primesTailValues(seq))`.

## Expected State

The focused proof should verify without timeout, and the full verification result should return to green after the minimal proof change.

## Initial Hypotheses

- The proof context may contain `seq.modulus == product(seq.primesTailValues)` implicitly through a sequence invariant, but Stainless may need it materialized immediately before the call.
- The proof may be passing through accessor aliases (`seq.modulus`, `seq.primesTailValues`) that obscure the required equality from the callee precondition.
- A nearby already-verified lemma may establish the modulus/product relationship more directly.

## Alternatives Considered

- Add one local assertion immediately before the failing call.
- Replace the direct helper call with a more specific lemma if one already exists.
- Restructure the proof to introduce local vals for `modulus` and `primes`, but only if a single assertion is insufficient.

## Risks

- Adding too many facts at once can make Stainless slower or violate the repo's one-change proof discipline.
- The timeout may come from a deeper quantifier/list reasoning path rather than a missing local fact.
- The current verify state may already include unrelated failures, so validation must distinguish this target from global noise.

## Validation Plan

- Read `verify.log` before re-running verification.
- Search `tickets/` for similar timeout or `assertModPreservesCoprime` work and link relevant prior tickets here.
- Inspect the failing function and the callee preconditions.
- Make at most one proof assertion change at a time.
- Run focused verification for `assertExpandedResiduesRepresentPeriod` after each proof edit.
- Run full `just verify` after code changes once the focused verification is green.

## Similar Tickets

- `tickets/superseded/v0-v2-apply-equivalence.md` records that `assertExpandedResiduesRepresentPeriod` and `assertModPreservesCoprime` previously verified, with the latter using prefix-product recursion to avoid recursive product precondition failures.
- `tickets/done/v0-apply-modulus-loop.md` records a similar timeout pattern where product equalities for recursive calls needed more direct facts.
- `tickets/active/sieve-sequence-proof.md` records the general local pattern: timeout-prone VCs often need one explicit anchor assertion rather than asking Stainless to rediscover a derived equality inside a larger proof.

## Progress Log

- Created ticket from the reported timeout and initial VC.
- Checked `verify.log`; latest recorded failure is UNKNOWN at the precondition requiring `seq.modulus == SieveUtils.product(seq.primesTailValues)`.
- Inspected `CycleSieveSequence`: `seq.modulus` is `PrimeUtils.primorial(seq.primes.list.tail.list)`, while `seq.primesTailValues` is `PrimeUtils.primeValues(seq.primes.list.tail.list)`. The missing bridge is therefore primorial/product representation, not coprimality itself.
- Added one assertion before the failing helper call: `seq.modulus == SieveUtils.product(seq.primesTailValues)`.
- Ran `just test` after the code change. Result: 144 tests run, 140 succeeded, 4 failed in `CycleSieveSequenceTest`, all comparing `AllPrimesSoFarList(...)` values against raw `List[BigInt]` expectations. These appear unrelated to the proof assertion.
- Focus verification attempt 1 after the direct assertion timed out at the new equality assertion: 33 total, 32 valid, 1 unknown, time 303.35s. This confirmed the original precondition is solved once the equality is present, but the equality cannot be proved inline.
- Added local `primorialMatchesSieveProduct` bridge lemma, matching the already-verified pattern in `SpecSieveSequence`, and called it before the equality assertion.
- Fixed the bridge lemma signature to use `stainless.collection.List[Prime]`.
- Focus verification passed for `assertExpandedResiduesRepresentPeriod`: 35 total, 35 valid, 0 invalid, 0 unknown, time 2.78s. The suggested Stainless debug flags were not needed after the bridge lemma exposed the missing equality.
- Added initial Stainless debug flags to the standard `just verify` recipe, then refined them after checking the valid options for Stainless 0.9.8.8.
- Current `just verify` debug default is `--debug=verification,full-vc,solver,timers,call-graph` with object filtering for `assertExpandedResiduesRepresentPeriod`, `assertModPreservesCoprime`, `nextGaps`, `nextSorted`, and `calculateGaps`.
- Deliberately left `trees` out of the default because full-tree dumps are too noisy for normal full verification logs; add it only for a focused lowered-tree inspection.
- Did not run `just verify` after changing the recipe because multiple actors were triggering verification and overwriting each other's `verify.log` output. Validation should be coordinated before the next run.
