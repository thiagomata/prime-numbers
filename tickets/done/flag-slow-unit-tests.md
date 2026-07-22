# Flag Slow Unit Tests

**Status:** Active
**Created:** 2026-06-22

## Goal

Keep the normal unit-test loop fast by marking tests that take too long for
`just test` as slow, so they can still exist but do not dominate ordinary proof
iteration.

## Current State

- A recent `just test` run passed, but took 129 seconds for 173 tests.
- The user noted that the standard test command is too slow for a unit-test
  feedback loop and that some tests should be flagged as slow.

## Expected State

- Identify the slowest tests from existing logs or framework output.
- Use the repository's existing slow-test mechanism, if one exists.
- Keep the change scoped to test classification or test command wiring.
- Avoid rerunning the full slow test suite unless needed for validation.

## Alternatives Considered

- Leave the tests as-is and rely on focused Stainless verification. Rejected:
  this does not fix the slow unit-test loop.
- Delete or weaken slow tests. Rejected: slow coverage can still be useful.
- Add a new slow-test mechanism from scratch. Risky unless no existing pattern
  exists.

## Risks

- The test framework may not currently support tags/categories.
- Slow tests may be slow because of shared setup rather than individual bodies.
- Running the full suite repeatedly would waste time while diagnosing this.

## Assumptions and Validation

- Assumption: existing logs identify which tests are slow.
  - Validate by inspecting `test.log` before rerunning tests.
- Assumption: tests already have or can cheaply add a slow marker.
  - Validate by searching test sources and build configuration for tags.
- Final validation: run the fastest command that checks test discovery or a
  small targeted subset. Full `just test` should be avoided unless the change
  requires it.

## Related Tickets

- No prior dedicated slow-test ticket found. Existing slow-test handling lived
  in `justfile` and `SpecSieveSequenceTest`.

## Update Log

### 2026-06-22 — Shared slow tag and first slow-test split

- Added shared test tag `v1.tags.SlowLemmaTest`.
- Reused the shared tag from `SpecSieveSequenceTest` instead of defining a
  local tag object there.
- Tagged proof-heavy property suites as slow:
  `ClassicCycleIntegralPropertiesTest`,
  `ModCycleIntegralPropertiesTest`, and `IntegralPropertiesTest`.
- Updated `just test-slow` to discover all tests tagged with
  `v1.tags.SlowLemmaTest`, not only slow tests in `SpecSieveSequenceTest`.
- First validation: `just verify` passed with 7806 valid, 0 invalid, 0 unknown.
  `just test` still took 138 seconds, so more linear-search examples needed to
  move out of the fast path.

### 2026-06-22 — Linear-search examples moved to slow bucket

- Tagged expensive Spec linear-search examples as slow:
  head-plus-tail-product acceptance, apply prefix generation,
  `indexOfAccepted`, and concrete `gapList` extraction.
- Tagged expensive `AllPrimesSoFarList` range and `nextPrime` examples as slow.
- Validation: `just verify` passed with 7806 valid, 0 invalid, 0 unknown.
  `just test` passed with 144 tests and now completes in 20 seconds total
  (ScalaTest run time: 7.828 seconds), down from 129-138 seconds.
- `just test-slow` was not run in this loop because it intentionally contains
  the expensive tests that were moved out of the default command.
