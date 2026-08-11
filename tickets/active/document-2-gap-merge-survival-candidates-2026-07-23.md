# Document 2-Gap Merge-Survival Candidates

## Goal

Create top-level `candidates/` with an index and one concise,
self-contained document for each of the fourteen proposed sufficient conditions for
square-safe 2-gap survival under the induced merge process.

## Current State

The property catalog already documents established global counts,
copy-index filtering, local strike capacity, safe-window certification, and
the short-window discrepancy boundary. The proposed merge-survival conditions
are currently collected only in discussion and need a clearly marked research
hypothesis catalog outside `properties/`. Candidate hypotheses are unproved and
may be false; only their conditional implications are proved.

Existing dirty files, especially `properties/sieve-sequence/README.md`, are out
of scope and must remain untouched.

## Expected State

- Add `candidates/README.md`.
- Add one document for each candidate:
  1. protected endpoints;
  2. local surplus;
  3. protected clusters;
  4. bounded consecutive destruction;
  5. bounded post-merge spacers;
  6. controlled merge runs;
  7. balanced spacers;
  8. distinguished head spacer;
  9. forbidden-copy covered runs;
  10. short-window discrepancy;
  11. random-like merge survival;
  12. local pattern-residue balance;
  13. uniform local observable sampling;
  14. hereditary shot-spacing capacity.
- Every document must separate:
  - the unproved candidate hypothesis;
  - the proved conditional implication;
  - established inputs from existing notes;
  - the exact limitation and research obligation.
- Holding a condition at one stage gives one square-safe certificate; holding
  it at infinitely many stages gives infinitely many certificates.

## Overlap Matrix

| Candidate | Existing related note | New document's distinct role |
|---|---|---|
| Protected endpoints | `absence-of-two-gaps-is-stable.md` | State endpoint protection as a sufficient merge hypothesis. |
| Local surplus | `sharp-local-two-gap-survival-threshold.md` | Reframe the exact threshold as a candidate invariant. |
| Protected clusters | `two-gap-isolation-after-filter-three.md` | Package redundant local clusters as a sufficient condition. |
| Bounded consecutive destruction | `two-gap-isolation-after-filter-three.md` | Bound runs of deleted 2-gap starts, not single-hit capacity. |
| Bounded post-merge spacers | `batched-short-window-discrepancy-boundary.md` | State a direct maximum-empty-arc condition. |
| Controlled merge runs | `absence-of-two-gaps-is-stable.md` | Combine deletion-run and prior-spacer bounds. |
| Balanced spacers | `exact-global-two-gap-count.md` | Convert average spacing into a candidate maximum-spacing bound. |
| Distinguished head spacer | `safe-window-two-gaps-certify-twin-primes.md` | Bound only the empty arc containing the head. |
| Forbidden-copy covered runs | `copy-index-filter-frequency.md` | State the covered-run bound needed for an eligible copy interval. |
| Short-window discrepancy | `batched-short-window-discrepancy-boundary.md` | State the error inequality that forces positivity. |
| Random-like merge survival | `short-window-discrepancy.md` and `two-gap-isolation-after-filter-three.md` | Combine a proved independent-random benchmark with an unproved deterministic transference condition. |
| Local pattern-residue balance | `copy-index-filter-frequency.md` and `random-like-merge-survival.md` | State deterministic, phase-sensitive balance of arbitrary finite gap words across residue classes. |
| Uniform local observable sampling | `random-like-merge-survival.md` and `two-gap-isolation-after-filter-three.md` | State deterministic unbiased sampling of arbitrary bounded local statistics by the actual hit set. |
| Hereditary shot-spacing capacity | `exact-accepted-local-filter-strikes.md`, `copy-index-filter-frequency.md`, and `local-surplus.md` | Use the exact numerical spacing of each future layer's shot train, conditioned on all earlier filters, rather than only a whole-window shot count. |

## Related Context

- `tickets/future/sieve-property-landscape.md`
- `tickets/active/sieve-sequence-property-catalog.md`
- `tickets/future/math-only-sieve-gap-survival-article.md`
- `tickets/active/deep-study-sieve-sequence-gap-dynamics-2026-07-23.md`
- `properties/sieve-sequence/README.md`

## Risks And Assumptions

- Risk: hypotheses may be mistaken for established theorems.
  - Mitigation: use the four-part status split in every file.
- Risk: the new folder duplicates the established catalog.
  - Mitigation: keep proofs of sufficiency short and cross-link established
    inputs rather than claiming new provenance.
- Assumption: `properties/` is reserved for established mathematical results,
  while `candidates/` is reserved for unproved and potentially false research
  hypotheses whose conditional consequences are still useful.
  - Validation: keep all additions under top-level `candidates/` and describe
    this boundary in its README.
- Hypothesis: a merge-oriented catalog makes the research boundary easier to
  compare than embedding all candidates in one long article.
  - Validation: use consistent notation and an index comparison table.

## Validation

- Confirm the index links to exactly fourteen candidate documents.
- Confirm every document contains hypothesis, conditional implication,
  established inputs, and limitation sections.
- Check relative links, fenced math balance, trailing whitespace, and duplicate
  headings within the new folder.
- Run `git diff --check` scoped to the new files where possible; do not modify
  unrelated dirty files.
- Markdown-only work requires no Stainless verification.

## Learning Log

- 2026-07-23: Ticket created after comparing the ten candidates with the
  existing property catalog. The collection will preserve one file per user-
  requested candidate while using status taxonomy and cross-links to avoid
  presenting overlapping established facts as new results.
- 2026-07-23: User clarified the epistemic boundary: `properties/` is for
  established results, while top-level `candidates/` is for unproved and
  potentially false hypotheses. Corrected the destination before creating the
  collection.
- 2026-07-23: Added `candidates/README.md` and ten standalone candidate notes.
  Every note distinguishes its unproved hypothesis, proved conditional
  implication, established inputs, and exact limitation.
- 2026-07-23: Semantic review tightened three preconditions: protected-cluster
  width now covers all four endpoints; a forbidden-copy batch must include
  every not-yet-installed prime below the target head; and the logarithmic
  average-spacer estimate is identified as an additional classical analytic
  input rather than a result established by the linked project notes.
- 2026-07-23: Validation passed for the new folder: one README plus ten
  candidate documents, all expected status/inputs/limitation sections present,
  no trailing whitespace, and scoped `git diff --check` clean. No Stainless run
  was required because all changes are Markdown-only.
- 2026-07-23: Added one combined random-like candidate rather than splitting
  the closely related ideas. The note proves the independent-random survival
  benchmark and separately states the unproved deterministic transference
  property needed to apply that benchmark to the actual sieve filter. The
  collection now contains eleven candidate documents.
- 2026-07-23: Semantic review separated two random benchmarks. Independent
  deletion gives destruction rate `2/p - 1/p^2` and independence across
  endpoint-disjoint gaps; a uniform random forbidden residue gives the more
  structurally faithful one-gap rate `2/p` but retains correlations across
  gaps. The gap-agnostic transference candidate now ranges over arbitrary
  local gap words and deletion-mark observables and specializes exactly to
  the required 2-gap destruction bound.
- 2026-07-23: Recovered two additional gap-agnostic formulations from the
  discussion: local pattern-residue balance and uniform local observable
  sampling. Bounded 2-gap endpoint bias will appear only as a specialization
  of observable sampling, and average merge size will appear only as an
  insufficiency boundary because neither warrants another candidate file.
- 2026-07-23: Added both recovered notes and expanded the index to thirteen
  candidates. Pattern-residue balance uses the number of distinct forbidden
  vertex-offset classes, including collisions when offsets agree modulo the
  incoming prime. Observable sampling handles the zero-hit case separately,
  fixes its endpoint count to one common boundary-safe anchor population, and
  derives bounded endpoint bias as a corollary. Validation passed for one
  README plus thirteen notes, relative links, required sections, math fences,
  control characters, trailing whitespace, and scoped diff integrity.
- 2026-07-23: Added hereditary shot-spacing capacity to the planned catalog.
  Unlike local surplus, it uses consecutive partial sums of the actual scaled
  shot-gap sequence at every future layer. The candidate obligation is that a
  shot-capacity surplus remains available after conditioning on all preceding
  filters in a fixed future square-safe window.
- 2026-07-23: Added and indexed the hereditary shot-spacing note as candidate
  fourteen. It proves the one-layer numerical capacity bound using half-open
  intervals and the minimum span of `k` shots, then clearly isolates the
  unproved hereditary obligation across the complete future filter chain. A
  bounded-incidence formulation extends the condition to arbitrary finite gap
  words. Semantic review and catalog validation passed for one README plus
  fourteen notes, links, required sections, fences, control characters,
  whitespace, and scoped diff integrity.
