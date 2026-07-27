# Prove a Local Count Threshold for k=2 Shot Capacity

**Status:** Complete

**Depends on:**

- `tickets/active/prove-hereditary-shot-spacing-2026-07-23.md`
- `properties/sieve-sequence/interval-premise-from-pair-existence.md`
- `properties/sieve-sequence/stable-small-k-shot-spacing.md`

## START HERE

This ticket is complete. It proves that a sufficiently large ordered
population of complete 2-gap starts in `[Q,Q^2)` forces two consecutive starts
whose enclosing interval is shorter than `2r`. Composed with the existing
bounded-pair lemma, this gives candidate #14's `k=2` interval premise.

The required universal local population lower bound remains open. Resume only
through a focused follow-on ticket for a residue-class refinement, an
early-layer periodic-placement theorem, or a conditioned local-count bound.

## Goal

Add a mathematically proved property giving an explicit sufficient lower bound
on the number of complete local 2-gaps that forces candidate #14's `k=2`
shot-capacity premise at one conditioned filter layer.

## Strategy

Let

```text
Q <= x_1 < ... < x_N <= Q^2 - 3
```

be complete 2-gap starts and let `r>=5` be the incoming filter. If no
consecutive pair has enclosure shorter than `2r`, then every consecutive start
distance is at least `2r-2`. Summing those distances forces

```text
x_N - x_1 >= (N-1)(2r-2).
```

The square-window endpoint bounds independently give

```text
x_N - x_1 <= Q^2-Q-3.
```

The strict reverse inequality on the two right-hand sides therefore forces a
close pair. The existing bounded-pair property then supplies the `k=2`
interval premise using `sigma_r(2)=2r`.

This route is chosen because it is elementary, exact, and does not introduce a
short-window distribution assumption. A stronger residue-class refinement may
be considered only after this generic ordered-point lemma is complete.

## Current State

- The prior #14 investigation proves the capacity implication from a close
  pair but leaves close-pair existence open.
- Search found no existing property that derives close-pair existence from a
  local population count.
- The property
  `properties/sieve-sequence/local-count-forces-k2-shot-capacity.md` now proves
  the threshold

  ```text
  N >= floor((Q^2-Q-3)/(2r-2)) + 2.
  ```

- Independent validation passed:
  - `git diff --check` reports no Markdown whitespace errors;
  - every related link target exists;
  - 50,100 synthetic `(L,d)` cases confirm that the stated threshold is the
    first integer count forcing `(N-1)d>L`;
  - all 27 applicable stored lineage layers satisfy the antecedent, with
    minimum observed margin `+3` at `Q=17,r=7`.
- The property catalog now links the new result as item 17 and states the
  unresolved conditioned-count boundary.
- Candidate #14's "Partial proof result" section now links the theorem, displays
  the exact threshold, and preserves the unresolved local-count antecedent.
- The first post-property ticket update was applied after a discipline
  announcement but without the formal Worker/Critic/Monitor pre-execution
  blocks. Its content is current, but this is process attempt 1 and must not be
  repeated.

## What is Learned

- The strict complete-gap convention `x+2<Q^2` implies the integer endpoint
  bound `x<=Q^2-3`.
- Failure of the close-pair condition
  `x_{i+1}+2-x_i<2r` implies
  `x_{i+1}-x_i>=2r-2`.
- The result can be proved by telescoping consecutive start distances; it does
  not need complete-period CRT counts or probabilistic placement.
- The threshold is exact for arbitrary ordered points under only the endpoint
  bounds: one fewer point can be placed at spacing `2r-2`. This sharpness does
  not rule out a stronger sieve-specific threshold using the common residue
  class of post-filter-3 starts.
- The new sufficient count is not merely theoretical on the stored examples:
  it certifies every applicable Q17 and Q101 layer. This is finite
  corroboration, not a universal local-count theorem.
- Cataloging the theorem immediately after the bounded-pair lemma makes the
  dependency explicit: local count forces a close pair, and a close pair
  forces the `k=2` capacity premise.

## Failed Paths

- **Pipeline-format omission on the first state update.** The ticket was
  updated continuously as required, but the modifying action lacked the formal
  Worker/Critic/Monitor pre-execution blocks. The content did not fail; the
  execution protocol did. Retry only with the visible formal gate emitted
  before every subsequent modification.
- **First multi-file CSV aggregation.** It used `NR==1` instead of `FNR==1`,
  so the second file's header reached an awk string comparison and produced an
  inconsistent `min_margin=-3` despite zero reported failures. The corrected
  command skips each file's header with `FNR==1` and explicitly coerces numeric
  fields. Reuse only the corrected form for multi-file lineage summaries.
- Do not retry the prior unconditional inference from pair existence alone:
  two starts may be arbitrarily far apart. It becomes viable only with a
  quantitative count-and-window-width hypothesis such as the one used here.

## Open Concerns

- The floor-form threshold and `Q^2-3` endpoint have passed independent
  validation; future refinements must preserve the strict inequality rather
  than weakening it to equality.
- The resulting theorem is conditional on a local count. It must not be framed
  as proving hereditary #14 or twin-prime positivity.
- Stainless formalization may require a reusable sorted-list telescoping lemma
  not currently exposed by the Chapter 6 model. Mathematical promotion should
  not wait on inventing a new source representation.
- The worktree contains unrelated existing changes and deleted test files.
  This ticket must not alter or restore them.

## Next Action

Done. Any stronger theorem must begin in a new focused ticket and must not infer
short-window abundance from complete-period counts alone.

## Validation

1. Check the threshold algebra independently in both product and floor form.
2. Test equality-edge examples where
   `(N-1)(2r-2) == Q^2-Q-3`; equality must not force a close pair.
3. Cross-check the property against the recorded lineage populations without
   treating finite agreement as proof.
4. Run Markdown consistency and link checks. Markdown-only changes do not
   require Stainless verification.

All four checks passed. The corrected lineage aggregation covers 27 applicable
Q17/Q101 layers with zero failures, minimum margin `+3`, and maximum margin
`+419`.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | Existing #14 work proves close-pair capacity but has no local-count pigeonhole bridge. The strict window convention yields total available start range `Q^2-Q-3`. | Opened this focused ticket and selected the generic ordered-point threshold as the single first lemma. |
| 2026-07-27 | Added the mathematical property. Absence of a close pair forces `(N-1)(2r-2)<=Q^2-Q-3`; the floor threshold gives the strict opposite inequality. | Validate algebra, links, and finite lineage behavior before cataloging or extending the result. |
| 2026-07-27 | The first continuous ticket update omitted the formal pre-execution pipeline blocks even though the update itself was made at the correct time. | Recorded process attempt 1 in Current State and Failed Paths; require the full visible gate before every later modification. |
| 2026-07-27 | Independent validation passed: links and Markdown are clean; 50,100 floor-edge cases pass; the corrected lineage aggregation shows all 27 applicable Q17/Q101 layers exceed the threshold, minimum margin `+3`. The first aggregation was invalid because it skipped only the first file header. | Recorded the diagnostic failure and correction; selected one property-catalog entry as the next change. |
| 2026-07-27 | Added and validated property-catalog item 17. Candidate #14's partial-result section is the clean semantic location for one cross-reference. | Update candidate #14 with the exact count threshold, then return to the ticket before final validation. |
| 2026-07-27 | Candidate #14 now links the theorem and states its boundary. Final Markdown, link, floor-edge, and 27-layer lineage checks pass. | Marked the scoped work complete and moved this persistent-memory ticket to `tickets/done/`. |
