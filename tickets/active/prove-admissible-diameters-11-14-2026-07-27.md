# Prove Admissible Diameters D(11) Through D(14)

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete
**Depends on:** `develop-admissible-shot-spacing-candidate-2026-07-27.md`

## START HERE

Replace the exhaustive no-smaller-pattern searches for

```math
D(11)=36,\quad D(12)=42,\quad D(13)=48,\quad D(14)=50
```

with compact, reviewable residue-cover certificates. The explicit admissible
patterns already prove the upper bounds. The only missing direction is that
every normalized pattern of smaller diameter covers all residues modulo at
least one prime `p<=k`.

## Goal

Prove the four proposed admissible diameters exactly and promote them from
candidate #15 into the fixed-`k` spacing property. If a compact certificate
cannot be obtained after three distinct proof attempts, stop with the exact
remaining obstruction recorded.

## Strategy

Normalize every candidate pattern to contain `0`. Admissibility modulo `2`
forces all offsets even. Use the already proved monotonic lower bound
`D(k)>=D(10)=32`, so only even diameters from `32` up to the proposed value
need consideration.

Compress the remaining cases through residue masks rather than listing
millions of subsets:

1. reject patterns covering all residues modulo `3`;
2. classify the survivors by their missing modulo-3 class;
3. reject them with modulo `5`, `7`, `11`, or `13`;
4. express the result as finite mask/count tables or a short family
   parametrization that a reader can audit.

## Current State

- The upper witnesses are already proved admissible:
  - `k=11`, diameter `36`;
  - `k=12`, diameter `42`;
  - `k=13`, diameter `48`;
  - `k=14`, diameter `50`.
- Exhaustive normalized searches found no smaller admissible pattern.
- The raw searches tested respectively
  `24,037`, `217,594`, `1,691,308`, and `3,251,477` patterns.
- Those search counts are evidence, not yet the compact mathematical
  certificate required for `properties/`.
- Attempt 1 found a compact certificate. For missing classes
  `a in {1,2}` modulo `3` and `b in {1,2,3,4}` modulo `5`, define

  ```math
  U_d(a,b)=
  \{x\in\{0,2,\ldots,d-2\}:x\not\equiv a\pmod3,\
  x\not\equiv b\pmod5\}.
  ```

  Every normalized pattern surviving modulo `3` and modulo `5` is a
  `k`-subset of at least one `U_d(a,b)`.
- For `k=11,d=36`, all eight sets have fewer than `11` elements, so no
  pattern survives both primes.
- Across `k=12,13,14`, only 14 sets have size at least `k`. Thirteen have
  exactly `k` elements and therefore force the whole set. The remaining case
  is `k=13,d=48,a=2,b=3`, where `|U|=14`; its modulo-7 multiplicity vector is
  `(2,2,2,2,2,2,2)`, so deleting any one nonzero point still leaves all seven
  residues represented.
- Every one of the thirteen forced sets also has a strictly positive count in
  every modulo-7 residue class. Therefore every survivor through primes `3`
  and `5` covers modulo `7`, completing all four lower bounds.
- The complete certificate and the four upper-witness missing-residue rows
  are now in
  `properties/sieve-sequence/stable-small-k-shot-spacing.md`. The property
  proves `D(11)=36`, `D(12)=42`, `D(13)=48`, and `D(14)=50`.
- Candidate #15 and the property/candidate catalogs now classify the exact
  profile through `k=14` as proved. The candidate retains only the genuinely
  open recurrence, scalable-bound, and extremal-classification program beyond
  that range.
- A final independent exhaustive audit checked the complete normalized even
  domains strictly below the four target diameters:
  - `19,448` patterns for `k=11`;
  - `167,960` patterns for `k=12`;
  - `1,352,078` patterns for `k=13`;
  - `2,496,144` patterns for `k=14`.
  Every pattern covered all residues modulo at least one prime `p<=k`, and all
  four upper witnesses passed direct admissibility checks.
- The earlier larger search-work counts include the discovery search's work
  within the first successful diameter. The final validation counts above are
  the exact domains strictly below each claimed optimum.

## What is Learned

- Only primes `p<=k` can obstruct a `k`-point pattern; larger primes cannot be
  fully covered.
- Parity and the exact `D(10)=32` lower bound drastically reduce the diameter
  range.
- The prior `D(2)..D(10)` proof succeeded because modulo `3` left at most 20
  cases. For `k=11..14`, a stronger compression may be needed.
- Pairing the missing classes modulo `3` and `5` turns the search into eight
  small ambient sets per diameter. Cardinality alone eliminates nearly all
  rows; modulo-7 multiplicities eliminate the remainder.
- The certificate does not need the original millions-of-pattern search or a
  recurrence implementation. It consists only of explicit finite sets,
  cardinalities, and residue multiplicities.

## Failed Paths

- **Treat exhaustive search output as the final proof.** Rejected by the
  project’s strict property boundary: the lower reason must be exposed as
  residue-cover algebra. Retry only after producing a compact certificate or
  independently verified proof artifact.
- **First prose count of viable ambient sets.** The initial promotion said
  thirteen viable rows and twelve forced rows, but the displayed table has
  fourteen viable rows: thirteen forced and one larger row. Corrected before
  proceeding; the residue sets and mathematical conclusion were unchanged.
- **Property-catalog edit emitted before the visible pre-execution gate.**
  The Markdown content was correct, but the required protocol ordering was
  missed for that one edit. Recorded immediately, not repeated, and included
  in the final diff and consistency checks.

## Open Concerns

- No mathematical concern remains for `D(11)..D(14)`.
- Unrelated shared-worktree test deletions/modifications and analysis changes
  remain outside this ticket and were preserved.

## Next Action

Done. A separate future ticket may pursue `D(k)` beyond `k=14`, recurrence
inequalities, or optimal-pattern classification.

## Validation

- Every promoted lower bound must cover all normalized smaller patterns.
- Each rejected family must name a prime whose residue classes are complete.
- Markdown-only edits require `git diff --check`; no Stainless verification is
  claimed.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-27 | User selected follow-on option 1: compact lower certificates for `D(11)..D(14)`. | Opened this focused ticket and selected residue-mask compression as attempt 1. |
| 2026-07-27 | The paired missing-class sets `U_d(a,b)` leave only 14 viable rows; modulo `7` rejects all of them. | Accepted attempt 1 and advanced to formalizing the exact four values. |
| 2026-07-27 | Promoted the four exact values with explicit upper and lower certificates. The first prose count was corrected from 13 to 14 viable rows before proceeding. | Advanced to candidate and catalog alignment. |
| 2026-07-27 | Candidate #15 and both catalogs now mark the profile through `k=14` proved. One catalog edit missed the visible pre-gate ordering; the omission was recorded and not repeated. | Ran the final independent exhaustive audit and `git diff --check`. |
| 2026-07-27 | All four witnesses and every normalized shorter even pattern passed the independent audit; no stale unresolved-profile claim remains in the promoted artifacts. | Marked the focused ticket complete. |
