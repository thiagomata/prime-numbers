# Document the Incremental Danger Annulus

**Created:** 2026-08-05

**Updated:** 2026-08-05

**Status:** Complete

**Related:**

- `quantifier-screen-refutation-targets-2026-08-03.md` — completed candidate
  closure audit whose handoff wording was synchronized with the annular
  refinement.
- `local-safe-window-capacity-exercise.md` — earlier safe-window capacity work.
- `prove-local-count-forces-shot-capacity-2026-07-27.md` — earlier local-count
  and strike-capacity route.

## START HERE

Synchronization is complete. The Danger-Annulus Decomposition property is the permanent source for the
distinction between the full square-safe window and the newly exposed danger
annulus. No annular 2-gap lower bound is claimed; resume only through one of the
explicit theorem triggers in `Next Action`.

## Goal

Correct the permanent property and candidate record to distinguish inherited
safe territory from values newly exposed between consecutive prime squares.
Propagate the distinction through the exact accepted-strike property,
candidate #2, candidate #16, and the closure handoff without overstating the
result as a proof of local 2-gap population or as a replacement for the current
#23 -> #24 frontier.

## Strategy

Keep the existing square-safe window `W_q=[q,q^2)` because it remains the
correct certification region. Add a parallel incremental formulation for
consecutive primes `p<q`: accepted strike values use the annulus
`V_{p,q}=[p^2,q^2)`, while gap-start intervals account for the gap width and
the forced composite boundary. Use the exact accepted-strike count when
available and record the raw annular multiple count only as a simpler upper
bound.

## Current State

- Documentation synchronization is complete. The Danger-Annulus Decomposition property, the exact-strike
  corollary, candidates #2 and #16, the property catalog, the authoritative
  closure matrix, and the candidate handoff now use compatible annular
  definitions and theorem boundaries.
- The square-safe certification property correctly uses the full window
  `[q,q^2)` and should not be replaced.
- The exact accepted-strike property now states that every accepted filter-`p`
  strike value in the full window lies in `[p^2,q^2)` and records the matching
  annular raw capacity.
- Separating viable annular starts also reveals one compulsory harmless strike:
  `p^2` is included in the accepted-strike count but cannot touch a viable
  newly exposed 2-gap.
- Candidate #2 now separates its valid full-window count from the refined
  pre-filter annular population.
- Candidate #16 now calls `[q,q^2)` the square-safe target and uses separate
  post-filter full-window and pre-filter annular observables.
- The closure matrix now records the annular refinement as a quantified reopen
  path for #2 and #16 without claiming their missing local lower bound.
- The permanent [incremental danger-annulus decomposition](../../properties/sieve-sequence/incremental-danger-annulus-decomposition.md)
  now proves the value/start decomposition, phase-compatible coordinate set,
  accepted-strike confinement, raw annular count, and effective `A-1`
  destruction bound. Positivity of `L_D(p,q)` remains open.
- `properties/sieve-sequence/exact-accepted-local-filter-strikes.md` now
  preserves its full-window theorem while recording annular confinement,
  equality of full and annular accepted counts, `A<=R_V`, and the
  refined-population-only bound `K_D<=A-1`.
- `candidates/local-surplus.md` now preserves its original full-window
  condition while adding the exact `L_D>A-1` and raw `L_D>R_V-1` incremental
  forms. It proves only their conditional implication and states that the
  existing 186-transition dataset does not measure `L_D`.
- `candidates/expanded-zone-exterior-capacity.md` now calls `W_q` the
  square-safe target, preserves its post-filter `S_q` exterior argument, and
  adds a separate pre-filter `S_{<p}` annular construction for consecutive
  primes `p<q` with `p>=5`. It derives `L_D>=B_D-U_D` and leaves the favorable
  expansion and population bounds open.
- `properties/sieve-sequence/README.md` now catalogs the foundational result as
  The Danger-Annulus Decomposition property, including its preconditions, distinct coordinate/population
  meanings, effective `A-1` bound, and open `L_D` lower bound.
- `candidates/INVESTIGATION_STATUS.md` now synchronizes rows #2 and #16 with
  The Danger-Annulus Decomposition property, records complete surplus/exterior reopen conditions, and
  classifies the route within the deferred local-mechanism family while
  preserving #23 -> #24 as primary.

## What is Learned

- For consecutive primes `p<q`, the accepted-value danger annulus is

  ```math
  V_{p,q}=[p^2,q^2).
  ```

- For a gap of width `h`, the newly exposed gap-start interval is

  ```math
  D^{(h)}_{p,q}=[p^2-h,q^2-h).
  ```

  The lower boundary start `p^2-h` has upper endpoint `p^2` and is certainly
  destroyed by filter `p`. Every post-filter-3 2-gap start is congruent to `5`
  modulo `6`, while every prime `p>=5` has `p^2` congruent to `1` modulo `6`.
  Thus the boundary start `p^2-2` is killed at `p^2`, and the next
  arithmetically possible start is `p^2+4`. Potentially surviving newly
  exposed 2-gap starts satisfy `x` congruent to `5` modulo `6` within the
  bounding interval

  ```math
  [p^2+4,q^2-2).
  ```

- Every accepted filter-`p` strike value in `[q,q^2)` is at least `p^2`.
  Therefore the exact accepted-strike counts agree as strike-value counts:

  ```math
  A_{full}(p,q)=A_{danger}(p,q).
  ```

  This equality does not assert equality of full-window and annular 2-gap
  populations.

- With `d=q-p`, the exact number of raw multiples of `p` in the accepted-value
  annulus is

  ```math
  R_V(p,q)
  =
  \left\lceil\frac{q^2-p^2}{p}\right\rceil
  =
  2d+\left\lceil\frac{d^2}{p}\right\rceil.
  ```

- Let `K_D(p,q)` count pre-filter 2-gaps destroyed by filter `p` whose starts
  are congruent to `5` modulo `6` in `[p^2+4,q^2-2)`. The exact accepted count
  `A(p,q)` includes the strike `p^2=p*p`, but that strike is not an endpoint of
  any gap in this refined population. Post-filter-3 endpoint isolation gives

  ```math
  K_D(p,q)
  \le A(p,q)-1
  \le R_V(p,q)-1
  =2d+\left\lceil\frac{d^2}{p}\right\rceil-1.
  ```

  These are upper bounds on destroyed refined-annular 2-gaps, not lower bounds
  on the annular population.

- After filter `3`, endpoint isolation makes one accepted strike destroy at
  most one 2-gap. Fixed 4-gaps are also endpoint-isolated after filter `3`:
  adjacent 4-gaps would require `x`, `x+4`, and `x+8`, which cover all
  residues modulo `3`. Fixed 6-gaps can share an endpoint. Each gap width
  therefore needs an explicit isolation or multiplicity property before the
  2-gap capacity argument is reused.
- The missing ingredient remains a proved lower bound for the number of
  pre-filter 2-gaps in the annular start interval. Complete-period density does
  not provide that localization when the annulus is shorter than one period.
- The permanent danger-annulus property is the source of truth for
  `V_{p,q}`, `X_D(p,q)`, `L_D(p,q)`, and `K_D(p,q)`. Later property and
  candidate updates should reuse these definitions rather than introduce
  incompatible interval conventions.
- The exact-strike note is now a synchronized corollary of that source rather
  than a competing definition of the annular population.
- Candidate #2 now separates full-window survival from newly exposed survival;
  neither its historical measurements nor the annular capacity bound supplies
  the still-open lower bound for `L_D`.
- Candidate #16 now keeps post-filter full-window and pre-filter annular
  observables at distinct layers. Its smaller destruction allowance is paired
  with a smaller population and is not known to make localization easier.
- the Danger-Annulus Decomposition property is now the cataloged permanent boundary for annular reuse; it
  sharpens the capacity side without satisfying the population-side reopen
  trigger.
- The authoritative closure matrix treats the annular route as a quantified
  reopen path, not a fourth active front or a solved reopening.

## Expected State

- A foundational property records the exact inherited-safe/danger-annulus
  decomposition and endpoint discipline.
- The exact accepted-strike property states annular confinement and the raw
  capacity formula without confusing raw and accepted strikes.
- Candidate #2 includes an incremental annular surplus formulation alongside
  its valid full-window formulation.
- Candidate #16 uses “square-safe target window” for `[q,q^2)` and
  “incremental danger annulus” for `[p^2,q^2)`.
- The candidate catalog and closure matrix record this as a sharper local route
  whose annular population theorem remains open; #23 -> #24 remains the primary
  established twin-prime frontier.

## Alternatives Considered

- **Replace every full-window definition with the annulus:** rejected because
  `[q,q^2)` remains the correct square-safe certification window and existing
  theorems stated on it are valid.
- **Treat full-window density as annular density:** rejected because periodic
  repetition gives exact counts only over complete periods, while late
  annuli are shorter than the old primorial period.
- **Use only the raw multiple count:** retained only as a simple sufficient
  bound; the exact accepted-strike count is generally sharper.
- **Recompute empirical tables immediately:** deferred. The current change is
  about structural definitions and theorem targets, not new finite evidence.

## Assumptions and Validation

- `p<q` are consecutive primes and the transition installs filter `p`.
- Intervals are half-open and gap intervals are indexed by their starts.
- Old filters contain every prime below `p`.
- Post-filter-3 2-gaps are endpoint-disjoint.
- Validate formulas at the interval endpoints and distinguish counts of values
  from counts of gap starts.
- Validate Markdown with `git diff --check` and verify all relative links.
- No Scala, Python, or executable instruction is changed, so no runtime gate is
  required.

## Failed Paths

- **Global-density localization:** complete-period 2-gap proportions do not
  force a positive count in a shorter annulus. Retry only if a proved
  short-interval discrepancy or maximum-empty-arc bound becomes available.
- **Full-window surplus as incremental production:** the full count may include
  already certified territory below `p^2`. Retry only after separating the
  inherited and annular populations.
- **Complete combined-period slice inside the annulus:** the combined period is
  eventually much larger than the square-scale annulus. Retry only with a
  smaller exact block decomposition or a rigorous exterior subtraction.

## Open Concerns

- The annular population lower bound may remain twin-prime-strength despite
  the much smaller raw destruction capacity.
- Candidate #16 has no constructed annular expansion with favorable bounds
  `B_D,U_D`; the corrected notation does not supply that missing theorem.
- The generic `h`-gap decomposition is valid, but destruction multiplicities
  for 4- and 6-gaps require separate properties.

## Next Action

No documentation action remains for this ticket. Future mathematical work may
reopen the annular route only after supplying one of these theorem inputs for a
recurring family:

```math
L_D(p,q)>A(p,q)-1,
```

paired independent estimates

```math
L_D(p,q)\ge B(p,q),
\qquad
K_D(p,q)\le H(p,q),
\qquad
B(p,q)>H(p,q),
```

or a constructed annular exterior expansion proving

```math
B_D-U_D>A(p,q)-1.
```

These are explicit reopen triggers, not unfinished documentation. Candidate
#23 -> #24 remains the primary established twin-prime continuation.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-05 | Previous-stage square certification separates inherited-safe territory from the newly exposed annulus. Accepted strike values and gap starts require different interval endpoints. | Open this focused documentation ticket and add the foundational annulus property before changing candidates or closure classifications. |
| 2026-08-05 | The coarse potential-start interval included forced boundary cases and ignored the post-filter-3 residue phase. Viable starts satisfy `x` congruent to `5` modulo `6` within `[p^2+4,q^2-2)`. | Correct the persistent endpoint record before drafting the permanent property. |
| 2026-08-05 | The compulsory accepted strike `p^2` cannot touch the refined annular population, so effective destruction is bounded by `A-1`, and hence by `R_V-1`. | Require the permanent property and candidate #2 refinement to use the sharper effective capacity. |
| 2026-08-05 | The permanent danger-annulus property now records the decomposition and sharp effective capacity while leaving annular population open. | Synchronize the exact accepted-strike note with the new source-of-truth definitions. |
| 2026-08-05 | The exact-strike note now records the annular corollary. Its first patch attempt was a no-op because the expected context did not match the fresh file; rereading the target allowed the same approved change to apply at the correct location, and validation passed. | Refine candidate #2 with the exact and raw incremental surplus forms. |
| 2026-08-05 | Candidate #2 now separates full-window and newly exposed survival, and explicitly prevents transferring its historical full-window measurements to `L_D`. | Correct candidate #16's danger-zone terminology and add the parallel annular exterior target. |
| 2026-08-05 | Candidate #16 now cleanly separates its valid post-filter full-window route from a pre-filter annular alternative, with preconditions matching the foundational property. | Catalog the permanent danger-annulus result as the Danger-Annulus Decomposition property. |
| 2026-08-05 | Ticket review found stale pre-change descriptions of candidates #2 and #16 after their permanent notes had already been corrected. | Synchronize Current State and Open Concerns before cataloging the Danger-Annulus Decomposition property. |
| 2026-08-05 | A second consistency review found the same stale pre-change wording for the already-synchronized exact accepted-strike property. | Correct the final contradictory Current State bullet before continuing. |
| 2026-08-05 | The property catalog now exposes the annular decomposition and sharp effective capacity as the Danger-Annulus Decomposition property, with `L_D` abundance explicitly open. | Synchronize the authoritative candidate closure matrix. |
| 2026-08-05 | The closure matrix now records the quantified annular reopen path while preserving #23 -> #24 as primary. Its first patch attempt was a no-op context mismatch; rereading the exact table allowed the approved same-target retry to pass. | Perform a narrow candidate-catalog consistency update. |
| 2026-08-05 | Post-update review found one remaining negative pre-change closure sentence despite the completed matrix synchronization. | Correct the stale sentence and audit Current State before touching the catalog. |
| 2026-08-05 | The candidate catalog now distinguishes full-window evidence from the unmeasured annular targets, records #16's pre-filter alternative, and preserves the primary handoff. Scoped Markdown, link, terminology, and status checks passed without touching unrelated dirty or untracked work. | Mark the documentation ticket complete; retain the population and exterior inequalities as future theorem triggers. |
| 2026-08-05 | Final cold-reader review found stale imperative wording in `START HERE` and a future-tense related-ticket description after completion. | Convert the header guidance to completed-state handoff language and point future work only to the explicit theorem triggers. |
