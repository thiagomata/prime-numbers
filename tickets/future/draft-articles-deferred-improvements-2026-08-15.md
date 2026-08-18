# Deferred Draft-Article Improvements — Team Review Before Applying

**Origin:** Round-2 review loop of 2026-08-15
(`articles/draft/review-draft-articles-2026-08-15.md`). These items were
deliberately **not** applied in the round-2 fix pass: they are either
optional, low-priority, or outside the owner-approved fix list. Nothing below
has been applied to any article. The team should review, prioritize, and
approve or reject each item before a future pass touches the drafts.

| ID | Draft | Suggestion | Author disposition (round 1) |
|---|---|---|---|
| F1 | draft 5 | Add the one-line `ϑ_Z` derivation (among `p−1` units mod odd `p`, exactly one class makes `x+2` divisible by `p`) | Accept with qualification — low priority |
| F2 | draft 5 | Make `X₀(α)` explicit (`X ≥ 2^{1/(3α−1)}` suffices) | Accept — low priority |
| F3 | draft 5 | Remove the `<div align="justify">` wrapper from the abstract | Accept — low priority |
| F4 | draft 6 | Merge §7.2's `κ_r` analysis into §3 as a specialization of `w_r` (symbol unification; appendix A.3/A.4 may stay as the proof-record surface) | Accept with qualification — optional |
| F5 | draft 6 | Add theorem numbering / theorem-by-theorem premise table (beyond the header status line already added) | Accept with qualification — optional |
| F6 | draft 6 | Relocate the View A / View B heatmap discussion from the introduction to §8 or an appendix | Accept with qualification — optional |
| F7 | draft 6 | Add descriptive spread/trend reporting (range, quantiles, trend in `p`) for §8.1 deterministic data; no confidence intervals | Accept as descriptive enrichment — optional |
| F8 | draft 6 | Normalize figure metadata (commit/parameter provenance) across all charts, not only those that already embed it | Accept minor normalization — low priority |
| F9 | draft 6 | Relocate or shorten the §4.6 boundary-percentage table (pointwise-misuse risk) | Rejected as a defect; optional taste edit only |
| F10 | draft 6 | External citations for the random-sieve comparison class (Cramér 1936; Gallagher 1976), stated as comparison, not identity | Accept with qualification — medium priority |
| F11 | draft 4 | Convert §11 claims inventory into a status table (proved / conditional / empirical / open) | Accept with qualification — optional |
| F12 | draft 4 | (If §12 is further compressed later) also trim the successor formula list beyond the qualitative summary applied in round 2 | Accept with qualification — done once in round 2; revisit only if requested |
| F13 | draft 3 | Add a data-provenance block (checksums / archived paths) for the retained CSV and runner while they exist | Accept with qualification |
| F14 | draft 3 | Cite the Spark §4.6 cross-validation provenance before promoting that section into canonical successor docs | Accept |
| F15 | drafts 2+3 | Normalize math rendering to the repo standard (fenced `math` blocks; draft 2's `text` fences) | Accept with qualification — mechanical, low priority |
| F16 | draft 1 | Add the one-line recursive-step identity to the §2 induction sketch | Accept — low priority |
| F17 | draft 1 | Add a forward-map table to §7 distinguishing direct code dependencies from conceptual foundations (round-1 finding: only `assertPrimeNotDivisibleByDistinctPrime` is consumed externally) | Accept with qualification |
| F18 | draft 2 | Add a Task 1 hint (k-range `ceil(A/a) ≤ k < ceil(B/a)`) | Accept with qualification — low priority |
| F19 | draft 2 | Add one clarifying sentence to Task 3 on the both-endpoints-removed edge case | Rejected as a defect; at most one clarifying sentence |
| F20 | draft 2 | Cross-link the endpoint-disjoint variant (§5) to draft 4 §6 and the maintained candidate record | Accept — low priority |
| F21 | all | Shared notation/vocabulary map for head symbol and window conventions across drafts (`h` vs `p` vs `Q`; `[h,h²)` vs `[q,q²)` vs `[Q,Q²)`) | Rejected as a set-wide defect; optional vocabulary map |
| F22 | drafts 5+6 | Full theorem-numbering pass with statement environments and named premise lists (draft 5 got labels in round 2; numbering/packaging could go further) | Accept with qualification — optional |

## Verification debt (not an edit; a check)

| ID | Item | Status |
|---|---|---|
| V1 | Draft 6 §8.1 quoted statistics vs `data/candidates/*.csv` | In progress in the round-2 ticket; result will be recorded there |
| V2 | Draft 6 §8.1 per-sequence statistics vs `data/sieve-sequence/first_gaps_per_seq.csv` | Pending team decision on whether to verify before publication |
| V3 | Full proof-check pass over draft 6's remaining derivations (round-1 review verified representative proofs only) | Pending; recommended before any publication move |
