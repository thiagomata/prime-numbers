# Draft Articles — Round-2 Fixes from the 2026-08-15 Review

## Goal

Apply the agreed fixes from the review record
`articles/draft/review-draft-articles-2026-08-15.md` (original review + author
response + reviewer rejoinder + addendum) to the six draft articles. Markdown
only; no code, no data, no pipeline changes.

## Strategy

Follow the response's revised priority order:

1. Draft 3 factual corrections (urgent — verified against
   `data/empirical/results.csv`).
2. Draft 5 external positioning + apparatus.
3. Draft 6 status line, premise definition, abstract caveat (+ best-effort
   verification of §8.1 numbers).
4. Minor usability fixes in drafts 1, 2, 4.

## Change Log (Round 2) — every edit applied, for team audit

Scope rule: ONLY the fixes agreed in the review record and summarized to the
project owner on 2026-08-15. No other text is touched. Each row lists the
exact change; "verified" cites the data/source that justifies it.

### Draft 3 — `articles/draft/draft-empirical-g-local-analysis.md`

| # | Location | Change (old → new) | Verified by |
|---|---|---|---|
| 3.1 | Title | `[p,p^2)` → `[p,p^2]` (closed interval) | `SegmentedSieve.scala` strikes `m <= hi`, `hi = p*p` (review 3.A) |
| 3.2 | Abstract | `2-gaps in $[p,p^2)$ for primes through 997` → `$[p,p^2]$ for primes through 991` | CSV terminal row `k=167, p=991` (review 3.5) |
| 3.3 | Property Index row 1 | `up to $p=997$` → `up to $p=991$` | CSV |
| 3.4 | Property Index row 4 | `all 154 subsequent primes` → `all 155 subsequent primes` | `awk` count: 156 rows with p≥37, i.e. 155 after p=37 (review 3.5) |
| 3.5 | §2.1 | add one sentence: closed at p² because p² has no prime divisor < p, so it survives the installed filters | review 3.A |
| 3.6 | §2.4 Range | `All 166 primes from $p=3$ to $p=997$ (the largest prime ≤ 1000)` → `All 166 primes from $p=3$ to $p=991$; the terminal row's next prime is 997 (the largest prime ≤ 1000)` | CSV |
| 3.7 | §3.1 | `for all 154 subsequent primes` → `for all 155 subsequent primes` | CSV count |
| 3.8 | §3.2 table, 5 rows | `353: 1484/+1125/4.20/3.19` → `1448/+1095/4.10/3.10`; `607: k=112, 3590/+2977/5.91/4.90` → `k=111, 3539/+2932/5.83/4.83`; `739: k=132, 4935/+4192/6.68/5.67` → `k=131, 4892/+4153/6.62/5.62`; `881: k=153, 6581/+5698/7.47/6.47` → `k=152, 6558/+5677/7.44/6.44`; `997: k=168` → `991: k=167` (G/δ unchanged: 8016/+7025) | CSV rows at those primes — values in the draft did not match the retained data (new finding during round 2) |
| 3.9 | §3.2 text | `increases monotonically (with one small fluctuation, see Section 3.3)` → `increases ... with five small dips, each occurring at a transition between twin primes (see Section 4.4)` | recomputation: 5 non-increasing G/p steps, all at twin-prime transitions (review addendum 3.C) |
| 3.10 | §3.3 | `for all remaining 153 primes` → `for the remaining 146 primes` | `awk` count: 146 rows with p>73 (review 3.5) |
| 3.11 | §3.5 | `covered 166 primes from $p=3$ through $p=997$` → `through $p=991$` | CSV |
| 3.12 | §4.1 | irreproducible fit `0.0071·p + 0.97 (R²>0.99)` → reproducible descriptive OLS over the 156 post-crossover rows `0.00701·p + 1.44 (R² = 0.992)`; extrapolation endpoints recomputed from the reproducible fit (p≈1220, p≈14100) | OLS recomputed from CSV (review 3.B) |
| 3.13 | §4.3 | wrong density denominator fixed: ρ_k = ∏(p_i−2)/(p_i−1) (per-coprime) → per-integer density (1/2)∏(1−2/p_i) = G₂/M; expected count uses window length p²−p+1; "exceeds ... by a factor of approximately 2-3" → data is consistent with the uniform estimate (sampled ratios 0.94–1.04 at p=31,101,503,991); earlier excess identified as the denominator artifact | recomputation (review 3.3); cross-checks §4.6 which already used G₂/M |
| 3.14 | §4.4 final sentence | `This pattern does not recur for any other adjacent pair in the dataset.` → the G/p dip recurs at every twin-prime transition (71→73, 107→109, 191→193, 269→271, 461→463); the δ dip at 71→73 remains unique for δ | recomputation (review addendum 3.C) |
| 3.15 | §5.1 table | `holds for all 154 subsequent primes tested` → `155` | CSV count |
| 3.16 | §5.2 | `($3 \le p \le 997$)` → `($3 \le p \le 991$)` | CSV |
| 3.17 | Sweep (§ superseded-note, §2.5, §4.2, §5.3) | 5 further instances of the same two patterns fixed: `[p,p^2)` → `[p,p^2]$` (header note, §2.5, §5.3) and `at $p=997$` / `up to $p=997$` → `991` (§4.2 δ/p endpoint, §5.3 inequality) | CSV; grep-verified no remaining instances |

**Status: draft 3 DONE (2026-08-15).** Post-edit grep confirms no remaining
`997`-as-measured-prime or `[p,p^2)` instances.

**Status: draft 5 DONE (2026-08-15).** Change log (matches rows 5.1–5.3):
- New `### 1.2 Relation To Known Results` positioning Chen/H-R/I-K/F-I,
  what is standard vs project-specific, parity barrier as context-not-identity
  (row 5.2).
- New vocabulary block at the top of §2 defining P2, lower-bound sieve,
  Type-I, Type-II (row 5.1).
- Theorem 1–5 statement labels inserted at the head of §§3–7; the existing
  scope paragraphs and proofs are unchanged (row 5.3).
- References: four external entries added as [7]–[10] with anchors; existing
  internal refs 1–6 untouched (row 5.2).

### Draft 5 — `articles/draft/draft-relaxed-almost-prime-sieve-sequence.md` (planned rows below; status above)

| # | Location | Change | Review item |
|---|---|---|---|
| 5.1 | §2 (Preliminaries) | add definitions of P₂, Type-I / Type-II estimates, and the lower-bound-sieve role | 5.2 (Accept) |
| 5.2 | References | add external bibliography: Chen 1973; Halberstam–Richert 1974; Iwaniec–Kowalski 2004; Friedlander–Iwaniec 2010; plus a positioning note (standard machinery vs project-specific parts; parity barrier as context, not identity) | C1/5.1 (Accept with qualification) |
| 5.3 | §§3–7 | label the five main results Theorem 1–5 with premise lists (content unchanged) | 5.3 (Accept) |

### Draft 6 — `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md`

| # | Location | Change | Review item |
|---|---|---|---|
| 6.1 | Header | add Status line (draft; companion theorems proved under stated premises; Stainless pending; date) — mirrors §1.1, no new claims | C3/6.3 |
| 6.2 | §2.1 Notation | one-place definition of the blind-placement empty-window premise (Pr(X_Q=0) ≤ e^{−λ_Q} as an explicit assumption); no other text changed | 6.1 (small clarification) |
| 6.3 | Abstract | one sentence: real-sieve transfer premises (availability, mixing/placement, deterministic discrepancy) remain unproved | 6.6 (Accept with qualification) |
| 6.4 | §8.1 (no edit) | VERIFIED, no change needed. Per-transition: 187 distinct transitions p=3..19429, 186 below 2/p, p=3 equal, 95 zero-destruction, max w=0.0523 (at p=1231) — all exact. Per-sequence: 188 covered heads 3..1129, mean ratio 0.9666 ("0.967"), largest head 0.947 with 10,056 vs 10,616 — exact under the chart script's own convention. Full-cycle: products 0.3733 / 0.003676, ratio 101.5 ("about 102") — exact. Fixed cohorts: c_eff ∈ [−0.035273, 0.009074]; stated bounds [−0.0353, 0.00908] are true (top end not tight by 1 rounding ulp; left as-is) | recomputation from `data/candidates/*.csv`, `data/sieve-sequence/first_gaps_per_seq.csv`, and `python/src/sieve_sequence/per_sequence_frontier_chart.py` conventions |

**Status: draft 6 DONE (2026-08-15).** Rows 6.1–6.3 applied exactly as
planned; row 6.4 verified with zero article changes required.

### Draft 1 — `articles/draft/draft-sieve-foundation.md`

| # | Location | Change | Review item |
|---|---|---|---|
| 1.1 | Header | add author/date lines (status line already present) | 1.2 (Accept) |
| 1.2 | §5 | retitle as a corollary of §4 (same lemma, filter reading); both Scala blocks kept — presentation change only, no code/source changes | 1.1 (Accept with qualification) |

**Status: draft 1 DONE (2026-08-15).**

- 1.1: author/date lines added below the existing status line.
- 1.2: §5 retitled "Corollary: The Filter Reading"; intro rewritten to state
  it is the same proposition as §4 with the argument renamed (verified Scala
  wrapper kept); §7 opening now says "five verified properties — four
  substantively distinct lemmas, with §5 as the filter-reading corollary of
  §4". Both Scala blocks and all source links unchanged.

### Draft 2 — `articles/draft/exercise-local-safe-window-capacity.md`

| # | Location | Change | Review item |
|---|---|---|---|
| 2.1 | Header | add date/author lines | 2.1 (Accept with qualification) |
| 2.2 | Appendix (new) | short solution sketches (one paragraph per task) | 2.1 |

**Status: draft 2 DONE (2026-08-15).**

- 2.1: author/date added to the status front matter.
- 2.2: new "Appendix: Solution Sketches" with one paragraph per task
  (Tasks 1–4 + the endpoint-disjoint variant); Task 3 sketch includes the
  both-endpoints-removed double-counting note as part of the sketch.

### Draft 4 — `articles/draft/draft-sieve-gap-survival-math.md`

| # | Location | Change | Review item |
|---|---|---|---|
| 4.1 | §12 | replace the formula dump with a qualitative summary + link to the successor article (gap-dynamics-v2) | 4.1 (Accept with qualification) |
| 4.2 | Reference [3] | mark the linked empirical draft as superseded | 4.3 (Accept) |
| 4.3 | §10 sentence | label the "empirical work has observed" appeal as historical/superseded | 4.4 (Accept) |

**Status: draft 4 DONE (2026-08-15).**

- 4.1: §12 formula dump replaced by a qualitative three-point summary
  (exact accepted strikes; weighted quadratic threshold; residue-energy
  reduction) with an explicit delegation link to gap-dynamics-v2; the
  candidate-#25 paragraph retained, also de-formulaized.
- 4.2: reference [3] now labeled "(superseded draft)".
- 4.3: §10 empirical sentence relabeled "Historical observation only" citing
  the superseded [p,p²] experiment and stating the canonical [q,q²) data do
  not measure A_h. The two non-agreed sentences that close that passage
  ("The missing theorem is not a full-period CRT statement...") were briefly
  dropped by mistake and restored — final text preserves them.

### Explicitly NOT done in this loop (deferred — team review required)

All deferred, optional, or out-of-loop improvement suggestions were moved to
`tickets/future/draft-articles-deferred-improvements-2026-08-15.md` (items
F1–F22, verification debt V1–V3). They must be reviewed and approved by the
team before any future pass applies them. Nothing from that file was applied
in this round.

## Current State

- [x] Review record complete; all disagreements closed.
- [x] Draft 3 fixes applied (17 logged changes; post-edit grep clean).
- [x] Draft 5 fixes applied (vocabulary, positioning, Theorems 1–5, refs).
- [x] Draft 6 fixes applied (status line, premise definition, abstract
      caveat) and §8.1 verified with no change required.
- [x] Drafts 1/2/4 minor fixes applied.
- Ticket ready for team audit; deferred suggestions live in
  `tickets/future/draft-articles-deferred-improvements-2026-08-15.md`.

## What is Learned

- Draft 3's §3–§4 prose was not written from the retained CSV; six
  independent claims failed against it (terminal row p=991 mislabeled p=997;
  range [3,991] not [3,997]; counts 156/146 not 154/153; closed interval
  [p,p²]; wrong density denominator φ(M) vs M; G/p has 5 dips, not 1).
  During the fix pass a seventh failure was found: five rows of the §3.2
  growth table (p=353, 607, 739, 881, terminal) did not match the CSV.
- Reproducible OLS: all 166 rows slope 0.0072095 / intercept 1.30817 /
  R² 0.98851; p≥37 (156 rows) slope 0.0070056 / intercept 1.44082 /
  R² 0.99186. Printed 0.0071p+0.97 matches neither.
- With the correct per-integer density (G₂/M), draft 3's data matches the
  uniform estimate within 0.94–1.04 at sampled heads — the reported
  "2–3× excess" was purely the denominator error.
- Draft 6 §8.1's quoted statistics all verify against the CSVs, including
  the mean ratio 0.967 (exact value 0.9666 under the chart script's own
  boundary convention — replicating the script's logic matters; a naive
  gap-walk gives 0.9716).

## Failed Paths

- (Round 1 of the review) Trusting the draft's own summary statistics without
  checking the CSV — do not repeat; every §3–§4 number must come from the CSV.
- (This pass) Reconstructing per-sequence windows with a naive gap-walk
  instead of the generating script's survivor-set convention produced a
  slightly different mean (0.9716 vs 0.9666); always mirror the script's
  exact counting rule when verifying published numbers.

## Open Concerns

- None blocking. Verification debt for the remaining unverified draft-6
  derivations is recorded as V2–V3 in the deferred-improvements file.

## Next Action

Team audit of the change log; then decide on the F1–F22 deferred items.

## Learning Log

| Date | Entry |
|---|---|
| 2026-08-15 | Ticket created from the round-1 review record; priority order taken from the author response's revised list. |
| 2026-08-15 | Draft 3 fixed from fresh CSV recomputation; 7th failure (growth-table rows) found and fixed; grep confirms no stale instances remain. |
| 2026-08-15 | Draft 5: §1.2 positioning, §2 vocabulary, Theorems 1–5, external refs [7]–[10]. |
| 2026-08-15 | Draft 6: status/premise/abstract edits; §8.1 fully verified against data (per-transition, per-sequence, full-cycle, fixed cohorts) — no change needed. |
| 2026-08-15 | Drafts 1/2/4 minor fixes applied; one accidental over-deletion in draft 4 §10 restored immediately; deferred suggestions moved to tickets/future for team review. |
