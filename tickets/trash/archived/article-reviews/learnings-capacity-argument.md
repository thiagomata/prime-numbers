# Review: articles/learnings/learnings-capacity-argument.md

## Source

- Article: `articles/learnings/learnings-capacity-argument.md`
- Current role: Research notebook / boundary document

## Verdict

Excellent internal learning document. Do not publish as a polished article without restructuring.

## Must Fix

- Keep the "learnings" status explicit if public.
- Do not present the document as a final proof article; it is a boundary map and failed-approach record.
- Add source links or tickets for each item in the final proven-properties catalog.
- Convert Unicode symbols and casual phrasing to the house article style if publishing.

## Missing Proof Notes

The document contains several `[Proven]` or `[Verified]` claims that are useful as internal landmarks, but are not yet article-grade unless each one is tied to an exact current source proof or explicitly marked as mathematical reasoning:

- Filter bound: max `p - 1` strikes in `[p, p^2]`
- 2-gap isolation: no adjacent 2-gaps for `k >= 2`
- Single-target deletion: at most one 2-gap per strike
- Global growth: `T_{k+1} >= (p - 2) * T_k`
- 1-value rotation cycles residues uniformly across copies
- Once in the safe zone, a surviving 2-gap stays there
- Cluster survival conditions such as `C >= 2` within bounded width

Recommended fix: keep these in the learnings file as a research boundary map, but before importing any item into `gap-dynamics.md` or another final article, require one of the following labels:

- `[Verified]`: exact `.holds` function exists, source reference is present, and `verify.log` is green.
- `[Proven - math only]`: full English and LaTeX proof exists, but no Stainless proof exists yet.
- `[Empirical]`: backed by runner output or dataset, not a proof.
- `[Open]`: not proven, especially any local density claim equivalent to the Twin Prime Conjecture.

## Should Fix

- Extract the final catalog into `gap-dynamics.md` after verification labels are corrected.
- Preserve the failed approaches section because it is valuable reviewer armor.
- Add a short executive summary stating the exact formal boundary: global invariants proven, local density open.

## Validation

- Cross-reference Section 16 against `OBJECTS.md` and current source.
- Confirm any empirical claims cite a reproducible runner or dataset.
- Use this file as a guardrail for any article touching twin primes.
- For every `[Proven]` item, either link a current `.holds` function or create a proof ticket before publication reuse.

## Review Execution Log

### 2026-06-17: Review completed

**Resolution:** Content consolidated into existing published articles; file retained as internal reference.

**Actions taken:**
- Section 16 catalog (10 properties) → Integrated into `gap-dynamics.md` property index and summary table
- Section 10 (Fundamental obstacle) → Already frames `gap-dynamics.md` Section 6 (Open Local Density Question)
- Section 9 (Failed approaches) → Preserved in learnings file as reviewer armor; cross-referenced from `gap-dynamics.md` conclusion
- Section 15 (Formal boundary) → Cross-referenced from `integral-cycle.md` and `gap-dynamics.md`
- Section 17 (Structural impossibility of inter-prime window) → Kept in learnings file

**Note on future consolidation:** Negative learnings (failed approaches catalog, impossibility proofs like Section 17) may be grouped into a future article or sections documenting structural barriers within the sieve framework.

**Post-change verification:**
- `just verify` confirms: **5499 valid, 0 invalid, 0 unknown** ✅
- No Scala code modified — only article markdown edits
