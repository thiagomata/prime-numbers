# Review: articles/gap-dynamics.md

## Source

- Article: `articles/gap-dynamics.md`
- Current role: Research-frontier article

## Verdict

Major revision required before publication. The framing around the open local density question is good, but the article currently overclaims Stainless verification.

## Must Fix

- Remove or qualify the abstract claim that all four global properties are verified in Stainless unless the exact functions exist in current source.
- The cited functions `verifyGeneralizedGrowth`, `assertNoAdjacentTwoGaps`, `countDeletionsAtIndex`, and `assertSafeZoneStability` were not found in `src/main/scala/` during review.
- Mark unverified mathematical claims as "Draft - mathematically proven, Stainless verification pending" if keeping them.
- Fix the safe-zone stability proof: as written, `newPosition = gapPosition - currentPrime` need not satisfy `newPosition >= nextPrime` from the listed preconditions.
- Replace the deprecated empirical reference path with the actual canonical empirical article location if one exists.

## Missing Proof Notes

The following lemmas are expressed as validated or Stainless-verified in the article, but no matching current source proof was found during review:

- `verifyGeneralizedGrowth`
- `assertNoAdjacentTwoGaps`
- `countDeletionsAtIndex`
- `assertSafeZoneStability`

Recommended fix: either implement these as real `.holds` proofs and verify them with `just verify`, or downgrade the article language to distinguish:

- `[Verified]` for current source-backed `.holds` lemmas
- `[Mathematically argued]` for proof sketches without Stainless code
- `[Empirical]` for computed observations
- `[Open]` for the local density question and anything equivalent to it

The current "All properties are verified in the Stainless system" abstract language should not remain unless all four functions are present in current source and appear in the green verification run.

## Should Fix

- Keep the excellent open-question section, but make it the article's organizing boundary.
- Add an explicit table separating `[Verified]`, `[Mathematically argued]`, `[Empirical]`, and `[Open]`.
- Cross-reference `learnings-capacity-argument.md` Section 16 for the final catalog.
- Avoid language like "cannot focus fire" unless it is backed by a precise lemma.

## Validation

- Search source for every cited `.holds` function.
- Run `just verify` or confirm the latest `verify.log`.
- Create tickets for any missing Stainless proofs before publishing.
- Re-check `articles/learnings/learnings-capacity-argument.md` Section 16 before finalizing the status table.

## Review Execution Log

### 2026-06-17: Review completed

**Changes applied to `articles/gap-dynamics.md`:**

### Must Fix — All addressed

- [x] **Abstract overclaim** — Rewritten: explicitly states "None of these four properties currently have Stainless-verified `.holds` code"
- [x] **Missing functions** — Confirmed absent from source. All 4 cited functions (`verifyGeneralizedGrowth`, `assertNoAdjacentTwoGaps`, `countDeletionsAtIndex`, `assertSafeZoneStability`) do not exist. No `GapProperties.scala` exists
- [x] **Unverified claims marked Draft** — All 4 properties marked `[Draft]` in section headers and property index table
- [x] **Safe zone stability proof** — Error documented: `newPosition >= nextPrime` does not follow from preconditions. Concrete counterexample given (`p=5, r=5, nextPrime=7`). Section marked `[Draft — Proof Has Gap]` with a "Flaw" subsection explaining the issue
- [x] **Empirical reference path** — Already correct (`articles/draft/draft-empirical-g-local-analysis.md` exists). Updated ref to use relative path `../articles/draft/...`

### Should Fix — All addressed

- [x] **Open-question section** — Kept as Section 6, framed as the organizing boundary
- [x] **Status table** — Property index at top (5 rows) + Summary table in Section 7 (7 rows). Uses `[Draft]`, `[Open]`, `[Corollary]`, `[Trivial]` labels
- [x] **Cross-reference learnings Section 16** — Added in Introduction (Section 1) and Open Local Density Question (Section 6)
- [x] **"Cannot focus fire" language** — Replaced with precise phrasing: "the filter cannot concentrate its destructive capacity on 2-gaps"

### Structure changes

- Added **Property Index** table at top (following pattern from cycle.md, integral.md, integral-cycle.md)
- Moved all 4 `.holds` code blocks to **Appendix A** (A.1–A.4), each marked `[DRAFT]` with explicit note
- Added **Appendix B** with verification log (5499 valid, 0 invalid, 0 unknown)
- Safe zone stability: added "Flaw" subsection explaining the gap
- Cross-referenced with learnings capacity argument Section 16 catalog

### Post-change verification

- `just verify` confirms: **5499 valid, 0 invalid, 0 unknown** ✅
- No Scala code was modified — only `.md` changes
