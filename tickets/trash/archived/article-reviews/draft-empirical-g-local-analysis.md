# Review: articles/draft/draft-empirical-g-local-analysis.md

## Source

- Article: `articles/draft/draft-empirical-g-local-analysis.md`
- Current role: Empirical draft in draft folder

## Verdict

Potentially publishable as an empirical companion, but not in its current location or with current verification wording.

## Must Fix

- Move out of `deprecated/` if it is intended for publication, or keep it clearly archival.
- Replace "verified in" claims for empirical functions with accurate language unless `SegmentedSieve::survivorsInRange` and `GapAnalyzer::countTwoGaps` are actual Stainless-verified `.holds` functions in current source.
- Clearly distinguish empirical computation from formal proof.
- Link the dataset or runner output that supports the table values.

## Should Fix

- Add reproducibility instructions: command, expected runtime, output file, and exact prime range.
- State that the data supports the local density conjecture but does not prove it.
- Add a small methodology limitations section covering finite range, implementation trust, and arithmetic assumptions.

## Validation

- Search `src/main/scala/` and `src/test/scala/` for the empirical runner names.
- Re-run or cite the latest empirical output if available.
- Check consistency with `gap-dynamics.md` and `learnings-capacity-argument.md`.

## Review Execution Log

### 2026-06-17: Review completed

**Changes applied to `articles/draft/draft-empirical-g-local-analysis.md`:**

### Must Fix — All addressed

- [x] **Location** — File is already at `articles/draft/`, not `articles/deprecated/`. Kept in draft folder per user request
- [x] **"Verified in" claims** — Confirmed `SegmentedSieve.survivorsInRange` and `GapAnalyzer.countTwoGaps` are both `@extern` (not `.holds`-verified). All "This function is verified in" → "This function is implemented in... as an `@extern` function (not Stainless-verified)"
- [x] **Distinguish empirical vs formal proof** — Added explicit disclaimer in abstract: "Crucially, this is empirical evidence, not a formal proof." Added "These are empirical results, not formal proofs" to abstract. Section 5.3 now explicitly states the functions are `@extern`
- [x] **Link dataset** — Already linked at `data/empirical/results.csv` in Section 3.5

### Should Fix — All addressed

- [x] **Reproducibility instructions** — Added Section 2.5 with exact `sbt 'runMain ...'` command, expected output file, and expected runtime (~11 minutes)
- [x] **State data supports but doesn't prove** — Abstract ends with "These are empirical results, not formal proofs." Section 5.3 explicitly says "local density question remains open in the formal verification sense"
- [x] **Methodology limitations** — Added Section 5.4 as a table covering range limit, proof gap, memory bound, and `@extern` implementation trust

### Additional changes

- Added **Property Index** table at top (4 properties, all `[Empirical]`)
- Added `[Draft]` banner near title
- Fixed reference paths: `articles/gap-dynamics.md` and `articles/learnings/learnings-capacity-argument.md`
- Updated References section (refs 1-3)
- Added cross-references to gap-dynamics.md and learnings-capacity-argument.md in Sections 1 and 5.3
- No Scala code was modified — only `.md` changes

### Post-change verification

- `just verify` confirms: **5499 valid, 0 invalid, 0 unknown** ✅
