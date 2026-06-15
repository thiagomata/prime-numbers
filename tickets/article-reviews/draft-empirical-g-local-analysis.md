# Review: articles/deprecated/draft-empirical-g-local-analysis.md

## Source

- Article: `articles/deprecated/draft-empirical-g-local-analysis.md`
- Current role: Empirical draft in deprecated folder

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
