# Review: articles/integral.md

## Source

- Article: `articles/integral.md`
- Current role: Foundational article

## Verdict

Substantive and valuable, but needs a publication polish pass.

## Must Fix

- Fix stale or malformed source links, including paths that appear to use `./src//main/...` instead of the repository-relative source path.
- Ensure every major property includes the required source-reference block.
- Remove or explain stray commented math fragments in the conclusion area.
- Cross-check all integral properties against the Lists section of `OBJECTS.md`.

## Should Fix

- Shorten the conclusion, which currently reads like a second article summary.
- Add a property index near the top so readers can navigate the long proof sequence.
- Standardize headings: some conclusion headings omit punctuation or numbering consistency.

## Validation

- Search source for each cited `IntegralProperties` function.
- Confirm `verify.log` green status.
- Check all links render correctly from the article location.

---

## Execution Plan (2026-06-16)

### Current State

- `just verify`: **5499 valid, 0 invalid, 0 unknown** (confirmed)
- Article title: "Formal Verification of Discrete Integration Properties from First Principles" (already good)
- Article length: 1030 lines
- Inline Scala code throughout (no appendix)
- Broken links: 10+ instances of `./src//main/` (double slash)
- Stray LaTeX comment `% n > 0 \implies` in conclusion
- Verify log stale: shows 2781 (should be 5499)

### Changes Made

1. **Broken links fixed**: `./src//main/` → `../src/main/scala/` (all occurrences)
2. **Property index table**: Added after abstract listing 8 properties
3. **Section restructure**:
   - 1 Introduction (kept)
   - 2 Preliminaries (kept)
   - 3 Definition (merged old 3+4)
   - 4 Core Properties (4.1-4.4)
   - 5 Implementation Consistency (5.1-5.5)
   - 6 Limitations (condensed)
   - 7 Conclusion (shortened, stray comment removed)
   - Appendix A: Scala Verification (A.1-A.8)
   - Appendix B: Verification Log (5499)
4. **Scala code → Appendix A**: All 8 `.holds` verification blocks moved
5. **Source-reference format**: Every property now has "This property is verified in [Object::method](path). Full Scala code in Appendix A.x"
6. **Stray comment removed**: `% n > 0 \implies` deleted
7. **Conclusion shortened**: Removed full restatement of definitions
8. **Verify log updated**: 2781 → 5499
9. **Bug fix**: Section 6.5 referenced `assertLast` but showed `assertLastEqualsSum` code — fixed

### Cross-Reference: OBJECTS.md IntegralProperties vs Article

| Property | In Article? | Action |
|----------|-------------|--------|
| `assertHeadValueMatchDefinition` | Yes (4.1) | Move code to Appendix A |
| `assertAccDifferenceEqualsTailHead` | Internal helper | Skip (internal) |
| `assertAccDiffMatchesList` | Yes (4.3, 5.3) | Move code to Appendix A |
| `assertAccMatchesApply` | Yes (5.2) | Move code to Appendix A |
| `assertSizeAccEqualsSizeList` | Yes (5.5) | Move code to Appendix A |
| `assertLastEqualsSum` | Yes (4.4) | Move code to Appendix A |
| `assertIntegralEqualsSum` | Yes (4.2) | Move code to Appendix A |
| `assertLast` | Yes (5.4) | Move code to Appendix A |

### Risks

- Large single edit to `articles/integral.md` (1030 lines → ~1050 lines)
- Must verify with `just verify` after changes (tool takes ~18s)
- No Scala code changes needed — only markdown edits

### Progress Log

- 2026-06-16: Ticket created/updated. `just verify` confirmed 5499 valid. Implementation complete.
