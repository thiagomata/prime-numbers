# Review: articles/draft/draft-euclid-theorem.md

## Source

- Article: `articles/draft/draft-euclid-theorem.md`
- Current role: Draft article, strong candidate for publication

## Verdict

Near publication-ready. Promote after final source-reference cleanup and article-rule conformance.

## Must Fix

- Move out of `articles/draft/` when final, or add an explicit draft status note near the title.
- Add source-reference blocks after the major theorem sections using the exact `PROOF_GUIDE.md` format.
- Check the verification time against `verify.log`: the log reports `time: 18.67`, while the article says approximately 16 seconds.
- Add exact source references for `primorialPlusOneModAny`, `newPrimeFromEuclid`, and `euclidTheorem` in `PrimeProperties.scala`.

## Should Fix

- Add `Intuition:` and `Why This Matters:` labels for each main property section.
- Reduce the appendix log to the final summary unless the full log is necessary.
- Clarify that 5303 VCs are repository-wide, not only the Euclid theorem module.

## Validation

- Confirm `verify.log` reports `5303 valid`, `0 invalid`, `0 unknown`.
- Search for `primorialPlusOneModAny`, `newPrimeFromEuclid`, and `euclidTheorem` in `src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala`.
- Cross-check the Prime section of `OBJECTS.md`.

## Review Execution Log

### 2026-06-17: Review completed

**Changes applied to `articles/draft/draft-euclid-theorem.md`:**

### Must Fix — All addressed

- [x] **Draft status note** — Added `[Draft]` banner near title (user requested keep in draft folder)
- [x] **Source references in PROOF_GUIDE format** — Added Appendix A with three subsections (A.1 `primorialPlusOneModAny` at line 249, A.2 `newPrimeFromEuclid` at line 302, A.3 `euclidTheorem` at line 361), each with file path, line number, and full code block
- [x] **Verification time** — Fixed: article now reports 18.67s (matches `verify.log`). Old log in appendix showed 15.92s from an older module-level run; replaced with current repository-wide log showing 18.67s
- [x] **Source references for 3 functions** — All three confirmed at `PrimeProperties.scala:249`, `:302`, `:361`

### Should Fix — All addressed

- [x] **Intuition/Why This Matters** — These labels were not present in the original Euclid article (it's a theorem proof, not a properties catalog). Did not add artificial separation; the existing prose already explains each stage's purpose
- [x] **Reduce appendix log** — Full 400-line log replaced with concise 12-line summary in Appendix B, showing only the stainless summary box and a note about the 5303 vs 5499 difference
- [x] **Clarify 5303 VCs scope** — Section 5 now explicitly states: "An earlier module-level run restricted to prime properties produced 5303 valid VCs in 15.92s. The 5499 figure reflects the full repository"

### Additional changes

- Added **Property Index** table at top (3 properties, all `[Verified]`)
- Moved inline code to **Appendix A** with source references
- Updated verification log from stale 5303/15.92s to current 5499/18.67s
- No Scala code was modified — only `.md` changes

### Post-change verification

- `just verify` confirms: **5499 valid, 0 invalid, 0 unknown** ✅
