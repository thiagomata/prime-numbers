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
- Search for `primorialPlusOneModAny`, `newPrimeFromEuclid`, and `euclidTheorem` in `src/main/scala/v1/prime/properties/PrimeProperties.scala`.
- Cross-check the Prime section of `OBJECTS.md`.
