# Review: articles/integral-cycle.md

## Source

- Article: `articles/integral-cycle.md`
- Current role: Foundational article

## Verdict

Strong foundational article. Needs consistency cleanup and completeness cross-check before publication.

## Must Fix

- Ensure every property has all three required forms: English, math, Scala verification code with source reference.
- Cross-check every property against the Cycle Integrals section of `OBJECTS.md`, including classic, recursive, and modulo variants.
- Make the distinction between `ClassicCycleIntegral`, recursive `CycleIntegral`, and `ModCycleIntegral` explicit in the abstract and conclusion.

## Should Fix

- Add a short dependency map showing how modulo, cycle, and list lemmas feed into this article.
- Tighten the conclusion so it claims only the equivalences and index-shift properties actually proven.
- Normalize heading levels and remove extra spacing in headings like base-case labels.

## Validation

- Search cited function names in `src/main/scala/v1/cycle/integral`.
- Confirm `verify.log` is green.
- Compare article coverage against `OBJECTS.md` and `PROOF_GUIDE.md`.
