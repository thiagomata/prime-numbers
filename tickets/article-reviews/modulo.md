# Review: articles/modulo.md

## Source

- Article: `articles/modulo.md`
- Current role: Foundational article

## Verdict

One of the strongest candidates for publication after cleanup. It establishes a key primitive used everywhere else.

## Must Fix

- Ensure every listed modulo property in `OBJECTS.md` is either covered or explicitly marked out of scope.
- Add `Intuition:` and `Why This Matters:` labels consistently for each property section.
- Check every source link to `src/main/scala/v1/div/properties`.
- Keep the article aligned with the repository rule: use `Calc.mod` and `Calc.div`, not native `%`.

## Should Fix

- Clarify early why the project builds division and modulo from `DivMod` rather than relying on native operators.
- Add a small dependency note explaining how later articles use these lemmas.
- Trim the appendix log to the final verification summary.

## Validation

- Compare against the Division & Modulo section of `OBJECTS.md`.
- Confirm `verify.log` reports all VCs valid.
- Search the article for native `%` in code contexts.
