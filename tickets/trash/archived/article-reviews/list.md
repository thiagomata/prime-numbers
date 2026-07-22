# Review: articles/list.md

## Source

- Article: `articles/list.md`
- Current role: Foundational article

## Verdict

Technically rich and central, but too long and uneven for magazine publication without editing.

## Must Fix

- Add a concise property index at the start.
- Ensure every important list property in `OBJECTS.md` appears or is explicitly out of scope.
- Add the required source-reference blocks consistently after Scala verification snippets.
- Check the appendix verification output against the current `verify.log`.

## Should Fix

- Split very long proof sections with short reader-roadmap paragraphs.
- Reduce implementation detail in the main narrative and move bulky code to appendices where possible.
- Tighten the limitations section so it supports the article rather than diluting the conclusion.

## Validation

- Cross-reference `ListUtilsProperties.scala`, `SliceEquivalenceLemmas.scala`, `IntegralProperties.scala`, `ListProduct.scala`, and `ListProductDiv.scala`.
- Confirm all cited properties are present in source and verified by the latest log.
