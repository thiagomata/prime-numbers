# Modulo Article Quality Review

## START HERE

Micro-goal: bring `articles/chapter2/modulo.md` up to the current article
standard established by `cycle.md`, `euclid-theorem.md`, and `list.md`.

## Goal

Review and revise the modulo article so the mathematical properties are the
first-class subjects. Scala proof code should appear only when it has a high
signal/noise ratio, and any excerpt must link to the maintained source file.

## Current State

The article still has older publication patterns: tutorial-style verification
prose, source-code walkthrough wording, long inline proof bodies in the main
article, and a thin appendix. The consecutive-integers section also contains an
article snippet with a commented conclusion, which should be replaced by the
real source proof or by prose plus a source link.

## Expected State

- Main sections explain the properties in prose and math first.
- Source methods are verification references, not the primary subject.
- No article snippet presents a commented theorem as a proof.
- Scala excerpts kept near the article body or appendix have nearby source
  links.
- The conclusion returns to the core proved properties in mathematical form.

## Similar Tickets

- `tickets/active/article-stub-lemma-audit-2026-07-22.md`
- `tickets/trash/archived/article-reviews/modulo.md`
- `tickets/done/scientific-review-articles-2026-07-17.md`

## Risks and Assumptions

- Assumption: this is a markdown-only article review; Stainless verification is
  not required unless source files change.
- Risk: removing code can make the article feel too terse. Preserve compact
  source excerpts in an appendix when the code clarifies the proof shape.
- Risk: modulo has many foundational lemmas. Keep the body readable by grouping
  related properties and using source references for implementation details.

## Validation

- Search `modulo.md` for old tutorial/code-first patterns.
- Check source links for property references.
- Run `git diff --check`.

## Progress Log

- Ticket created after user requested the same review style for
  `articles/chapter2/modulo.md`.
- Reframed the article title, abstract, and introduction around recursive
  normalization while keeping formal verification visible as a core result.
- Removed tutorial-style formal-verification quotations and old "Stainless
  mechanics" prose from the introduction.
- Replaced noisy main-body Scala snippets with math-first explanations plus
  source references; kept selected high-signal excerpts in Appendix A with
  nearby source links.
- Corrected the consecutive-integers proof framing: the exactly-one property is
  supported by existence plus at-most-one lemmas, not by a stub/commented proof
  body. Added real excerpts for `nonzeroAfterZero`, `existsZero`, and
  `atMostOneZero`.
- Updated `CONTRIBUTING.md`, `PROOF_GUIDE.md`, and `LEARNINGS.md` with the
  distinction the user clarified: articles should avoid low-level verifier
  mechanics, but should clearly and proudly state when formal verification was
  achieved.
- Reviewed `modulo.md` against the new `:=` convention. Corrected both the
  recursive `DivMod.solve` definition and the traditional `div`/`mod` notation
  definitions to use `:=`; kept relation, theorem, invariant, and proof
  equalities as `=`.
