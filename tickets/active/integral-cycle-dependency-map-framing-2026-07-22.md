# Integral Cycle Dependency Map Framing

**Created:** 2026-07-22
**Updated:** 2026-07-22
**Status:** Complete
**Depends on:** None

## Related Tickets

- `tickets/done/integral-cycle-examiner-review.md` — examiner review of the article's publication readiness. Relevant lesson: article structure should make scope and purpose obvious to readers.
- `tickets/done/scientific-review-articles-2026-07-17.md` — cross-article scientific review. Relevant lesson: `integral-cycle.md` already has a dependency diagram, but its framing should be editorially precise.
- `tickets/active/sieve-sequence-article-rewrite.md` — cites `integral-cycle.md` as a layout model. Relevant lesson: dependency diagrams are useful as orientation aids, not as article goals.

## Goal

Adjust `articles/chapter4/integral-cycle.md` so the dependency map is presented as reader orientation and prerequisite context, not as a goal of the article.

## Current State

The article includes a `### Dependency Map` subsection immediately before the definitions section. The diagram is useful, but the subsection title can read as if the dependency map itself is one of the article goals.

## Expected State

The same conceptual information remains, but the heading and introductory sentence make clear that the diagram is supporting context for the verified cycle-integral properties.

## Approaches Considered

### Rename And Reframe

**Status:** RECOMMENDED

Rename `Dependency Map` to a context-oriented heading and adjust the following sentence.

**Strengths:** Minimal article-only change; preserves useful orientation.
**Risks:** None beyond wording taste.
**Fallback:** Remove the diagram entirely if the user wants a leaner article opening.

## Assumptions

- The user wants the article wording corrected, not the verified Scala code changed.
- The dependency diagram is still useful if it is framed as context.

## Risks

No verification risk. The change is markdown-only.

## Validation

Review the opening of `articles/chapter4/integral-cycle.md` and confirm the dependency diagram is no longer framed as a goal.

## Implementation Plan

1. Rename the subsection in `articles/chapter4/integral-cycle.md`.
2. Reword the sentence before the diagram.
3. Update this ticket with the result.

## Fallback Options

Remove the diagram if even the reframed context feels too prominent.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-22 | Ticket created. Related article-review tickets checked. | Reframe the article subsection. |
| 2026-07-22 | The article now presents the diagram as prerequisite structure and reader orientation, not as an article goal. | Done. |
