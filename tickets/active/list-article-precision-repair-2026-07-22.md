# list.md Article Precision Repair

## Goal

Repair agreed precision issues in `articles/chapter3/list.md` after review:

- Fix the tail-access algebra so it matches the verified right/left shift lemmas.
- Use list-cons notation for head-recursive and index-range slices.
- Keep the product-divisibility theorem strong, while clarifying the recursive-head induction.
- Fix the conclusion slice precondition.
- Fix reference anchors.
- Replace stale `GapList` names with `ShiftedList`.

## Current State

The article already has local edits in the worktree. Treat those as existing user/project changes and preserve them.

Known related review artifact:

- `tickets/trash/archived/article-reviews/list.md`

## Expected State

The article should be publication-consistent: prose, math notation, and current Scala proof names should agree. The product-divisibility section should continue to state the strong mathematical result, since each element is the head of one recursive sublist and divisibility is lifted through multiplication.

## Alternatives Considered

- Downgrade product divisibility to only head-of-sublist divisibility. Rejected: the user wants the stronger mathematical claim preserved.
- Add or change Scala lemmas. Rejected for this pass: the requested fixes are article-only.

## Risks and Assumptions

- Risk: touching broad article formatting could collide with existing worktree edits.
- Assumption: markdown-only repair does not require Stainless verification.

## Validation

- Run `git diff --check` after editing.
- Inspect the changed hunks for the agreed six issues.

## Progress Log

- Created ticket and found prior archived `list.md` review.
- Repaired `articles/chapter3/list.md` for tail-shift direction, cons notation in slice definitions, product-divisibility explanation, slice precondition, reference anchors, and stale `GapList` names.
- Repaired the echoed list-summary lemmas in `README.md`: slice preconditions now include `t < |L|`, and tail-shift bounds now match the left/right verified forms.
- Removed reader-facing `apply` terminology from the shifted-list math in `articles/chapter3/list.md`, keeping `apply` only in Scala verification snippets.
