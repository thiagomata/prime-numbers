# Gap Dynamics Math Formatting Review

## Goal

Fix GitHub and VS Code Markdown math rendering issues in
`articles/chapter6/gap-dynamics.md`, following the same formatting standards
recently applied to the list, modulo, and Euclid theorem articles.

## Current State

- The article has many fenced `math` blocks using `aligned`.
- A structural scan found balanced `\begin{aligned}` and `\end{aligned}` blocks.
- Similar recent failures in other articles were caused by renderer-fragile
  inline notation, unsupported macros, or awkward labels inside aligned blocks,
  not necessarily by truly missing `\end{aligned}`.

## Expected State

- Fenced math blocks remain valid and renderer-friendly.
- Inline math avoids fragile underscore/subscript patterns in linked bullets or
  compact prose where GitHub may mangle the expression.
- Labels inside `aligned` avoid complex mixed text/math fragments.
- No unsupported macros such as `\operatorname`.

## Related Tickets

- `tickets/future/math-only-sieve-gap-survival-article.md` notes the broader
  history of `gap-dynamics.md` as mathematically sensitive material.
- `tickets/done/gap-dynamics-v2-research-update.md` records earlier cleanup of
  the gap-dynamics article family.

## Validation Plan

- Search for unsupported macros and fragile math patterns.
- Parse fenced math blocks to confirm each `aligned` environment is balanced.
- Run `git diff --check`.

## Learning Log

- 2026-07-23: Structural scan found 47 fenced math blocks and no literal
  missing `\end{aligned}`. The likely problem is renderer-sensitive math
  contents rather than unbalanced fences.
- 2026-07-23: Normalized standalone Q.E.D. rows from `&&&` to `&&` and
  replaced annotation labels that mixed text and live math with plain text
  labels. This keeps the mathematical statements unchanged while making the
  aligned blocks more renderer-friendly.
- 2026-07-23: Validation passed: 47 fenced math blocks, balanced `aligned`
  environments, no remaining `&&&`, no `\operatorname`, and `git diff --check`
  is clean.
