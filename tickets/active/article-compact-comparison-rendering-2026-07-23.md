# Article Compact Comparison Rendering

## Goal

Fix article math that uses compact strict comparisons such as `d<N`, `r<p`, or
`Q<p^2`, because GitHub and VS Code can confuse forms like `<N` with markup.

## Current State

- `sieve-sequence.md` has already been normalized so only intentional HTML tags
  and reference anchors use raw `<` / `>`.
- A scan of nearby active articles found compact inline comparisons in
  `euclid-theorem.md` and `gap-dynamics.md`.

## Expected State

- Use readable spaced comparisons such as `d < N` where raw comparison symbols
  are kept.
- Use `\lt` / `\gt` only when spacing would make the expression awkward.
- Do not touch real HTML tags or reference anchors.

## Validation Plan

- Search active articles for compact strict comparisons inside inline math.
- Run `git diff --check`.

## Learning Log

- 2026-07-23: The problem is not every raw `<` or `>`. The risky form is the
  compact no-space form before a letter, such as `<N` or `<b`, because Markdown
  renderers may treat it like the start of an HTML tag.
- 2026-07-23: Spaced compact comparisons in `euclid-theorem.md`,
  `gap-dynamics.md`, and `modulo.md`. A math-only scan over active chapter
  articles now reports no compact strict comparisons in inline math or fenced
  `math` blocks. `git diff --check` is clean.
