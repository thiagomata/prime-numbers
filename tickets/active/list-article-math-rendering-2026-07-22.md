# list.md Math Rendering Repair

## START HERE

Micro-goal: standardize article list-concat notation on
`\mathbin{\texttt{++}}` so it renders reliably in GitHub and VS Code Markdown
previews.

## Goal

Repair the article-wide replacement that changed concat notation into:

```text
A & = [x] \operatorname{append} L  & \qquad \text{[Concatenation]} \\
```

so proofs remain mathematically clear and render in VS Code.

## Current State

`articles/chapter3/list.md`, `articles/chapter4/cycle.md`,
`articles/chapter4/integral.md`, and `articles/chapter6/sieve-sequence.md` use
`\operatorname{append}` in math blocks. The user reported that this notation
does not render correctly in Visual Studio Code and clarified that the problem
is not restricted to the list article.

## Expected State

Article math and public summary math should use `\mathbin{\texttt{++}}` for
list concatenation consistently, replacing `\operatorname{append}`,
`\mathbin{+\!+}`, and the Unicode concat glyph `⧺`.

## Similar Tickets

- `tickets/active/list-article-precision-repair-2026-07-22.md` repaired
  precision and notation issues in the same article.

## Alternatives Considered

- Keep `\operatorname{append}` and adjust spacing. Risky because the problem is
  likely renderer support rather than spacing.
- Use a Unicode concatenation symbol. Rejected because VS Code/KaTeX support can
  vary, and the project already maps Scala append to `++`.
- Use `\mathbin{\texttt{++}}`. Preferred because it is explicit, matches Scala
  list append, and avoids renderer-sensitive operator names or squeezed-symbol
  tricks.

## Risks and Assumptions

- Assumption: markdown-only repair does not require Stainless verification.
- Risk: replacing unrelated prose or source references would create unnecessary
  churn; the fix should be limited to article math/prose notation where the
  concat symbol was changed.

## Validation

- Inspect the edited hunks across affected articles.
- Run `git diff --check`.

## Progress Log

- Created ticket after finding the reported line in `articles/chapter3/list.md`.
- Broadened ticket after user clarified that the concat rendering problem is
  repo-wide across article math, not restricted to the list article.
- Standardized `\operatorname{append}` and `\mathbin{+\!+}` occurrences in
  affected article math to `\mathbin{\texttt{++}}`.
- Also normalized public-doc concat math in `README.md` from `⧺`, plus
  repeated-list concat shorthands in `articles/chapter4/integral-cycle.md` and
  `articles/deprecated/deprecated-generalized-gap-dynamic.md` from `::` to
  `\mathbin{\texttt{++}}`.
- Validation passed: no remaining `\operatorname{append}`, `\mathbin{+\!+}`, or
  `⧺` occurrences under `articles`, `README.md`, or `OBJECTS.md`;
  `git diff --check` passed.
- Follow-up repair in `articles/chapter4/integral.md`: fixed scalar/list concat
  mismatches exposed by the new notation. Head/tail decomposition now uses
  cons: `x_0 :: tail(L)` and `I_0 :: tail(I)`. The accumulated-list definition
  now uses `(head(L) + init) :: acc(...)`.
- Follow-up audit in `articles/chapter3/list.md`: fixed scalar/list concat
  mismatches by using cons for head prepend/decomposition: `x_0 :: P`,
  `head(L) :: tail(L)`, `x :: L`, and `head(A) :: (...)`.
  The remaining singleton concat uses are suffix or middle insertion cases,
  such as `slice ++ [L_t]` and `prefix ++ [e] ++ suffix`.
  Validation passed with `git diff --check`.
- Saved the standard in `LEARNINGS.md`, `CONTRIBUTING.md`, and
  `PROOF_GUIDE.md`: `::` is for element-list cons, while
  `\mathbin{\texttt{++}}` is for list-list concat in article math. Removed the
  old `\mathbin{+\!+}` recommendation. Validation passed with `git diff --check`.
