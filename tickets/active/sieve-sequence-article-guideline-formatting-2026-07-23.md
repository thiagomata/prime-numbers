# Sieve Sequence Article Guideline And Formatting Review

## Goal

Bring `articles/chapter6/sieve-sequence.md` closer to the current article
guidelines and fix the reported GitHub/VS Code math formatting failures in
Section 6.2 and the conclusion.

## Current State

- Existing rewrite tickets already identify that `sieve-sequence.md` lags the
  finished article style.
- A structural scan found 20 fenced math blocks and balanced `aligned`
  environments, so the reported `Missing \end{aligned}` errors are likely
  caused by renderer-fragile math contents.
- Section 6.2 contains an annotation that mixes `\text{...}` with live math.
- The conclusion contains one large mixed aligned block, which is more fragile
  than smaller property summaries.
- Section 2.4 has tutorial-like verification wording, and Section 8 is framed
  as future work rather than current proof boundary/open work.

## Expected State

- Section 6.2 and the conclusion render cleanly on GitHub and VS Code.
- The article keeps Stainless/formal verification visible without teaching the
  verifier mechanics in a patronizing way.
- Open work is framed as current proof boundary, not speculative future-facing
  narrative.
- Formatting changes do not alter mathematical claims.

## Related Tickets

- `tickets/active/sieve-sequence-article-rewrite.md`
- `tickets/active/sieve-sequence-v2-article.md`
- `tickets/active/sieve-sequence-v2-salvage-before-v1-removal.md`

## Validation Plan

- Parse fenced math blocks for balanced `aligned` environments.
- Search for unsupported macros and fragile annotation patterns.
- Run `git diff --check`.

## Learning Log

- 2026-07-23: Existing tickets confirm this article has known publication-style
  drift. This pass should stay focused on renderer failures and small guideline
  violations, not a full article rewrite.
- 2026-07-23: Fixed renderer-fragile math annotations in Section 6.2 and other
  nearby blocks by replacing labels that mixed `\text{...}` with live math.
- 2026-07-23: Split the conclusion's single large `aligned` block into four
  smaller property recaps: linear stage semantics, gap-cycle reconstruction,
  filtering/copy-or-merge, and conditional next-stage results.
- 2026-07-23: Removed long Scala proof bodies from the main article body while
  keeping the source links immediately after the mathematical statements.
- 2026-07-23: Replaced the Mermaid proof-architecture diagram with prose and
  changed the tutorial-style verification subsection into a concise source
  evidence note.
- 2026-07-23: Renamed `Future Work` to `Open Proof Work` and framed those items
  as current proof boundaries rather than future-facing article justification.
- 2026-07-23: Validation passed: 23 fenced math blocks, balanced `aligned`
  environments, no Scala or Mermaid fences, no `\operatorname`, no split
  `\text{...}` annotation labels, and `git diff --check` is clean.
- 2026-07-23: Replaced raw strict comparison operators in article math with
  `\lt` and `\gt`. This avoids renderer confusion where expressions such as
  `$p^+<h^2$` or values below a bound can be mistaken for markup. The only
  remaining raw `<` and `>` in `sieve-sequence.md` are intentional HTML tags
  and reference anchors.
