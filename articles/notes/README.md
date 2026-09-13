# Notes — useful documents that are never promoted

This directory holds working documents that are **not drafts, not
properties, not models, and not articles**: research notes, review
records, and assessment catalogs. They are useful reference material,
but they must never be promoted to published articles — no PDF, no
arXiv LaTeX package, no parity gate applies to them.

Siblings with different contracts:

- `articles/draft/` — promotable candidates (the only place a future
  chapter article comes from);
- `articles/learnings/` — internal learnings documents;
- `articles/chapterN/` + `articles/arxiv/` — the published editions.

## Inventory

| File | What it is |
|---|---|
| [gap-dynamics-research-notes.md](gap-dynamics-research-notes.md) | Working notes extracted from the gap-dynamics article during its 2026-09-13 de-drafting: per-section research-record pointers, verification-status remarks, and the former Appendix B research map. |
| [review-draft-articles-2026-08-15.md](review-draft-articles-2026-08-15.md) | Scientific-quality review of the draft set (rigor, literature engagement, statistical soundness), revised 2026-09-13 during the survival-frontiers audit. |
| [review-draft-adversariality-phase-transition-2-gap-companions.md](review-draft-adversariality-phase-transition-2-gap-companions.md) | House-style review of the Survival Frontiers draft. |
| [review-draft-relaxed-almost-prime-sieve-sequence.md](review-draft-relaxed-almost-prime-sieve-sequence.md) | House-style review of the Relaxed Almost-Prime draft. |
| [review-draft-sieve-foundation.md](review-draft-sieve-foundation.md) | House-style review of the Sieve Foundation bridge draft. |
| [review-exercise-local-safe-window-capacity.md](review-exercise-local-safe-window-capacity.md) | House-style review of the capacity exercise. |
| [review-list.md](review-list.md) | House-style review of the published list article (chapter 3). |
| [reviewer-notes-aug-2026.md](reviewer-notes-aug-2026.md) | External-style reviewer notes; source of the "canonical note" vocabulary used by the gap-dynamics evidence tables. |
| [reviewer-notes-gap-dynamic.md](reviewer-notes-gap-dynamic.md) | Reviewer notes on the gap-dynamics draft. |

## Superseded material (deleted 2026-09-13)

Two superseded drafts and their reviews were deleted rather than moved,
because their mathematical content is preserved in published or
maintained documents:

- `draft-sieve-gap-survival-math.md` — copy-or-merge, stable absence,
  and full-period survival derivations live in
  [Gap Dynamics](../chapter6/gap-dynamics.md) and
  [gap-dynamics-research-notes.md](gap-dynamics-research-notes.md).
- `draft-empirical-g-local-analysis.md` — the superseded `[p,p^2]`
  experiment record; its corrected density analysis and its own
  documented error are superseded by the canonical `[q,q^2)` transition
  experiment behind the gap-dynamics article.
- `review-draft-empirical-g-local-analysis.md`,
  `review-draft-sieve-gap-survival-math.md` — reviews of the deleted
  files above.

## Cross-cutting style findings worth keeping (from the 2026-09-01 house-style pass)

The per-finished-article review files listed in the original index of
these reviews were never committed, so their rows survive here as plain
findings (no links): modulo (~40% state-and-cite properties), list
(conclusion merges unrelated groups), cycle (best in class; 11-property
conclusion block), integral (raw `$$` blocks), integral-cycle (most
disciplined status framing), euclid-theorem (no conclusion math recap),
gap-dynamics (120 `properties/` authority citations — resolved by the
2026-09-13 de-drafting), sieve-sequence (bare `§N` references).

Patterns that recur across independently written documents:

1. `\blacksquare` usage eroded across the series while `[Q.E.D.]`
   stayed; worth one sweep, not per-file fixes.
2. Conclusion math blocks merging unrelated property groups violate the
   one-block-per-group rendering rule.
3. Internal `§N` references as bare text instead of anchored Markdown
   links (sieve-sequence, Survival Frontiers draft).
4. Math delimiter drift: `` ```math `` vs raw `$$` vs `` ```text ``.
5. Renames of chapter-6 articles have twice left dangling references —
   run a repo-wide link check after any rename.

## Property and model coverage audit (2026-09-01, still accurate)

Headline findings of the coverage cross-check of draft claims against
`OBJECTS.md`, `properties/sieve-sequence/`, `candidates/`, and
`companions/`:

- **draft-sieve-foundation** — parity good; one optional prerequisite
  (smallest divisor ≤ √n) would complete the foundation story.
- **draft-relaxed-almost-prime** — parity adequate; optional §8
  cross-reference to the learnings §15 signed-program boundary.
- **draft-adversariality (Survival Frontiers)** — the six proved
  `companions/properties/` lemmas match its Appendix A records but are
  never cited by path (required cross-references before promotion);
  a fifth companion model `uniform-digit-2-gap/` exists on disk
  unindexed.
- **exercise-local-safe-window-capacity** — its `2·R(p,q)` pigeonhole
  bound is strictly weaker than the proved
  `G_local > A(p,q)` threshold; an instructor "where this sits" note
  recommended.

Statuses are preserved verbatim from the source notes; nothing is
promoted to a stronger status, and no article content was changed by
this directory's creation.
