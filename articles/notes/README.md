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
| [exercise-local-safe-window-capacity.md](exercise-local-safe-window-capacity.md) | Worked exercise (tasks + solution sketches) proving a local pigeonhole 2-gap survival bound. Moved here from `articles/draft/` 2026-09-14: a real, correctly-proved result, but not an article of its own — its background restated material already in `sieve-sequence.md`/`gap-dynamics.md` (now links to those sections instead), and its main bound is the elementary warm-up to the exact result already published in Gap Dynamics §4.3–4.4. |
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

### Superseded material (deleted 2026-09-14)

- `draft-sieve-foundation.md` — a "bridge" draft of five small
  prerequisite lemmas, not a standalone result. Its unit-cycle
  generation/strict-increase lemmas (§§2–3) are already published in
  [Integral Cycle](../chapter4/integral-cycle.md) §4.6 / Appendix A.17.
  Its remaining three (§§4–6, `FilterPreservesPrimesProperties`:
  distinct primes don't divide each other, filtering preserves primes,
  filtered lists still contain them) are correct and Stainless-verified
  — confirmed directly against `logs/verify-ch-5-v1-chapter5-_.log`
  (`total: 2145 valid: 2145 ... invalid: 0`) — but checked one call
  chain deep: none of the three is actually consumed by anything a
  published article cites. `assertPrimeNotDivisibleByDistinctPrime`'s
  only chapter-6 caller,
  `SpecDerivedRepeatedCycleProperties.assertFirstSurvivorMatchesNextSeqHead`,
  is itself called by nothing, including the lemma `sieve-sequence.md`
  §5.4 actually cites (`assertSpecBaseAndRepeatedGapListMatch`).
  Verified-but-uncited is not the same as wrong, and it isn't grounds
  for forcing a weak article just to have somewhere to quote them; the
  three lemmas remain valid, verified Scala code with no citing article,
  same as most of the codebase's internal building-stone lemmas.
- `review-draft-sieve-foundation.md` — review of the file above.

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
  (smallest divisor ≤ √n) would complete the foundation story. Retired
  2026-09-14 (see "Superseded material" above) rather than completed:
  parity being good did not make it a strong enough article on its own.
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
  recommended. Done 2026-09-14, but as a move rather than a promotion:
  relocated to `articles/notes/` (it was never headed for a chapter
  number), math converted from ` ```text ` to ` ```math `/`$...$`, its
  restated background swapped for links into `sieve-sequence.md` and
  `gap-dynamics.md`, and the recommended "where this sits" pointer to
  Gap Dynamics §4.3–4.4 added directly to §6/§7.

Statuses are preserved verbatim from the source notes; nothing is
promoted to a stronger status, and no article content was changed by
this directory's creation.
