# Sieve Sequence Article: v2 Fixes + v1 Retirement Decision

**Status:** Active
**Created:** 2026-08-19 (consolidated from three tickets)
**Owner:** `articles/chapter6/sieve-sequence.md` (v1) and
`articles/chapter6/sieve-sequence-v2.md` (v2)

Consolidates: `m-interval-density-and-sieve-sequence-v2.md`,
`sieve-sequence-v2-salvage-before-v1-removal.md`, and
`sieve-sequence-article-rewrite.md` (the last is v1's original rewrite
ticket, now superseded — v2 is the stronger canonical article; folded in
here per the one-ticket-per-article rule).

## Goal

Bring `sieve-sequence-v2.md` to publication quality by fixing its known
framing errors, then decide and execute v1's fate: either retire it (it
currently has abstract placeholder debris and overclaims a fully verified
three-way equivalence) after salvaging its few useful explanatory blocks
into v2, or keep both with v1 clearly marked superseded.

## Current State

**v2 framing issues (open, technical):**
- §4.2 says `[h, h * M)`, which likely mixes the current-period interval
  `[h, h + M)` with the expanded next-period length `h * M`. `M = product(Pbar)`.
- §7.3 says filtering removes "every h-th value" / "one per block of h" from
  the expanded list — risky wording, since `nextExpanded` is lifted survivor
  residues, not raw consecutive integers.
- §8 claims only Bertrand remains and no Euclid requirement remains; current
  proof notes say that is optimistic — product/coprimality or CRT-style
  support is still open for the closed-form count. If Euclid/product-
  coprimality needs restating, verify the current proof surface in
  `PrimeUtils`, `BezoutUtils`, `AllPrimesSoFarList`, and the chapter6 source
  files first, then use current function names (stale proof names are a
  recurring failure mode here).
- Baseline: `SieveUtils.assertExpandResiduesSize` is verified
  (`expandResidues(residues, M, h).size == residues.size * h`);
  `SieveUtils.assertResiduesComplete` gives one-period containment for
  coprime values but not counted set equality by itself.

**v1 disposition:**
- v1's abstract contains placeholder debris (`Hello World`, `$x = 1^2$`) and
  its top-level framing overclaims a fully verified three-way equivalence;
  some proof-boundary language is stale relative to v2's theorem surface.
- v1 still has a few useful explanatory blocks worth salvaging before
  retirement (see Expected Changes below).
- v1's own earlier rewrite ticket (2026-06-28 onward) brought it structurally
  close to `integral-cycle.md`'s style and confirmed (via `logs/verify.log`,
  `10495 valid, 0 invalid, 0 unknown`) that its cited lemma names existed at
  the time. Its leftover suggestions — a dependency-map diagram, smoothing
  §§3-4, shortening Section 9's inline Scala — only matter if v1 is kept
  rather than retired; re-evaluate once the retire-vs-keep decision is made.

## Expected Changes (to v2, if salvaging before v1 retirement)

1. Add a short concrete-walk boundary note.
2. Add or prepare a verified lemma inventory appendix.
3. Expand the dependency section with a compact modulo-law table.
4. Add one explicit sentence explaining that the current head is not an
   active filter until the next stage.
5. Leave v2's abstract and proof-boundary framing intact except for small
   clarifications.
6. Do not reference tickets from the article body.

## Validation

- Markdown-only edits do not require Stainless verification.
- Confirm every new source reference in v2 exists under `src/main/scala/`.
- Confirm no article text references any internal ticket.
- Confirm v2 still satisfies the three-representation rule for any newly
  added property section.
- Confirm v2 does not claim `CycleSieveSequence.next()` / `nextGapsWalk`
  correctness unless a current verified lemma proves it.
- Confirm any salvaged v1 material is rewritten as polished article prose,
  not copied as archival commentary.

## Next Action

Resolve the §4.2/§7.3/§8 framing issues in v2 first (technical correctness
before salvage/retirement editorial work). Then decide v1's fate and, if
retiring, execute the salvage list above before removing it.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-14 | v2 should remain canonical; v1 has useful material to salvage around the concrete-walk caveat, proof inventory, modulo dependency explanation, and the "head is not an active filter" reader warning. | Filed as `sieve-sequence-v2-salvage-before-v1-removal.md`. |
| (undated, pre-consolidation) | v2's §4.2/§7.3/§8 have real framing/interval errors distinct from the salvage question. | Filed as `m-interval-density-and-sieve-sequence-v2.md`. |
| 2026-08-19 | Three tickets targeting the same v1/v2 article pair consolidated into one, per the one-ticket-per-article rule. | This file. Originals removed. |
