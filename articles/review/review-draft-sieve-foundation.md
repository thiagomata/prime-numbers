# Review — `articles/draft/draft-sieve-foundation.md`

**Date:** 2026-09-01
**Reviewed against:** `PROOF_GUIDE.md`, `CONTRIBUTING.md` (26-point checklist), `AGENTS.md`.
**Status:** No changes made — analysis only. A prior review
(`articles/draft/review-draft-articles-2026-08-15.md`) already assessed this
draft as a scientific paper; this review checks it specifically against the
repository's own house-style checklist and notes what has changed since.

## Overall assessment

This is the most nearly-finished of the six drafts: every property carries
a real derivation, a matching `.holds` function, and a source citation, and
the two issues the 2026-08-15 review flagged — a redundant §4/§5 pair and a
missing author block — both appear to have been fixed since (§5 now opens
by naming itself explicitly as "the filter-reading corollary of §4," and an
author block with name, date, and license is present at the top). What
remains are small structural gaps relative to the finished-article template
(no `Conclusion` heading, no `References` section, no `\blacksquare`/
`[Q.E.D.]` closers anywhere) rather than anything mathematical.

## Strengths

- §5 no longer duplicates §4 as a second proof of the same fact; its
  opening sentence states plainly that it "renames the divisor `p` of §4 to
  `filterPrime` and keeps the verified Scala wrapper because it is the
  form the sieve consumes," and §7 explicitly counts "four substantively
  distinct lemmas, with §5 as the filter-reading corollary of §4" — the
  exact fix PROOF_GUIDE's "A Named Citation Is Not a Different Fact"
  anti-pattern calls for.
- §8 (Boundary) states clearly what this draft does *not* claim ("that a
  particular sieve-stage head is prime, that a new period has a particular
  size, or that a gap survives in any local window") — solid
  `framing-integrity`.
- Every Scala snippet shown is a real, already-cited `.holds` function
  (not a `DRAFT — not yet verified` placeholder), and each one is short
  enough to read at a glance without needing an appendix.

## Issues

### 1. No `Conclusion` section (minor)

CONTRIBUTING's example structure and the "Draft Articles" rule ("Same
structure as formal articles") both expect a `## Conclusion` heading. This
draft goes directly from `## 7. What This Bridge Gives The Sieve` to
`## 8. Boundary` — §7 functionally serves as the conclusion (it recaps the
four properties in a compact math block) but is not labeled as one, and §8
serves as the scope/limitations section conventionally kept separate from
the conclusion in the finished articles.

**Fix:** rename §7 to `## 7. Conclusion` (its content already fits), or
add a one-paragraph `## Conclusion` before §8 that references §7's recap.

### 2. No `\blacksquare` or `[Q.E.D.]` anywhere (minor)

None of the four math blocks in §2–§6 closes with either mark — this
draft skips the convention entirely rather than using one over the other.
PROOF_GUIDE's Voice-and-Style section asks every article, including
version drafts, to close derivations with `\blacksquare` and/or
`[Q.E.D.]`.

**Fix:** add a closing mark to each of §2, §3, §4, §6's derivations.

### 3. No `References` section (minor)

The CONTRIBUTING template lists References as a standard section. This
draft has none — its only external pointer is an inline link to
`sieve-sequence.md` inside the abstract, not a numbered reference. Given
the draft cites no external literature, an empty References section isn't
obviously warranted, but the companion-article link could reasonably be
promoted to a numbered reference matching the pattern used by every
finished article.

**Fix:** optional — add a one-entry References section citing
`sieve-sequence.md`, or leave as is if the inline link is judged
sufficient for a bridge-scoped draft.

### 4. §1's scope list has no section links (minor)

The five-item numbered list in §1 ("show that the unit gap cycle
generates consecutive integers," etc.) does not link each item to the
section that proves it, unlike the compact group lists in every finished
article's introduction (checklist rule 1).

**Fix:** append `— §2`, `— §3`, etc. to each of the five list items.

## A structural observation, not a rule violation

Given how close this draft already is to the finished-article standard —
author block present, no redundant lemmas, honest scope boundary, every
claim source-backed — it may be close to ready to drop the `draft-` prefix
and move to `articles/chapter5/` or `articles/chapter6/` once issues 1–4
are addressed, per CONTRIBUTING's "remove prefix when article is
finalized" guidance.

## Not an issue (checked, compliant)

- No forward references, no ticket references, no status columns —
  compliant.
- Mathematical authority: all citations point to `src/main/scala/`
  directly, none to `properties/` or other internal notes — compliant.
- `:=`/`=` usage, first-person-plural voice — compliant.

## Suggested priority

1. Add the `Conclusion` heading (issue 1) — one-line rename.
2. Add `\blacksquare`/`[Q.E.D.]` closers (issue 2) — mechanical.
3. Link §1's scope list to its sections (issue 4) — mechanical.
4. Decide on a References section (issue 3) — optional.

## Property and Model Coverage Audit (2026-09-01)

Cross-checked the draft's five cited `.holds` functions against `OBJECTS.md`
(chapters 2–6) and the `properties/sieve-sequence/` catalog. Parity for the
draft's declared scope is good: `CycleIntegralOnesProperties` (2 of 2 public
lemmas) and `FilterPreservesPrimesProperties` (3 of 3) are all present.

One **optional load-bearing prerequisite** is missing: the chapter-5
"smallest divisor is prime and ≤ √n" result (`PrimeUtils`/`PrimeProperties`
per `OBJECTS.md` ch5). The draft's §7 motivates filtering as "removing the
composites the sieve will later need to remove," and a reader asking *why
filtering by primes up to the square root suffices* finds no answer in the
draft or its cited lemmas. Adding it as a sixth bridge property would
complete the sieve-foundation story without touching the declared boundary
in §8. This is a scope decision, not an omission of an already-claimed
result — the draft never asserts anything that depends on it.

No `properties/sieve-sequence/` note belongs in this draft: the entire
catalog concerns period/gap survival semantics, which §8 explicitly excludes.

### Source-Check Adjudication (2026-09-01)

**Confirmed:** the five displayed source-backed properties cover the draft's
declared bridge scope exactly: the two public `CycleIntegralOnesProperties`
lemmas and the three public `FilterPreservesPrimesProperties` lemmas. The
later sieve-stage properties are already handled by the cited published
`sieve-sequence.md` article, so they are not missing here.

**Required correction:** the abstract's unqualified phrase “the elementary
filtering operation is prime-preserving” is too broad. `filterList` removes
every multiple of the installed filter prime, including that prime itself; the
proved result preserves every **distinct** prime already in the list. State
that qualification and treat retention/installation of the current filter
prime as a separate stage-representation obligation.

**Rejected as an addition:** the smallest-divisor/square-root material is not
load-bearing for this deliberately earlier bridge and should remain in the
published Euclid/sieve-sequence treatment. No direct Stainless theorem was
found for the broader filter-output soundness claim, so it may be named only
as an unverified desirable extension, not added as a proved sixth property.
