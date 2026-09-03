# Article Guideline-Compliance Review — Index

**Date:** 2026-09-01
**Scope:** All 8 finished articles (`articles/chapter2/` through
`articles/chapter6/`) and all 6 documents in `articles/draft/`, each checked
against `PROOF_GUIDE.md`, `CONTRIBUTING.md`'s 26-point checklist, and the
`AGENTS.md` article rules (`three-representations`, `framing-integrity`,
`property-completeness`, `no-ticket-references`). One review file per
article/draft; this index summarizes what recurs across them and what
doesn't. No article content was changed — this is analysis only.

`articles/draft/review-draft-articles-2026-08-15.md` already reviewed the
six drafts as scientific papers (rigor, literature engagement, statistical
soundness); the per-file reviews here check the repository's own house
style instead and note where that earlier review's findings have since been
fixed.

## Overview

| Article | Genre | Overall | Top issue |
|---|---|---|---|
| [modulo.md](review-modulo.md) | Finished (ch2) | Strong, one real gap | ~40% of properties state-and-cite instead of deriving |
| [list.md](review-list.md) | Finished (ch3) | Strong, drifts late | Conclusion merges unrelated property groups; §8 has zero derivations |
| [cycle.md](review-cycle.md) | Finished (ch4) | Best in class | Conclusion merges 11 properties into one block; `[Q.E.D.]` misplaced ~10× |
| [integral.md](review-integral.md) | Finished (ch4) | Strong, one outlier | Only article dominated by raw `$$` instead of `` ```math `` (46 vs 16) |
| [integral-cycle.md](review-integral-cycle.md) | Finished (ch4) | Most disciplined status framing | Conclusion silently drops 3 of §4's 5 headline properties |
| [euclid-theorem.md](review-euclid-theorem.md) | Finished (ch5) | Real drift begins here | **No math recap in the conclusion at all**, despite CONTRIBUTING.md naming this article as a model for exactly that |
| [gap-dynamics.md](review-gap-dynamics.md) | Finished (ch6) | Structurally different genre | 120 links citing `properties/` as "where the proof is maintained" — the article says so in its own words |
| [sieve-sequence.md](review-sieve-sequence.md) | Finished (ch6) | Best of chapter 6 | Zero of ~16 internal section references are Markdown links |
| [draft-sieve-foundation.md](review-draft-sieve-foundation.md) | Draft | Nearly finished | No `Conclusion` heading; ready to graduate once small gaps close |
| [exercise-local-safe-window-capacity.md](review-exercise-local-safe-window-capacity.md) | Exercise | Different genre, solutions now included | All math in ` ```text `, not ` ```math ` |
| [draft-empirical-g-local-analysis.md](review-draft-empirical-g-local-analysis.md) | Superseded record | Honest, misplaced | Status-column tables; belongs in a non-existent `articles/deprecated/` |
| [draft-sieve-gap-survival-math.md](review-draft-sieve-gap-survival-math.md) | Superseded draft | Good math, broken pointer | 3 dead links to `gap-dynamics-v2.md` (renamed to `gap-dynamics.md`) |
| [draft-relaxed-almost-prime-sieve-sequence.md](review-draft-relaxed-almost-prime-sieve-sequence.md) | Active draft | Most improved since 08-15 | Every theorem restates its own scope twice in a row |
| [draft-adversariality-phase-transition-2-gap-companions.md](review-draft-adversariality-phase-transition-2-gap-companions.md) | Active draft | Best citation discipline of the set | 32 internal `§N` references, zero linked |

## Cross-cutting patterns

These recur across independently-written articles, which is why they're
worth fixing as a batch rather than file by file.

### A. `\blacksquare` is disappearing from the series

`list.md`, `cycle.md`, `integral.md`, and `integral-cycle.md` all close
derivations with `\blacksquare` and `[Q.E.D.]` together, as PROOF_GUIDE's
Voice-and-Style section asks. `modulo.md`, `euclid-theorem.md`,
`gap-dynamics.md`, and `sieve-sequence.md` use `[Q.E.D.]` only — zero
`\blacksquare` — and `draft-sieve-foundation.md` uses neither. The
adversariality draft and the relaxed almost-prime draft use `[Q.E.D.]`
almost exclusively too (2/19 and 0/several `\blacksquare`, respectively).
This reads like a habit that was present at the start and has been
eroding article by article; every review above lists it as at most a minor
finding on its own, but the pattern across eight of fourteen documents
makes it worth a single sweep rather than fourteen small ones.

### B. Conclusion math blocks merge unrelated property groups

CONTRIBUTING rule 19 asks for one `` ```math `` block per property group in
the conclusion recap, specifically because KaTeX sizes every row in a
shared block to its widest row. `list.md` (3 merged blocks), `cycle.md` (11
properties in one block), and `integral.md` (10 properties in one block)
all violate this to varying degrees; `integral-cycle.md` and
`gap-dynamics.md` do it much more mildly (blocks stay reasonably scoped).
`euclid-theorem.md` skips the requirement entirely by having no conclusion
math at all. This is a mechanical, low-risk fix everywhere it appears.

### C. `properties/`, `candidates/`, and similar internal notes cited as mathematical authority

PROOF_GUIDE's "Mathematical Authority and Article Boundaries" section
explicitly forbids citing `properties/`, `candidates/`, `articles/learnings/`,
or tickets as the authority for a proof, even when the article also gives
the derivation in its own body. `gap-dynamics.md` does this systematically
(120 links; Appendix C states outright that "the canonical notes remain
the authoritative source"). The relaxed almost-prime draft does it at
much smaller scale (~6 instances). `modulo.md` through `sieve-sequence.md`
and the adversariality draft do not do this at all — their citations point
to `src/main/scala/` or other published articles, correctly. This is the
single most severe individual finding in the whole set (see
`gap-dynamics.md`'s review) and is worth treating as a scope/structure
decision, not just a wording fix.

### D. Internal `§N` references are bare text, not Markdown links

CONTRIBUTING rule 26 requires every same-document `§N` reference to be a
Markdown link to its own anchor. `sieve-sequence.md` (16 occurrences) and
the adversariality draft (32 occurrences) violate this completely — not
one internal reference in either document is linked, while their
cross-*article* references are correctly formatted as full links. This
looks like a single habit applied consistently within each document
(internal refs written as plain prose, external refs written as proper
links), which makes it a fast, mechanical, high-confidence fix once
identified.

### E. Math delimiter drift: `` ```math `` vs. `$$`/`` ```text ``

The repository standard is fenced `` ```math `` LaTeX blocks. `integral.md`
is a clear outlier (46 raw `$$` blocks vs. 16 fenced), and
`draft-empirical-g-local-analysis.md` uses `$$`/`$...$` throughout with
zero fenced blocks. `exercise-local-safe-window-capacity.md` uses plain
`` ```text `` for all of its math, which doesn't render as math at all.
Every other article and draft reviewed is fully compliant (`0` raw `$$`).

### F. Stale cross-references after the chapter-6 consolidation

A commit consolidated `gap-dynamics-v2.md`/`sieve-sequence-v2.md` into
today's `gap-dynamics.md`/`sieve-sequence.md`. Two drafts still point at
the old names: `draft-sieve-gap-survival-math.md` links to the
now-nonexistent `gap-dynamics-v2.md` three times (including in its own
"read this next" header note), and the adversariality draft's reference
list titles `gap-dynamics.md` with its pre-rename title ("Open Boundaries"
instead of "Signed Boundaries"). Worth a repo-wide link check after any
future rename of a chapter-6 article, since this is the second time it's
caused a dangling reference.

### G. Superseded content has nowhere documented to live

`CONTRIBUTING.md`'s Directory Structure section names `articles/deprecated/`
as a sibling of the chapter folders, but that directory does not exist.
`draft-empirical-g-local-analysis.md` and `draft-sieve-gap-survival-math.md`
both self-identify as permanently superseded (not actively evolving drafts)
and are the natural first occupants of that folder once it's created — or,
alternatively, `CONTRIBUTING.md`'s directory diagram should be corrected if
the maintainers intend deletion instead of archival.

## What's *not* a cross-cutting problem

Worth stating explicitly, since it's easy to read a long findings list as
uniformly bad news: no article or draft reviewed had a broken proof, an
unstated forward reference to a later chapter, a ticket reference, a
verification-condition count published in violation of rule 24, or
first-person-voice drift. The `three-representations` structure (English →
math → Scala) is intact everywhere it's supposed to be. The problems found
are concentrated in five or six specific, mechanical patterns (A–G above),
not spread evenly across every checklist item — which is good news for how
fast this is fixable.

## Suggested order of work

1. **`euclid-theorem.md`'s missing conclusion recap** (its own review,
   issue 1) — the clearest contradiction between a rule and the article
   CONTRIBUTING.md names as that rule's own example.
2. **Pattern C** (`gap-dynamics.md`'s `properties/` citations) — the
   largest single finding in the set; needs a scope decision, not just
   text edits.
3. **Patterns A, B, D** — three mechanical, low-risk sweeps across the
   files listed in each pattern above.
4. **Pattern E** (`integral.md`'s `$$` blocks, the exercise's `` ```text ``
   math) — mechanical conversion.
5. **Patterns F and G** — link fixes and a directory decision,
   respectively; low effort once decided.
6. Everything else is captured per-file in the individual reviews linked
   above, roughly in priority order within each file's own "Suggested
   priority" section.

## Property and Model Coverage Audit (2026-09-01)

On 2026-09-01 a second pass added a "Property and Model Coverage Audit"
section to each of the six draft/exercise review files, cross-checking
draft claims against `OBJECTS.md`, the `properties/sieve-sequence/`
catalog, `candidates/`, `companions/`, and
`articles/learnings/learnings-capacity-argument.md` (§9 failed paths,
§15 proved/open boundary, §16 ten-property snapshot). This dimension was
missing from the original house-style pass, which performed no parity
check between draft claims and the proved-property catalog. Headline
findings (details in the per-file audit sections):

- **draft-sieve-foundation.md** — parity good; one optional prerequisite
  (smallest divisor ≤ √n, OBJECTS.md ch5) would complete the
  foundation story.
- **draft-sieve-gap-survival-math.md** (superseded) — its `h−1` local
  threshold is superseded in form by the sharper proved note
  `sharp-local-two-gap-survival-threshold.md` (`G_local > A(p,q)`,
  accepted strikes only); archival cross-references recommended.
- **draft-relaxed-almost-prime-sieve-sequence.md** — parity adequate, no
  required additions; optional §8 cross-reference to the learnings §15
  signed-program boundary.
- **draft-empirical-g-local-analysis.md** (superseded) — its
  `G_local > p−1` measurements are the empirical record of learnings §16
  item 10, the single open property; archival note recommended.
- **draft-adversariality-phase-transition-2-gap-companions.md** — the six
  proved `companions/properties/` lemmas match its Appendix A records but
  are never cited by path (required cross-references); a fifth companion
  model `uniform-digit-2-gap/` exists on disk unindexed.
- **exercise-local-safe-window-capacity.md** — the exercise's
  `2·R(p,q)` pigeonhole bound is strictly weaker than the proved
  `G_local > A(p,q)` threshold; an instructor "where this sits" note
  recommended.

Statuses are preserved verbatim from the source notes (proved /
mathematically proved, Stainless verification not claimed / empirical /
open); nothing is promoted to a stronger status, and no article content
was changed.
