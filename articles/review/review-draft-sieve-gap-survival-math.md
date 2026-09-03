# Review — `articles/draft/draft-sieve-gap-survival-math.md`

**Date:** 2026-09-01
**Reviewed against:** `PROOF_GUIDE.md`, `CONTRIBUTING.md` (26-point checklist), `AGENTS.md`.
**Status:** No changes made — analysis only. This document self-identifies as
a "Superseded historical draft — mathematical exploration, not a
Stainless-verified article"; several checklist items are judged with that
genre in mind.

## Overall assessment

The core mathematics here is sound and clearly written: the copy-or-merge
dichotomy (§2), the stable-absence induction (§3), and the full-period
`h-2` survival law (§4) are all real, followable derivations, and §5's
global-vs-local distinction is stated as sharply as anywhere else in the
series. Two mechanical problems stand out. First, this draft's own pointer
to its successor — `articles/chapter6/gap-dynamics-v2.md`, linked three
times, including as reference `[4]` — is a dead link: that file was
consolidated into `articles/chapter6/gap-dynamics.md` (confirmed via `git
log`: "Consolidate chapter6 sieve-sequence and gap-dynamics article
versions"), and the rename was never propagated back into this draft.
Second, four of the document's five numbered references are never cited
in the body at all; the prose links directly to the same articles instead
of using the bracketed citation system it defines.

## Strengths

- §3's stable-absence argument for the value 2 is a genuine, complete
  induction (copy case, merge case, both closed out), not an assertion.
- §5 states the article's central boundary in one crisp non-implication:
  "global 2-gap survival `⇏` safe-window 2-gap survival" — exactly the
  scope discipline `framing-integrity` asks for, stated as a formula, not
  just prose.
- §11 ("What This Article Claims") and §12 ("Current Successor Boundary")
  together give an honest closing accounting: what's established, what
  isn't claimed, and specifically how the successor's approach differs —
  a real audit trail for a document handing off to a later article, rather
  than a vague "see also."
- All math uses fenced ` ```math ` blocks — no `$$`/`$...$` drift, unlike
  several sibling drafts.

## Issues

### 1. Three links to a file that no longer exists (major)

`articles/chapter6/gap-dynamics-v2.md` is linked at line 15 (the header
note pointing readers to "the current" successor), line 540 (§12's
opening sentence), and as reference `[4]` (lines 594–596). `git log`
confirms that file was renamed/merged into `articles/chapter6/gap-dynamics.md`
by the "Consolidate chapter6 sieve-sequence and gap-dynamics article
versions" commit; the `-v2` path does not exist on the current branch.
Since this draft's entire framing depends on directing the reader to "the
current" continuation, a dead link at that exact spot is more than
cosmetic — a reader following the header note at line 15 hits a 404 at the
first click.

**Fix:** update all three occurrences to
`articles/chapter6/gap-dynamics.md`.

### 2. Four of five numbered references are never cited in the body (moderate)

The References section defines `[1]` (Sieve Sequence), `[2]` (Gap
Dynamics, now superseded by consolidation), `[3]` (the empirical draft),
`[4]` (the gap-dynamics-v2 successor, see issue 1), and `[5]` (the relaxed
almost-prime draft). Only `[3]` is cited in the body (line 508, as bare
text `([3], superseded)` — not even a working `[[3]](#ref3)` link). The
document's other companion-article mentions (lines 15, 540, 575) use plain
inline Markdown links to the same targets instead of the bracketed
citation apparatus, leaving `[1]`, `[2]`, `[4]`, and `[5]` orphaned.

**Fix:** either cite each reference at its natural point in the text
(e.g. `[[1]](#ref1)` where the Sieve Sequence article is first invoked in
§1), or drop the numbered References section in favor of the inline links
already used consistently elsewhere in the document — but not both
conventions half-used as currently.

## A structural observation, not a rule violation

Like `draft-empirical-g-local-analysis.md`, this file is explicitly
superseded rather than actively developed, and CONTRIBUTING.md's directory
structure names an `articles/deprecated/` location for such material that
does not yet exist in the repository. See that file's review for the fuller
discussion; the same observation applies here.

## Not an issue (checked, compliant)

- All math in fenced ` ```math ` blocks — compliant, unlike several
  sibling drafts.
- No ticket references — compliant.
- Framing integrity — §11 states plainly "No formal verification is
  claimed for the new results in this article," matching its status line.
- First-person-plural voice — compliant.

## Suggested priority

1. Fix the three dead links to `gap-dynamics-v2.md` (issue 1) — the single
   highest-value, lowest-effort fix in this document.
2. Reconcile the citation system (issue 2) — either wire up the orphaned
   references or remove the unused apparatus.
3. Consider the `articles/deprecated/` question alongside the other
   superseded draft, as one decision covering both files.

## Property and Model Coverage Audit (2026-09-01)

Because this draft is superseded, the audit recommendation is **archival
cross-references, not new mathematical sections**. Several of its central
results now exist as standalone proved property notes that the draft cannot
cite (it predates them) and should not re-derive:

- §3 (stable absence of the value 2) —
  `properties/sieve-sequence/absence-of-two-gaps-is-stable.md`.
- §4 (full-period `h-2` survival) —
  `properties/sieve-sequence/exact-batched-two-gap-survival.md` and
  `exact-global-two-gap-count.md`.
- §7 (cluster survival) —
  `properties/sieve-sequence/exact-global-two-gap-cluster-count.md`
  (which proves the `(r-4)C` recurrence and leaves short-window placement
  open — the same boundary §5 draws here).
- §5/§6 (at most `h-1` strikes; conditional `G_local > h-1`) — **superseded
  in form** by `properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md`,
  which proves the sharper threshold `G_local > A(p,q)` using the exact
  accepted strike count `A(p,q) = π(⌊(q²−1)/p⌋) − π(p−1)` instead of the
  crude count of all multiples. Status: proved conditional implication,
  Stainless verification not claimed. An archival note should record that
  the draft's `h-1` form is the weaker ancestor of this note, so a reader
  arriving from the draft does not mistake it for the current best
  threshold.

These notes are internal (`properties/`), so per the math-authority rule
they should appear in the archival note as "also recorded in" pointers, not
as proof authority.
