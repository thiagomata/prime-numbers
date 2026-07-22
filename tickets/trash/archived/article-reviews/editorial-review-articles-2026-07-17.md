# Editorial Review: `articles/`

**Reviewer role:** Editorial board, evaluating against this repository's own stated
standards — `CONTRIBUTING.md`'s 14-item Article Quality Checklist, `PROOF_GUIDE.md`'s
three-representations rule, and the `AGENTS.md` rules `framing-integrity`,
`property-completeness`, `no-ticket-references`, and `no-emojis`.

**Date:** 2026-07-17
**Scope:** All 17 files under `articles/` (8 finished, 2 draft, 5 deprecated, 2 learnings).
**Method:** Full read of the 8 finished articles; targeted reads plus repo-wide grep/script
checks (broken links, emoji ranges, VC-count leaks, status-column tables, ticket references,
heading structure, per-chapter opening style) across all 17 files. Property-completeness
was spot-checked against `OBJECTS.md`'s chapter-6 catalog, not exhaustively audited line by
line against every `.holds` function in `src/` — see Limitations at the end.

No `.scala` files were touched. This is a documentation-only review.

---

## Verdict Summary

| Article | Verdict | Main issues |
|---|---|---|
| `chapter2/modulo.md` | Minor–moderate revisions | Missing intro group list; Ch.6 opens with no framing; conclusion omits two verified properties |
| `chapter3/list.md` | Minor revisions | Ch.2 opens with a bare subsection; conclusion omits one property |
| `chapter4/cycle.md` | Minor revisions | Inline GitHub URLs instead of relative paths |
| `chapter4/integral.md` | Minor revisions | Same inline-URL issue |
| `chapter4/integral-cycle.md` | Minor revisions | Same inline-URL issue; missing required Mermaid diagram for its two variant definitions |
| `chapter5/euclid-theorem.md` | Accept | Same inline-URL issue only; otherwise a model article |
| `chapter6/gap-dynamics.md` | Minor revisions | Status column in a properties table; chapters open with prose but no lemma-summary bullets |
| `chapter6/sieve-sequence.md` | Minor revisions | No compact intro group list; two chapters (§4, §5) open with zero framing text |
| `draft/*` (2 files) | Fine as drafts | Correctly labeled, correctly withhold Stainless code; one has broken relative links |
| `deprecated/*` (5 files) | Needs cleanup | All 5 have broken relative links to the merged targets; one leaks a VC count and references a ticket file |

None of the finished articles have emoji, meta-labels ("Intuition:", "Proved:"), or letter-suffixed section numbers. Title/abstract/conclusion framing-integrity holds up well across the board — nobody overclaims a Twin Prime Conjecture proof, and `gap-dynamics.md` and `sieve-sequence.md` are explicit about open boundaries (Bertrand's postulate dependency, the local-density question).

---

## Cross-Cutting Issues (affect multiple files)

### 1. Broken relative links — all 5 files in `deprecated/`

Every deprecated article's "merged into" notice links to the wrong path:

```
deprecated-sieve-foundation.md:3   [sieve-sequence.md](../sieve-sequence.md)
deprecated-sieve-sequence.md:11    [sieve-sequence.md](../sieve-sequence.md)
deprecated-gap-persistence.md:3    [gap-dynamics.md](../gap-dynamics.md)
deprecated-generalized-gap-dynamic.md:3  [gap-dynamics.md](../gap-dynamics.md)
deprecated-twin-prime-persistence.md:3   [gap-dynamics.md](../gap-dynamics.md)
```

`sieve-sequence.md` and `gap-dynamics.md` both live in `chapter6/`, not in `articles/` directly, so `../sieve-sequence.md` and `../gap-dynamics.md` 404 from `deprecated/`. Should be `../chapter6/sieve-sequence.md` and `../chapter6/gap-dynamics.md`. Trivial fix, but it means the "go read the current version" pointer in every deprecated file is currently dead.

### 2. Stale, contradictory deprecation note in `deprecated-sieve-sequence.md`

Lines 1–7 say the article was superseded by `draft-sieve-foundation.md` and point to a ticket:

> `See the ticket `article-consolidation.md` for the plan to merge both articles.`

But: (a) no `draft-sieve-foundation.md` exists anywhere in the repo — the only similarly-named file is `deprecated/deprecated-sieve-foundation.md`, which itself says it was merged into `sieve-sequence.md`, not that it supersedes anything; (b) this violates `no-ticket-references`, which explicitly covers `deprecated/`; (c) it also states "5303 total VCs across 468 functions," which `CONTRIBUTING.md` item 14 says never belongs in an article. Lines 11–13 immediately below give the correct, current story (merged into `sieve-sequence.md`). The old note above it should just be deleted rather than left contradicting the new one.

### 3. Inline citations use absolute GitHub URLs instead of relative paths (ch4–ch5)

`CONTRIBUTING.md` item 11 calls for relative paths (`../chapterN/file.md`) when citing prerequisite articles, and the References section is the place for formal, fully-qualified citations. `chapter6/sieve-sequence.md` (the newest article) follows this correctly — relative links inline, `github.com/...blob/master/...` URLs only in the References list. `chapter4/cycle.md`, `chapter4/integral.md`, `chapter4/integral-cycle.md`, and `chapter5/euclid-theorem.md` instead use the full `https://github.com/thiagomata/prime-numbers/blob/master/...` URL inline in the body text too (e.g. `cycle.md:61-64`, `integral.md:41-42`). Functionally these links resolve today, but they hard-code `master` as the branch name and assume the repo stays public, and they're inconsistent with the article the project itself treats as the current convention. Worth a pass to swap these to relative links, probably done together across the four files in one edit.

### 4. Draft link rot

- `draft/draft-empirical-g-local-analysis.md:43` links to `../articles/gap-dynamics.md` and `../articles/learnings/learnings-capacity-argument.md` — both have an extra, erroneous `articles/` segment (the file is already inside `articles/draft/`, so it should be `../chapter6/gap-dynamics.md` and `../learnings/learnings-capacity-argument.md`).
- `draft/draft-sieve-gap-survival-math.md` links to `../chapter6/sieve-sequence-v2.md`, which doesn't exist (there's no "v2" file in the repo — likely a stale reference from a renamed/removed file).

---

## Per-Article Detail

### `chapter2/modulo.md` — Minor–moderate revisions

- **Item 1 (compact group list):** The Introduction (§1, lines 25–49) never gives the reader a bullet list of property groups with section numbers — every other finished article does this. Readers get straight to a Stainless blockquote instead.
- **Item 2 (per-chapter bullet summaries):** §6 "Some Important Properties of Modulo and Division" (line 143) is the article's main content chapter — it covers 13 distinct properties — and it jumps straight to `### Trivial Case` with no framing sentence or summary bullets at all.
- **Item 6 (conclusion completeness):** The Conclusion's math block (lines 520–554) covers most properties but omits two that are proven and source-linked in the body: **Symmetrical Modulo Pairs** (`k mod b + (b-k) mod b = b`, §6, line ~380) and the **multi-filter density lemmas** (`densityForDivisor`, `densityForPrimeList`, `densityPreservedAfterFiltering`, `twoPrimesDensity` — the text at line 506 even says "all 11 lemmas are verified," but none of the density results appear in the summary). Given this is the foundational chapter for the whole sieve project, the density result in particular seems worth surfacing in the conclusion.

### `chapter3/list.md` — Minor revisions

- §2 "Definitions" (line 54) opens directly with `### 2.1 List construction` — no framing sentence. Minor since it's a definitions chapter, not a lemma chapter, but every other section in this article (§3–§11) does open with prose + bullets, so it stands out.
- Conclusion (§12) is otherwise excellent — matches the intro's group list closely — but omits **Same Period** (§10.1) from the shifted-list math block; Adjacent Difference and Gap Translation are there, Same Period isn't.

### `chapter4/cycle.md` — Minor revisions

Structurally strong: intro group list present, Mermaid `classDiagram` present for the three cycle variants (item 10), every content chapter opens with prose + bullets. Only issue is the inline-GitHub-URL pattern described above.

### `chapter4/integral.md` — Minor revisions

Same story as `cycle.md`: compliant structure, only the inline-URL issue.

### `chapter4/integral-cycle.md` — Minor revisions

- Good practice: §5.3 and §5.4 are explicitly tagged `[Finite-Period Verified]` / `[Draft]` in their own headers, and §5.4 ends with "**Status**: Mathematically proven. Stainless verification pending." — this is exactly the transparent handling `AGENTS.md`'s `property-completeness` rule (items 8–9) asks for, and it's the cleanest example of it in the corpus.
- **Item 10 violation:** this article defines two variant forms of Cycle Integral (Recursive, §3.1; Modulo, §3.2) and proves their equivalence (§3.3) — precisely the "multi-variant definition" case item 10 says needs a Mermaid `classDiagram`. Instead, §2 has a plain ASCII-art "Dependency Map" showing article-level dependencies, not a class diagram of the two variants. The two aren't substitutes for each other.
- Same inline-URL issue as above.

### `chapter5/euclid-theorem.md` — Accept

The strongest article in the set. §5 "Verification Status" explicitly declines to publish a VC count and explains why ("intentionally omitted because it changes as unrelated verified modules are added") — this is the checklist's own item 14 rule stated back almost verbatim, and no other article calls this out this clearly. Structure, intro list, and conclusion all check out. Only the inline-URL convention issue applies here too.

### `chapter6/gap-dynamics.md` — Minor revisions

- **Item 14 violation:** the table at lines 297–303 has a `Status` column ("Proved in §2", "Proved in §4", etc.). Item 14 is explicit: "No status columns in tables... the default assumption is verification." Since every row already says "Proved in §N," the column is redundant with the table's own existence and should be dropped (the §-reference could move into the Property column instead, e.g. "Copy-or-merge rule (§2)").
- **Item 2 (softer):** §2–§6 each open with a genuine framing paragraph (good), but none follow it with a bullet list summarizing that chapter's own subsections (e.g. §2 has 2.1/2.2/2.3 but no bullet preview of them). This is the softer half of item 2 — better than `sieve-sequence.md`'s bare `###` starts, but not fully compliant either.
- Framing-integrity is good here: abstract and conclusion are honest that the local-density question is open and explicitly say "no formal proof is claimed."

### `chapter6/sieve-sequence.md` — Minor revisions

- **Item 1 violation:** the Introduction gives a numbered list of "three facts" (lines 36–43) but never gives the bullet-list-with-section-numbers format every other article uses ("This article verifies: - ... — §N"). A reader can't skim the intro to map claims to sections the way they can in `list.md` or `cycle.md`.
- **Item 2 violations:** §4 "Linear Scan Properties" (line 252) and §5 "Gap-Cycle Reconstruction" (line 527) both go straight from the `## ` heading into a `### ` subsection with zero framing text — the clearest bare-opening violations in the finished set.
- Otherwise this is a genuinely careful article: §7 "Proof Boundary" is an unusually honest limitations section (explicitly separates the Bertrand's-postulate dependency from a Stainless-tooling boundary rather than hiding either), relative links are used correctly throughout, and no VC counts leak into the text.
- **Possible property-completeness gap (spot-checked, not confirmed):** `OBJECTS.md`'s Domain 6 catalog lists `SpecDerivedEquivalence`, `SpecDerivedExtendedWindowProperties`, `SpecDerivedRebuiltCycleProperties`, and `SieveUtils` as chapter-6 objects; none of these names appear anywhere in `sieve-sequence.md`. Some of these may be internal helpers that don't need article coverage (per `AGENTS.md`'s own framing, `SieveUtils` sounds like exactly that), but `SpecDerivedEquivalence` in particular is named as one of the "search these first" modules in `AGENTS.md`'s `search-primacy` rule, which suggests it holds article-worthy lemmas. Worth a look before calling this article's coverage complete.

### `draft/draft-empirical-g-local-analysis.md` and `draft/draft-sieve-gap-survival-math.md`

Both correctly self-identify as drafts, correctly state they contain no Stainless-verified code, and correctly avoid claiming more than they show. The empirical draft's Property Index table has a Status column with `[Empirical]` markers — fine for a draft under CONTRIBUTING's own logic (the no-status-column rule is a pre-publication checklist item; these files are explicitly not yet publishable), but it would need to be restructured before promotion to a finished article. Both have the link-rot issues noted above.

### `deprecated/*` (5 files)

All correctly carry a `DEPRECATED` banner pointing to the superseding article. All 5 have the broken-link issue above. `deprecated-sieve-sequence.md` additionally has the stale/contradictory note and ticket-reference/VC-count issues above.

---

## Limitations of This Review

- Property-completeness was spot-checked (modulo.md's density lemmas, list.md's shifted-list properties, sieve-sequence.md's chapter-6 object catalog), not exhaustively verified against every `.holds` function in `src/main/scala`. A full sweep — matching every proven lemma to an article section — would be a separate, longer pass; `OBJECTS.md` alone is ~97KB.
- I did not re-run `just verify`; verification status claims in the articles are taken as accurate based on the articles' own text and the absence of contradicting evidence, per the ticket-first rule's scope (this is a documentation review, not a proof audit).
- Mathematical correctness of the proofs themselves (as opposed to structural/editorial compliance) was read but not independently re-derived line by line for every lemma.
