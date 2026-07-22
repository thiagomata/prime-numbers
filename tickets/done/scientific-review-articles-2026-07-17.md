# Scientific Magazine Review of articles/

**Created:** 2026-07-17
**Updated:** 2026-07-17
**Status:** Complete
**Depends on:** none (documentation-only review, no code changes)

## Related Tickets

- None found under `tickets/active/`, `tickets/done/`, or `tickets/blocked/` that
  perform a full editorial review of `articles/`. `articles/learnings/reviewer-notes-gap-dynamic.md`
  contains informal reviewer commentary on the gap-dynamics work but is not a
  structured checklist-based review.

## Goal

Act as an editorial reviewer for a scientific magazine and evaluate every article
under `articles/` (finished, draft, and deprecated) against this repository's own
publication standards: the 14-item Article Quality Checklist in `CONTRIBUTING.md`,
the three-representations rule in `PROOF_GUIDE.md`, and the `framing-integrity`,
`property-completeness`, `no-ticket-references`, and `no-emojis` rules in
`AGENTS.md`. Produce a per-article verdict (accept / minor revisions / major
revisions / reject-as-is) with specific, line-referenced issues.

This is a documentation-only task. No `.scala` source or proofs are modified, so
`just verify` is not required (markdown-only change per the green-to-green rule
exception).

## Current State

Repository contains:
- Finished articles (chapter2-6): `modulo.md`, `list.md`, `cycle.md`, `integral.md`,
  `integral-cycle.md`, `euclid-theorem.md`, `gap-dynamics.md`, `sieve-sequence.md`.
- Drafts: `draft-empirical-g-local-analysis.md`, `draft-sieve-gap-survival-math.md`.
- Deprecated: 5 files under `deprecated/`.
- Learnings: `learnings-capacity-argument.md`, `reviewer-notes-gap-dynamic.md`.

## Expected State

A review report saved as markdown (in the working outputs folder, then shared
with the user — not committed into `articles/` itself, since it is a review
artifact, not an article) containing, per finished article: checklist pass/fail
per item, three-representations compliance, and an overall verdict. Drafts and
deprecated files get a shorter status note. A `questions.md` capturing any
ambiguities or concerns flagged during review, per project instructions.

## Approaches Considered

### Full property-completeness audit against OBJECTS.md for every article

**Status:** REJECTED (too costly for this pass)

Cross-referencing every `.holds` lemma in `src/main/scala` against every article
would require reading all of `OBJECTS.md` (96KB) and matching against source.
Given this is an editorial review, not a proof-completeness audit, I will spot-check
property-completeness using `OBJECTS.md` and `learnings-capacity-argument.md`
Section 16 (the documented catalog) rather than a full line-by-line source sweep,
and will flag this limitation explicitly in the report.

### Checklist-driven review of finished articles, lighter pass on drafts/deprecated

**Status:** RECOMMENDED

Read each finished article in full, check against CONTRIBUTING.md's 14 items,
PROOF_GUIDE.md three-representations, and the relevant AGENTS.md rules. Drafts
and deprecated files get a short paragraph noting their declared status and
whether that status still looks accurate.

## Assumptions

- "for your scientific magazine" means applying this repo's own stated editorial
  standards (CONTRIBUTING.md / PROOF_GUIDE.md / AGENTS.md), not an external
  journal's standards.
- The review output itself is a deliverable for the user, not a new `articles/`
  entry, so it should not be placed inside `articles/`.

## Risks

- Property-completeness spot-check may miss real gaps that a full source sweep
  would catch — flagged as a known limitation, not silently skipped.

## Validation

- Every claim in the review (e.g. "missing three-representations", "no ticket
  reference violation") is backed by a specific line or section quote from the
  actual file, not a general impression.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-17 | Ticket created. No prior full-review ticket exists; reviewer-notes-gap-dynamic.md is informal commentary, not checklist-based. Scope set to finished articles (full) + drafts/deprecated (lighter). | Read all finished articles next. |
| 2026-07-17 | Read all 8 finished articles in full; ran repo-wide scripted checks for broken relative links, emoji ranges, VC-count leaks, ticket references, status-column tables, and per-chapter heading structure. Found: all 5 deprecated articles link to the wrong path for their superseding article (`../sieve-sequence.md` / `../gap-dynamics.md` instead of `../chapter6/...`); `deprecated-sieve-sequence.md` has a stale banner referencing a nonexistent `draft-sieve-foundation.md` and a ticket file, plus a leaked VC count; `chapter2/modulo.md` lacks the intro compact-group-list and its Ch.6 opens with no framing, and its conclusion omits the Symmetrical Modulo Pairs and density-lemma results; `chapter6/sieve-sequence.md` lacks the intro group list and two chapters open with a bare `###`; `chapter4/integral-cycle.md` needs a Mermaid diagram for its two variant definitions (has only an ASCII dependency map); `chapter6/gap-dynamics.md` has a `Status` column in a properties table; `chapter4/cycle.md`, `integral.md`, `integral-cycle.md`, and `chapter5/euclid-theorem.md` use inline absolute GitHub URLs instead of relative paths, unlike the newer `sieve-sequence.md`. `euclid-theorem.md` is the strongest article — explicitly declines to publish VC counts and explains why. Both drafts correctly self-label and withhold Stainless code, but have their own broken relative links. Full findings written to `editorial-review-articles-2026-07-17.md`, open questions to `editorial-review-questions-2026-07-17.md`, both copied to repo root. | Done — awaiting user decision on the open questions (see questions file) before any of these become code/doc edits. |
| 2026-07-17 | Discussed which citations `gap-dynamics.md` is missing, balancing against the author's wish to keep articles self-contained. Landed on 3, each anchoring a claim already in the text rather than general related-work padding: Halberstam & Richert (1974) *Sieve Methods* for the parity-problem limitation behind "equivalent to TPC" (§8); Rubinstein & Sarnak (1994) "Chebyshev's bias" for "empirical evidence is not a formal proof" (§6) — a residue-class distribution bias that looks stable over any reasonable computational range and still isn't asymptotically fixed, a tighter analogy than an initially-suggested Mertens-conjecture citation, which the author correctly flagged as a weak link (different mechanism — zeta-zero cancellation, not counting/uniformity); Zhang (2014) "Bounded gaps between primes" to note the one real advance on this problem used non-sieve techniques. Recorded as an addendum in `scientific-merit-review-2026-07-17.md`. Not yet inserted into the actual article — pending author go-ahead. | Awaiting decision on whether to insert these into `gap-dynamics.md` directly. |
| 2026-07-17 | User caught two errors in the chapter-6 critique via discussion (not yet re-verified against source independently, corrected based on re-reading gap-dynamics.md §5.1/§5.3): (1) "equivalent to TPC claim" critique wrongly applied the learnings-doc's narrow "head position" argument to the article's actual open question, which per §5.1 only needs a 2-gap anywhere in the safe window `[h, h²)` — retracted. (2) The "no quantitative bridge between global §4 and local §6" framing was also wrong — that separation is intentional, honest scope discipline (§5.3 explicitly states global does not imply local), not a clarity defect — retracted, replaced with credit for handling it well. What stands and was reinforced: the empirical evidence (p≤997) is fine as illustration but the article's own "suggesting the inequality is structural, not coincidental" (gap-dynamics.md §6) oversteps into using that illustration to argue the open claim, contradicted by the very next sentence's own hedge — recommended dropping that phrase (and the equivalent framing in draft-empirical-g-local-analysis.md). The parity-problem caution stands as a caveat on the local question itself. Updated `scientific-merit-review-2026-07-17.md` accordingly. | Corrected and re-saved. |
| 2026-07-17 | User correctly pushed back: rule-compliance is not the same as scientific merit. Did a second pass judging actual contribution, checking novelty against prior art (web search: EPFL-LARA's own `bolts` Stainless-example repo has no prime/modular-arithmetic content, so this material isn't a duplicate there; but Euclid's theorem has been formalized many times over — Lean mathlib's `Nat.exists_infinite_primes`, Coq, Isabelle/HOL, plus a dedicated survey paper of Euclid-theorem proofs from 300 BC-2022 — so chapters 2-5 are correct, well-engineered, but not novel mathematics; their real audience is formal-methods/verification tooling, not number theory, and the articles don't say that explicitly). Chapter 6 (gap-dynamics/sieve-sequence) is the actual research content, and it's a pure sieve/counting argument for twin-prime persistence — which runs directly into Selberg's parity problem (1949), the well-known obstruction that pure sieve methods can't distinguish primes from products of an even number of primes and so cannot lower-bound primes or twin primes without extra analytic input (confirmed via Terence Tao's writeup and the sieve-theory literature; this is also why Zhang/Maynard-Tao's bounded-gaps results needed genuinely new machinery, not just better sieves). Neither `gap-dynamics.md` nor `learnings-capacity-argument.md` mentions the parity problem. Also flagged: the "equivalent to the Twin Prime Conjecture" claim conflates a window-wide 2-gap *count* with a 2-gap landing at the specific head position actually needed for a twin prime — that logical step isn't shown; and the p≤997 empirical evidence carries little weight given number theory's history of patterns breaking at large scale (Mertens conjecture, Skewes' number). Also flagged `reviewer-notes-gap-dynamic.md` as a process risk — it reads as an AI validating the user's framing ("airtight," "unassailable") rather than independent adversarial review. Full writeup in `scientific-merit-review-2026-07-17.md`, copied to repo root. | Done — this is the substantive review; the earlier compliance pass is a secondary, narrower artifact. |
