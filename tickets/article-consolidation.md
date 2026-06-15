# Article Consolidation — Merge Draft Articles into Coherent Groups

**Created:** 2026-06-15
**Updated:** 2026-06-15
**Status:** Plan — Ticket created, awaiting execution
**Depends on:** Evaluation completed (see summary below). AGENTS.md updated with `three-representations` rule (2026-06-15).

--- 

## New Guidelines Added to AGENTS.md (2026-06-15)

### `three-representations` rule
Every property MUST be presented in all three forms:
1. **English text** — with **Intuition:** and **Why This Matters:**, placed above the math
2. **Mathematical symbols** — LaTeX `\begin{aligned}` blocks with bracketed labels (`[Q.E.D.]`, `[By Definition]`, `[By Induction Hypothesis]`, etc.)
3. **Scala verification code** — `.holds` function + source reference link to `.scala` file

### `property-completeness` rule (9 items)
Before publishing, verify the article covers ALL important properties by:
1. Search `src/main/scala/` for `.holds` functions in relevant packages
2. Cross-reference with OBJECTS.md
3. Cross-reference with `learnings-capacity-argument.md` (Section 16 catalog, Section 9 failed approaches, Section 15 boundary)
4. Identify logical gaps (what a reader would expect)
5. Add missing verified properties
6. Flag unverified expected properties as gaps (ticket)
7. Document failed verification attempts as limitations
8. Unverified math → mark as **"Draft — mathematically proven, Stainless verification pending"**
9. If you CAN draft missing Scala `.holds` code → do it, but annotate with `// DRAFT` and create a tracking ticket

---

## Goal

Merge the existing 8 draft articles into fewer, coherent, finished-quality articles by consolidating overlapping topics. Currently there are 5 finished articles and 8 drafts with significant topical overlap and inconsistent quality.

---

## Current State

### Draft Inventory

| # | Article | Lines | Quality | Topic |
|---|---------|-------|---------|-------|
| 1 | `draft-sieve-foundation.md` | 438 | ~80% | Unit cycle, filter preserves primes |
| 2 | `draft-sieve-sequence.md` | 371 | ~40% | Wheel factorization, gap representation — explicitly outdated |
| 3 | `draft-euclid-theorem.md` | 420 | ~90% | Euclid's theorem proof |
| 4 | `draft-gap-persistence.md` | 102 | ~10% | 2-gap survival outline |
| 5 | `draft-twin-prime-persistence.md` | 112 | ~10% | Twin candidate survival outline |
| 6 | `draft-generalized-gap-dynamic.md` | 303 | ~50% | Worst-case growth, dispersion, overclaims TPC |
| 7 | `draft-generalized-gap-dynamic.suggestions.md` | 261 | N/A | Reviewer rebuttal suggestions (meta) |
| 8 | `draft-empirical-g-local-analysis.md` | 239 | ~90% | Empirical G_local data up to p=997 |

### Finished Articles (reference template)

| # | Article | Lines | Topic |
|---|---------|-------|-------|
| A | `modulo.md` | 504 | Div/Mod properties |
| B | `list.md` | 1177 | Recursive lists |
| C | `integral.md` | 1030 | Discrete integral |
| D | `cycle.md` | 808 | Unbounded cycles |
| E | `integral-cycle.md` | 880 | Cycle integrals |

---

## Proposed Merge Groups

### Group 1: Sieve Core (merge #1 + #2)
**Title:** "Formal Verification of Sieve Sequence Properties from First Principles"

| Source | Content to Keep | Issues to Fix |
|--------|----------------|---------------|
| `draft-sieve-foundation.md` | Unit cycle generates N, strict monotonicity, filter preserves primes, distinct primes coprime | Duplicate refs (ref1=ref3) |
| `draft-sieve-sequence.md` | Wheel factorization representation, head-is-prime proof | Section numbering (4.9 orphan), update to current codebase, remove deprecation note |

**Outcome:** Single article covering both sieve foundation AND sieve sequence as a coherent narrative: candidate generation → wheel representation → preservation → head-is-prime.

### Group 2: Gap Dynamics & Twin Primes (merge #4 + #5 + #6 + learnings content)
**Title:** "Gap Dynamics and Twin Prime Candidates in Sieve Sequences" (or similar)

| Source | Content to Keep | Issues to Fix |
|--------|----------------|---------------|
| `draft-gap-persistence.md` | 2-gap definition, concept of persistence (absorb into intro) | Rewrite from scratch — 102 lines is outline only |
| `draft-twin-prime-persistence.md` | Survival inequality framing (absorb into section) | Rewrite from scratch — 112 lines is outline only |
| `draft-generalized-gap-dynamic.md` | Worst-case growth inequality, structural dispersion, CRT uniformity | Replace `%` operator with `Calc.mod`, remove `@inductive`, remove TPC overclaim |
| `learnings-capacity-argument.md` | Sections 2 (isolation), 11 (cluster approach), 14 (cross-layer), 16 (proven catalog), 17 (structural impossibility) | Extract as sections in merged article |

**Key constraint:** The merged article must honestly frame the **open local density question** as described in learnings Section 10 and 16. It must NOT claim the Twin Prime Conjecture is solved.

### Keep Separate (no merge)

| Article | Rationale |
|---------|-----------|
| `draft-euclid-theorem.md` | Standalone classical result, independent of sieve machinery |
| `draft-empirical-g-local-analysis.md` | Different methodology (empirical data collection), complements Group 2 as supporting evidence |
| `draft-generalized-gap-dynamic.suggestions.md` | Meta-content (reviewer strategy), should be archived not published |

---

## Pre-Merge Fixes — Progress

### ✅ Done (2026-06-15)

| Task | Article | Changes Made |
|------|---------|-------------|
| 1 | **sieve-foundation** | Fixed ref1 from list.md → Stainless framework paper (Hamza et al. 2019). Updated VC count 4939 → 5303. |
| 2 | **euclid-theorem** | Fixed VC counts everywhere: intro 4837→5303, stats 4837→5303 (425→468 funcs), conclusion 4939/4939→5303/5303, future work 4939→5303, appendix log 4749→5303. Removed draft refs [7][8][9] from related work table and references section. |
| 3 | **generalized-gap-dynamic** | Replaced `%` → `Calc.mod` (3 occurrences). Removed `@inductive`. Rewrote abstract, intro, conclusion to be honest about global vs. local distinction per `framing-integrity`. Added refs [7] (empirical) and [8] (learnings). |
| 4 | **sieve-sequence** | Strengthened deprecation notice. Updated VC references 4939→5303. |

### AGENTS.md Rules Added

| Rule | Items |
|------|-------|
| `three-representations` | 3 forms: English → LaTeX → Scala `.holds` + source ref |
| `property-completeness` | 9 items: search code, cross-ref OBJECTS.md, cross-ref learnings.md, gaps→ticket, unverified math→mark draft, draft Scala code if possible |
| `framing-integrity` | Abstract/intro/conclusion must match content; no overpromising |

### Current Baseline Verification

`just verify` output: **5303 / 5303 valid, 468 functions, 0 invalid, 0 unknown** (run 2026-06-15, 15.48s)

---

## Risks

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Group 2 article could overclaim TPC solution | High | Use learnings.md as guardrail; require explicit "open question" section |
| Group 1 merge loses detail from sieve-sequence's head-is-prime proof | Low | Both articles have it; keep the more complete version |
| Euclidean theorem article VC numbers still wrong after fix | Low | Run `just verify` and record the actual count |
| `generalized-gap-dynamic` has `%` operator in code that was never actually verified in Stainless | Medium | The code using `%` would fail Stainless; may indicate the code was never run through verification |

---

## Validation Plan

1. After each individual fix: `just verify` must pass (green-to-green rule)
2. After merge: article reads coherently without section gaps
3. Group 2 article must explicitly state the open local density question (Section 10 of learnings)
4. No article may reference another draft article as a citation
5. All VC counts in articles must match actual `just verify` output
6. Cross-reference with `learnings-capacity-argument.md` Section 16 (proven catalog): every listed property belonging to the article's subject must appear in the article. Document any gaps.
7. Cross-reference with `learnings-capacity-argument.md` Section 9 (failed approaches): any approach that has been proven futile must be acknowledged or explicitly excluded in the article.

---

## Alternatives Considered

| Alternative | Reason Rejected |
|-------------|-----------------|
| Keep all drafts separate | 8 drafts with overlapping content creates confusion about which is authoritative |
| Discard gap-persistence and twin-prime-persistence outright | Both contain framing ideas worth preserving; absorb into Group 2 |
| Merge everything into one giant article | Would mix independent topics (Euclid + sieve + empirical + twins) into an incoherent document |
