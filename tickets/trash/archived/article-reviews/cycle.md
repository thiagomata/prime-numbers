# Review: articles/cycle.md

## Source

- Article: `articles/cycle.md`
- Current role: Foundational article

## Verdict

Promising foundation article, but needs editorial tightening before magazine publication.

## Must Fix

- Add explicit source-reference blocks after every major verified property, following the current `PROOF_GUIDE.md` format.
- Cross-check every cited lemma name against `OBJECTS.md` and `src/main/scala/` so the article does not rely on renamed or stale proof functions.
- Make the title more precise. "Unbound Lists" is awkward and should become something like "Formal Verification of Cyclic Lists".
- Ensure each property has all three forms: English overview with `Intuition:` and `Why This Matters:`, mathematical proof, and Scala verification code.

## Should Fix

- Treat the repetition in the long equivalence section as an editorial choice, not an automatic flaw. The self-contained proof blocks are useful, especially for readers entering from one side of the equivalence. Recommended fix: add a short roadmap before the proof explaining that some repetition is intentional, and only remove repeated text where it does not improve local readability.
- Split long code listings from proof explanation so readers can scan the argument.
- Add a short scope note clarifying that the article proves cycle access, equivalence, and periodicity properties; applications to sieve sequences are handled in later articles.

## Validation

- Run `just verify` or confirm the latest `verify.log` still reports all VCs valid.
- Search for every function cited by the article in `src/main/scala/`.
- Compare the article property list against the Cycles section of `OBJECTS.md`.

---

## Execution Plan (2026-06-16)

### Current State

- `just verify`: **5499 valid, 0 invalid, 0 unknown** (confirmed)
- Article title: "Using Formal Verification to Prove Properties of Unbound Lists"
- Article length: 808 lines
- Inline Scala code throughout (no appendix)
- 7 properties covered, 2 missing from OBJECTS.md

### Changes Needed

1. **Title**: "Using Formal Verification to Prove Properties of Unbound Lists" → "Formal Verification of Cyclic Lists"
2. **Property index table**: Add at start of article (like list.md)
3. **Section restructure**: 
   - 1 Introduction
   - 2 Preliminaries
   - 3 Cycle Definitions (3.1 Recursive, 3.2 Modulo)
   - 4 Cycle Equivalence
   - 5 Cycle Properties (5.1-5.7)
   - 6 Conclusion
   - Appendix A: Scala Verification Code
   - Appendix B: Verification Log
4. **Move Scala code to Appendix A**: All inline `.scala` code blocks → Appendix A; keep source-reference links in body
5. **[CANCELLED] Add missing properties** — User clarified internal lemmas don't need article coverage.
   `cycleValuePositiveOrZero` and `rotateAtValue` are internal helpers; keep them in code only.
6. **Add scope note** in Conclusion
7. **PROOF_GUIDE format**: English prose (no explicit labels), LaTeX math, source reference

### Cross-Reference: OBJECTS.md Cycles vs Article

| Property | File | In Article? | Action |
|----------|------|-------------|--------|
| `findValueInCycle` | CycleProperties.scala | Yes (5.1) | Move code to Appendix A |
| `smallValueInCycle` | CycleProperties.scala | Yes (5.2) | Move code to Appendix A |
| `valueMatchAfterManyLoops` | CycleProperties.scala | Yes (5.3) | Move code to Appendix A |
| `valueMatchAfterManyLoopsInBoth` | CycleProperties.scala | Yes (5.4) | Move code to Appendix A |
| `propagateModFromValueToCycle` | CycleProperties.scala | Yes (5.5) | Move code to Appendix A |
| `assertCycleOfPosEqualsCycleOfModPos` | CycleProperties.scala | Yes (5.5) | Move code to Appendix A |
| `cycleValuePositiveOrZero` | CycleProperties.scala | **NO (internal)** | Skip — internal helper |
| `rotateAtValue` | CycleProperties.scala | **NO (internal)** | Skip — internal helper |

### Risks

- Large single edit to `articles/cycle.md` (808 lines → ~900 lines)
- Must verify with `just verify` after changes (tool takes ~18s)
- No Scala code changes needed — only markdown edits

### Progress Log

- 2026-06-16: Ticket created. `just verify` confirmed 5499 valid. Starting edits.
- 2026-06-16: Full restructure complete. Title fixed. Property index added. 6 Scala code blocks moved to Appendix A (A.1-A.7). Scope note added to conclusion. Appendix B with verify log added. User clarified internal lemmas stay in code only (removed 5.6/5.7 from plan). `just verify` after changes: 5499 valid, 0 invalid, 0 unknown.
