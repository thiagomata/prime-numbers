# Chapter 60 Review — Open Questions

**Context:** Review of `tickets/active/chapter6-goal-driven-audit.md` and
`tickets/active/chapter6-stateless-properties.md`, 2026-07-17.

1. **Ticket status mismatch.** `chapter6-stateless-properties.md` has
   `**Status:** Complete` in the header but lives in `tickets/active/`
   (per `tickets/README.md`, `active/` = current work; `done/` = completed).
   Should it move to `tickets/done/`, or is it staying in `active/`
   intentionally because `chapter6-goal-driven-audit.md` still depends on it?

2. **Goal 3's "assumed" precondition — is closing it in scope?**
   `assertNextCycleReconstructsNextSpec` (and its two sibling assembly lemmas)
   in `SpecSieveSeqNextStageProperties.scala` all `require`
   `seq.next.apply(nextPeriod) == seq.next.head.value + seq.next.tailPrimorial`
   rather than deriving it. The article (`articles/chapter6/sieve-sequence.md`,
   §4.7/§6.2) already frames this as an acknowledged open boundary in chapter6.
   Is chapter6's job to (a) leave it as a documented precondition like chapter6
   does, or (b) actually attempt the derivation chapter6 never closed? The ticket
   text ("Open") reads ambiguously between "known limitation, stop here" and
   "next task."

3. **Relationship to the canonical epic ticket.** `tickets/README.md` names
   `active/sieve-sequence-proof.md` as "the canonical active ticket," and its
   EPIC table tracks Legs 1-5 entirely in `chapter6` (e.g.
   `SpecDerivedCycleSieve`, `CycleSieveSequence`). Neither chapter6 ticket is
   cross-referenced there, and `sieve-sequence-proof.md` doesn't mention
   chapter6 at all. Is chapter6 a parallel/successor track to that epic, or
   does it need to be merged into the epic's Leg tracking once finished? Right
   now two active tickets describe overlapping goals (spec=cycle, next-stage
   correctness) without linking to each other.

4. **"Noise" section — is non-migration final?** `chapter6-goal-driven-audit.md`
   lists several chapter6 lemmas explicitly marked "not needed for the 3 goals"
   (e.g. `assertApplyModIsCoprime`, `assertSingletonFilterDecision`,
   fine-grained survivor-count helpers). Should these be tracked anywhere as
   deliberately-not-ported (e.g. a note in `OBJECTS.md` or a `future/` ticket),
   or is silent omission acceptable per the "leave chapter6 untouched" directive
   in AGENTS.md?

5. **chapter4 reuse note.** The audit ticket flags that `RepeatedGapIntegralProperties`
   (chapter4) duplicates hand-rolled chapter6 assertions and says "fresh writes
   should use the newer chapter4 properties." Is there a follow-up ticket for
   actually swapping the *existing* chapter6 code to use these, or is this
   only meant to guide code not yet written?
