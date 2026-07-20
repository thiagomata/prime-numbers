# Chapter 60: Minimal Spec + Stateless Properties

**Created:** 2026-07-16
**Status:** Complete

## START HERE

All phases complete. Chapter60 is self-contained, stateless, and verified.

## Architecture Achieved

**Correct direction:** Property objects call INTO the spec. The spec never calls INTO
property objects.

```
SpecSieveSequence (data model + core proofs + bridge proofs)
  ↑           ↑           ↑           ↑
  |           |           |           |
  HeadIsPrime  NextProps   PeriodProps  SurvivorCount
```

## What Was Done

1. All 4 property classes converted from `final case class` + `import seq.*` to `object` + explicit `seq` param
2. 47 delegation methods stripped from SpecSieveSequence
3. Method ordering: headline theorems at top, private helpers at end
4. SieveUtils + CycleUtils copied to chapter6 package — zero chapter6 imports
5. AGENTS.md updated with `proof-class-structure` rule

## Final State

| File | Lines | Role |
|------|-------|------|
| SpecSieveSequence.scala | ~642 | Data model + cornerstone proofs |
| SieveUtils.scala | ~1225 | Arithmetic utilities |
| CycleUtils.scala | ~102 | List bound predicates |
| SpecSieveSeqHeadIsPrime.scala | ~272 | Prime generation proof |
| SpecSieveSeqPeriodProperties.scala | ~370 | Period, block shift, gap cycle |
| SpecSieveSeqNextProperties.scala | ~1396 | Filter bridge, gap merge |
| SpecSieveSeqSurvivorCountProperties.scala | ~1048 | Survivor counting |

**Verification:** `just verify-ch 60`: 4704 valid, 0 invalid, 0 unknown
