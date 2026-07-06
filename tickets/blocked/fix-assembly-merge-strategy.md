# Fix `sbt assembly` deduplicate error for stainless annotations

**Created:** 2026-06-22
**Status:** Open
**Depends on:** none

## Goal

Fix `sbt clean reload assembly jacoco` which fails with 229 deduplicate errors when creating the fat JAR. The error:

```
deduplicate: different file contents found in the following:
stainless/annotation/anyHeapRef.class
stainless/annotation/anyHeapRef.tasty
...
```

## Root Cause

Both `project/lib/sbt-stainless.jar` and `project/lib/stainless-library.jar` contain the `stainless.annotation` package, but with different content (different versions). The default `assemblyMergeStrategy` uses `MergeStrategy.deduplicate` which fails when files differ at the same path.

## Fix

Add an `assemblyMergeStrategy` to `build.sbt` that picks the first copy for stainless annotations:

```scala
assembly / assemblyMergeStrategy := {
  case path if path.startsWith("stainless/annotation/") => MergeStrategy.first
  case x => (assembly / assemblyMergeStrategy).value(x)
}
```

## Verification

- [ ] `sbt clean reload assembly jacoco` completes without errors
- [ ] `just verify` still passes (7755 valid, 0 invalid)
- [ ] `just test` still passes (173 tests)
