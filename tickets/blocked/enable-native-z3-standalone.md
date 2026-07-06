# Enable Native Z3 Interface in Standalone Stainless

**Created:** 2026-06-22
**Status:** Open
**Depends on:** none

## Goal

Remove the warning `"The Z3 native interface is not available. Falling back onto smt-z3."` when running `just verify` (standalone Stainless 0.9.8.8).

## Current State

- Z3 4.16.0 is installed via Homebrew at `/opt/homebrew/Cellar/z3/4.16.0/lib/libz3.dylib`
- Java can load `libz3` with `-Djava.library.path` set correctly
- The standalone JAR (`stainless-dotty-standalone-0.9.8.8.jar`) contains `inox.solvers.z3.NativeZ3Solver` and `NativeZ3Impl` classes
- But the JAR does NOT contain the `com.microsoft.z3` JNI wrapper classes required for native Z3
- The justfile already sets `DYLD_LIBRARY_PATH` and `JAVA_OPTS=-Djava.library.path`

## Root Cause

Stainless standalone 0.9.8.8 doesn't bundle the `com.microsoft.z3` JAR (the Microsoft Z3 Java bindings). The native Z3 interface tries to load classes like `com.microsoft.z3.Z3Exception`, fails to find them, and falls back to `smt-z3`.

This is the expected behavior per Stainless docs: "Use option `--solvers=smt-z3` on Mac."

## Impact on Performance

**Low.** The `smt-z3` solver (text-based SMT-LIB protocol) was the solver used during all previous fast runs (~30s). The native Z3 interface would not significantly improve verification times. The cache hit rate is the dominant factor in performance.

## Approaches Considered

### A: Download and bundle the Microsoft Z3 JAR

Download `com.microsoft.z3` JAR matching Z3 4.16.0 and add it to `$STAINLESS_JAR` classpath in the launcher script.

**Risk:** Version mismatch between the Z3 binary (4.12.2 bundled with Stainless 0.9.8.8) and the JAR (would need 4.16.0 for Homebrew-installed Z3). Also, the JNI library name/signatures might differ between Z3 versions.

### B: Upgrade Stainless to a version with bundled Z3 JAR

Newer Stainless versions (0.9.9.x) might bundle the Microsoft Z3 JAR. This would require a full upgrade, which has compatibility risks (see discussions about upgrading).

### C: Accept the warning

The warning is cosmetic. `smt-z3` works and performance is acceptable with a warm cache (~40s). Leave the `DYLD_LIBRARY_PATH` and `JAVA_OPTS` in the justfile (no-op but harmless) and suppress the warning if possible.

## Recommendation

**Approach C — Accept the warning.** The warning has no performance impact. If upgrading Stainless is pursued later (for other reasons), the native Z3 fix may come for free.
