# Spark Sieve Sequence Data Generator

**Created:** 2026-07-17
**Updated:** 2026-07-19
**Status:** Working — 32/32 tests pass, DataFrame-native pipeline
**Verification:** Not required (this is a data-generation sub-project, not a proof project)
**Testing:** Unit tests required — ScalaTest in `spark/src/test/scala/`

## Related Tickets

- `sieve-sequence-epic.md` — The three-representation sieve proof (Spec/Canonical/Cycle). Current: 12138 valid. The Spark generator reimplements the Cycle pipeline for data generation, not verification.
- `active/sieve-sequence-proof.md` — Active proof ticket for the verified sieve sequence. The Spark code is intentionally disconnected from this.
- `active/explain-sieve-sequence-architecture.md` — Documentation cleanup for chapter6 naming. Background context on the three representations.
- `done/canonical-spec-to-cycle-alignment.md` — Completed alignment of canonical and cycle representations.

## Goal

Create a self-contained Apache Spark application (`v1.chapter8`) that reimplements the sieve sequence algorithm using `Array[Long]` and generates gap cycles + first 1000 values for each sieve stage, saving results to CSV files.

**Key constraints:**
1. **Complete isolation** from the Stainless-verified code. No shared imports, no `@extern`, no Stainless dependency. The Spark code lives in a separate sbt sub-project under `spark/`.
2. **No Stainless verification** — this is a data-generation project, not a proof project. Verification is not required.
3. **Unit tests required** — ScalaTest in `spark/src/test/scala/` covering the core algorithm (nextStage, gap lineage, copy/merge detection).
4. **Gap lineage metadata** — track how gaps evolve across stages to support analysis for the gap-dynamics article (see §Gap Lineage Metadata below).

## Current State

- Verified sieve sequence code exists in `src/main/scala/v1/chapter6/`
- Chapter 7 (`src/main/scala/v1/chapter7/empirical/`) attempted empirical data generation but is confusing and focused only on twin-prime data for a different article
- The verified code is extremely slow (expected — performance was never the goal)
- No Spark dependency exists in the project
- Stainless scans `src/main/scala/**/*.scala` via `find-src.sh`

## Expected State

After completion:

1. **Separate sub-project** at `spark/src/main/scala/v1/chapter8/` with its own Spark dependencies
2. **Three Scala files** implementing the sieve algorithm with `Array[Long]` + Spark
3. **CSV output** in `data/sieve/` with gaps, values, gap lineage metadata, and summary for each stage
4. **Unit tests** in `spark/src/test/scala/v1/chapter8/` covering core algorithm, gap lineage, and copy/merge detection
5. **Justfile recipe** `spark-run` to execute the generator
6. **Zero impact** on Stainless verification — `just verify` unchanged, no Spark on the verified classpath

## Approaches Considered

### Approach A: Separate sbt sub-project (RECOMMENDED)

**Status:** RECOMMENDED

Create a `spark` sub-project in `build.sbt` with its own source directory (`spark/src/main/scala/`). Stainless's `find-src.sh` only scans `src/main/scala/`, so the Spark code is invisible to verification.

**Strengths:**
- Clean isolation — no shared classpath between Stainless and Spark
- Idiomatic sbt — sub-projects are the standard way to separate concerns
- Can run independently: `sbt spark/run` vs `sbt compile` (Stainless)
- Future flexibility — could add its own tests, dependencies

**Risks:**
- Slightly more complex `build.sbt` (sub-project definition)
- Need to verify Stainless doesn't pick up the sub-project sources

**Fallback:** If sub-project causes build issues, use a simple `spark/` directory with its own `build.sbt` (fully separate project).

### Approach B: Additional source directory in main project

Add `spark/src/main/scala` as an additional `Compile / unmanagedSourceDirectories` in the main project.

**Status:** UNTESTED

**Strengths:** Simpler than sub-project
**Risks:** Spark dependencies leak into the main project classpath; Stainless might still scan it depending on configuration
**Fallback:** N/A — Approach A is cleaner.

## Algorithm (from chapter6)

Each sieve stage `S_k` has:
- **head** `h`: the current prime (starting value)
- **tail primes** `P̄`: primes already used as filters (descending order)
- **modulus** `M = product(P̄)`: primorial of tail primes (M=1 when P̄ is empty)
- **gap cycle** `G`: `T` gaps where `T = |G|` and `sum(G) = M`

Next stage pipeline:
1. **Residues**: values in `[0, M)` coprime to all tail primes → `T` residues
2. **Expand**: repeat residues `h` times → `h * T` candidates over `[h, h + h*M)`
3. **Filter**: remove values divisible by `h` → `T * (h-1)` survivors
4. **Gaps**: adjacent differences + wrap-around gap → new gap cycle of length `T * (h-1)`
5. **Rotate**: align cycle so next head is at position 0

Base cases:
- `S_0`: head=2, P̄=[], M=1, T=1, G=[1] → generates [2,3,4,5,...]
- `S_1`: head=3, P̄=[2], M=2, T=1, G=[2] → generates [3,5,7,9,...]
- `S_2`: head=5, P̄=[3,2], M=6, T=2, G=[2,4] → generates [5,7,11,13,...]

## Gap Lineage Metadata

The gap-dynamics article (`articles/chapter6/gap-dynamics.md`) studies how gaps evolve across sieve stages via the copy-or-merge rule. To support empirical analysis of gap evolution and help identify new properties, we track **gap lineage** — the history of how each gap in each stage was formed.

### Per-Gap Metadata (stage_NNN_gaps.csv columns)

Each row in the gaps CSV carries additional columns beyond just `index` and `gap`:

```
index,gap,origin,age,mergeCount,mergeAncestors,ancestorValues
0,6,merge,1,2,"0;1","2;4"
1,4,copy,2,0,"",""
2,2,copy,3,0,"",""
3,4,merge,1,2,"2;3","2;4"
...
```

| Column | Type | Description |
|--------|------|-------------|
| `index` | Int | Position in the gap cycle |
| `gap` | Long | The gap value (difference between consecutive survivors) |
| `origin` | String | `"copy"` if this gap was copied from the previous stage (both endpoints survived), `"merge"` if formed by merging 2+ old gaps (interior endpoints were filtered out), or `"new"` for stage 0 |
| `age` | Int | How many consecutive stages this gap has persisted. Starts at 1 when a gap first appears. Increments each stage if a gap of the same value at the same relative position is a copy. Resets to 1 on merge or when the gap value changes. |
| `mergeCount` | Int | Number of old gaps that were merged to form this one. 0 for copies, 2+ for merges. |
| `mergeAncestors` | String | Semicolon-separated indices of the old gaps that were merged. Empty for copies. |
| `ancestorValues` | String | Semicolon-separated values of the old gaps that were merged. Empty for copies. |

### Gap Lineage Tracking Algorithm

During `nextStage()`, the pipeline tracks lineage:

1. **Expand**: repeat current gaps `head` times. Each expanded copy inherits the original gap's index and lineage.
2. **Filter**: mark survivors and non-survivors. Non-survivors are the interior points being removed.
3. **Compute new gaps**: walk the filtered list. For each new gap:
   - If it spans exactly one old gap (no interior points removed) → **copy**: inherit age+1, mergeCount=0, same ancestors.
   - If it spans 2+ old gaps (interior points removed) → **merge**: age=1, mergeCount=k, ancestors = the k old gap indices, ancestorValues = their values.
4. **Rotate**: lineage rotates with the gap cycle.

### Aggregated Gap Statistics (gap_stats.csv)

A per-stage summary of gap dynamics:

```
stage,head,period,modulus,gapCount,copyCount,mergeCount,newGapValues,lostGapValues,maxAge,avgAge,twoGapCount,twoGapSurvived
0,2,1,1,1,0,0,1,0,1,1.0,0,0
1,3,1,2,1,0,0,1,1,1,1.0,1,0
2,5,2,6,2,0,0,2,0,1,1.0,1,1
3,7,8,30,8,2,6,4,1,1,1.0,3,2
...
```

| Column | Description |
|--------|-------------|
| `copyCount` | Number of gaps that were copied (not merged) |
| `mergeCount` | Number of gaps that were formed by merging |
| `newGapValues` | Count of gap values appearing for the first time at this stage |
| `lostGapValues` | Count of gap values present in previous stage but absent in this one |
| `maxAge` | Maximum age of any gap in this stage |
| `avgAge` | Average age of gaps in this stage |
| `twoGapCount` | Number of 2-gaps in this stage |
| `twoGapSurvived` | Number of 2-gaps that survived from previous stage (copy origin) |

### Why This Matters for Gap Dynamics

The gap-dynamics article proves:
- **Copy-or-merge rule** (§2): every new gap is copy or merge — the metadata makes this observable per-gap
- **Non-generation** (§3): absent gap values stay absent — `lostGapValues` tracks when values disappear, `newGapValues` tracks when new values appear
- **Full-period survival** (§4): each d-gap has h-2 surviving descendants — `twoGapSurvived` tracks actual 2-gap survival across transitions
- **Local density** (§6): whether enough 2-gaps exist in [p, p²] — `twoGapCount` per stage gives the global count, local count needs position-aware analysis

The metadata enables empirical questions like:
- What is the age distribution of gaps? Do 2-gaps tend to be older (more persistent)?
- How often do merges create new 2-gaps vs destroy existing ones?
- Is there a correlation between a gap's age and its survival probability?

### 2-Gap Focused Compression

The gap-dynamics article focuses on 2-gaps (twin prime candidates). To make the structure of 2-gap neighborhoods visible, we produce a **compressed** version of each stage's gap cycle where consecutive non-2 gaps are merged into their sum.

**Rule:** Walk the gap cycle. If a gap equals 2, emit it as-is. If a gap does not equal 2, accumulate it with the previous consecutive non-2 gaps into a running sum, then emit the sum when the next 2 (or end of cycle) is reached.

**Example:**

```
Original:  [6, 4, 2, 4, 2, 4, 6, 2]
Compressed: [10, 2, 4, 2, 10, 2]
            ↑      ↑        ↑
            6+4=10  4        4+6=10
```

The compressed view shows the **distance between consecutive 2-gaps** in terms of summed non-2 gaps. This directly answers: "how far apart are twin prime candidates in this stage?"

**Example stages:**

| Stage | Original gaps | Compressed (2-focused) |
|-------|--------------|----------------------|
| S_0 | [1] | [1] |
| S_1 | [2] | [2] |
| S_2 | [2, 4] | [2, 4] |
| S_3 | [6, 4, 2, 4, 2, 4, 6, 2] | [10, 2, 4, 2, 10, 2] |
| S_4 | (48 gaps) | compressed version |

**Implementation:** `GapLineage.compressAround2(gaps: Array[Long]): Array[Long]` — pure function, no lineage needed. Returns the compressed gap cycle.

**Output file:** `stage_NNN/gaps_2focused.csv` — generated alongside the regular gaps CSV, not replacing it.

```
index,gap,originalSpan
0,10,2
1,2,1
2,4,1
3,2,1
4,10,2
5,2,1
```

Where `originalSpan` = how many original gaps were merged to produce this compressed gap (1 = was already a 2 or single non-2, 2+ = merged block).

This compressed representation is useful for:
- Visualizing2-gap spacing patterns across stages
- Tracking how the "distance between twin prime candidates" evolves
- Identifying stages where 2-gaps become more/less clustered
- Empirical analysis of the local density question (§6 of gap-dynamics)

## Output Structure

```
data/sieve-spark/
  stages_summary/             # Spark DataFrame CSV (directory with part files)
  gap_stats/
  stage_000/
    gaps/
    gaps_2focused/
    values/
  stage_001/
    gaps/
    gaps_2focused/
    values/
  ...
```

Each path is a Spark DataFrame CSV directory containing `part-00000-*.csv` + `_SUCCESS` marker.

### stages_summary.csv

```
stage,head,period,modulus,gapCount,gapsFile,gaps2focusedFile,valuesFile
0,2,1,1,1,data/sieve/stage_000/gaps.csv,data/sieve/stage_000/gaps_2focused.csv,data/sieve/stage_000/values.csv
1,3,1,2,1,data/sieve/stage_001/gaps.csv,data/sieve/stage_001/gaps_2focused.csv,data/sieve/stage_001/values.csv
2,5,2,6,2,data/sieve/stage_002/gaps.csv,data/sieve/stage_002/gaps_2focused.csv,data/sieve/stage_002/values.csv
3,7,8,30,8,data/sieve/stage_003/gaps.csv,data/sieve/stage_003/gaps_2focused.csv,data/sieve/stage_003/values.csv
...
```

### gap_stats.csv

```
stage,head,period,modulus,gapCount,copyCount,mergeCount,newGapValues,lostGapValues,maxAge,avgAge,twoGapCount,twoGapSurvived
0,2,1,1,1,0,0,1,0,1,1.0,0,0
1,3,1,2,1,0,0,1,1,1,1.0,1,0
2,5,2,6,2,0,0,2,0,1,1.0,1,1
3,7,8,30,8,2,6,4,1,1,1.0,3,2
...
```

### stage_NNN_gaps.csv

```
index,gap,origin,age,mergeCount,mergeAncestors,ancestorValues
0,6,merge,1,2,"0;1","2;4"
1,4,copy,2,0,"",""
2,2,copy,3,0,"",""
3,4,merge,1,2,"2;3","2;4"
...
```

### stage_NNN_gaps_2focused.csv

```
index,gap,originalSpan
0,10,2
1,2,1
2,4,1
3,2,1
4,10,2
5,2,1
```

Where `originalSpan` = number of original gaps merged to produce this compressed gap (1 = already a 2 or isolated non-2, 2+ = merged block).

### stage_NNN_values.csv

```
index,value
0,7
1,11
2,13
3,17
...
```

## File Plan

| # | File | Action | Purpose |
|---|------|--------|---------|
| 1 | `build.sbt` | Edit | Add `lazy val spark` sub-project with Spark + ScalaTest dependencies |
| 2 | `justfile` | Edit | Add `spark-run` and `spark-test` recipes |
| 3 | `spark/src/main/scala/v1/chapter8/SparkSieveStage.scala` | Create | Self-contained stage model + next-stage pipeline |
| 4 | `spark/src/main/scala/v1/chapter8/GapLineage.scala` | Create | Gap lineage tracking: copy/merge detection, age, ancestry |
| 5 | `spark/src/main/scala/v1/chapter8/SparkSieveRunner.scala` | Create | Spark app entry point, CLI arg parsing, iterative generation |
| 6 | `spark/src/main/scala/v1/chapter8/SieveDataWriter.scala` | Create | CSV writer for gaps (with lineage), values, summary, and stats |
| 7 | `spark/src/test/scala/v1/chapter8/SparkSieveStageSpec.scala` | Create | Unit tests for core algorithm (base stages, nextStage, values) |
| 8 | `spark/src/test/scala/v1/chapter8/GapLineageSpec.scala` | Create | Unit tests for copy/merge detection, age tracking, ancestry |

### File 1: `build.sbt` — add spark sub-project

```scala
lazy val spark = (project in file("spark"))
  .settings(
    scalaVersion := "3.5.0",
    libraryDependencies ++= Seq(
      "org.apache.spark" %% "spark-core" % "3.5.1",
      "org.apache.spark" %% "spark-sql" % "3.5.1",
      "org.scalatest" %% "scalatest" % "3.3.0-SNAP4" % Test
    ),
    assembly / mainClass := Some("v1.chapter8.SparkSieveRunner")
  )
```

No `.dependsOn(root)` — full isolation.

### File 2: `justfile` — add spark recipes

```just
spark-run numStages="10":
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    sbt "spark/runMain v1.chapter8.SparkSieveRunner {{numStages}}"

spark-test:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    sbt "spark/test"
```

### File 3: `SparkSieveStage.scala`

```scala
package v1.chapter8

case class SparkSieveStage(
  head: Long,
  tailPrimes: Array[Long],
  modulus: Long,
  period: Int,
  gaps: Array[Long]
)
```

Methods:
- `firstNValues(n: Int): Array[Long]` — replay gap cycle from head
- `nextStage(): (SparkSieveStage, Array[GapLineage])` — expand → filter → gaps → rotate pipeline, also returning gap lineage metadata for the new gaps
- `isCoprime(v: Long, primes: Array[Long]): Boolean` — check v % p != 0 for all p

Companion object:
- `SparkSieveStage.base: SparkSieveStage` — stage 0
- `SparkSieveStage.nextFromCurrent(current: SparkSieveStage): (SparkSieveStage, Array[GapLineage])`

### File 4: `GapLineage.scala`

```scala
package v1.chapter8

case class GapLineage(
  index: Int,
  gap: Long,
  origin: String,        // "copy", "merge", or "new"
  age: Int,              // consecutive stages this gap has persisted
  mergeCount: Int,       // 0 for copies, 2+ for merges
  mergeAncestors: Array[Int],  // indices of merged gaps from previous stage
  ancestorValues: Array[Long]  // values of merged gaps from previous stage
)
```

Companion object:
- `GapLineage.trackNewGaps(newGaps: Array[Long], previousGaps: Array[Long], removedIndices: Set[Int]): Array[GapLineage]`
  - Given the new gap values, the previous stage's gaps, and which expanded indices were filtered out, determine for each new gap whether it was a copy or merge and compute its lineage.
- `GapLineage.computeStats(gaps: Array[GapLineage], prevTwoGapCount: Int): GapStageStats`
  - Aggregate statistics: copyCount, mergeCount, newGapValues, lostGapValues, maxAge, avgAge, twoGapCount, twoGapSurvived.

```scala
case class GapStageStats(
  copyCount: Int,
  mergeCount: Int,
  newGapValues: Int,
  lostGapValues: Int,
  maxAge: Int,
  avgAge: Double,
  twoGapCount: Int,
  twoGapSurvived: Int
)
```

### File 7: `SparkSieveStageSpec.scala`

Unit tests (ScalaTest):
- `S_0` base stage: head=2, gaps=[1], modulus=1
- `S_1` first stage: head=3, gaps=[2], modulus=2
- `S_2` second stage: head=5, gaps=[2,4], modulus=6
- `S_3` third stage: head=7, gaps=[6,4,2,4,2,4,6,2], modulus=30, period=8
- `firstNValues` returns correct first 10 values for each stage
- `nextStage` produces correct head, modulus, period for stages 0→4
- Long overflow detection at stage 18+

### File 8: `GapLineageSpec.scala`

Unit tests (ScalaTest):
- `S_0` → `S_1`: single gap [1] filtered by head=2, produces gap [2] with origin="new"
- `S_1` → `S_2`: gap [2] expanded by head=3, filtered, produces gaps [2,4]
  - Gap 2: copy of previous gap 2 (both endpoints survived)
  - Gap 4: merge of two gaps (interior point removed)
- Age tracking: a copied gap increments age, a merged gap resets to 1
- `computeStats`: correct copyCount, mergeCount, twoGapCount for known stages
- Lost gap detection: gap value 1 disappears after stage 0

### File 4: `SparkSieveRunner.scala`

Entry point with:
- CLI args: `[numStages]` (default 10), `[outputDir]` (default "data/sieve")
- SparkSession initialization (local[*] master)
- Iterative stage generation loop
- CSV output via SieveDataWriter
- Summary CSV with stage metadata and file paths

### File 5: `SieveDataWriter.scala`

CSV writer using Spark DataFrames:
- `writeGaps(spark, gaps, path)` — single CSV with index,gap columns
- `writeValues(spark, values, path)` — single CSV with index,value columns
- `writeSummary(spark, rows, path)` — single CSV with stage metadata

Uses `coalesce(1)` for single-file output.

## Algorithm Correctness Mapping

| Chapter 6 (verified) | Chapter 8 (Spark) |
|---|---|
| `SieveUtils.residues(M, P̄)` | `(0L until M).filter(r => isCoprime(r, P̄))` |
| `SieveUtils.expandResidues(R, M, h)` | `R.flatMap(r => (0L until h).map(_ * M + r))` |
| `SieveUtils.filterList(E, h)` | `E.filter(v => v % h != 0)` |
| `SieveUtils.calculateGaps(S, M')` | `S.zip(S.tail).map(_ - _) :+ (M' - S.last + S.head)` |
| `nextHeadResidueIndex` | Find position of min value, rotate gaps |

The mathematical structure is identical — only the implementation substrate changes (Stainless `List[BigInt]` → Scala `Array[Long]` + Spark).

## Long Overflow Boundary

`Long.MaxValue` = 9,223,372,036,854,775,807. The primorial grows as:
- Stage 0: M=1
- Stage 5: M=2,310
- Stage 10: M=6,469,693,230
- Stage 15: M=1,308,276,133,167,003,0
- Stage 17: M=510,909,421,717,094,400,000+ (exceeds Long)

The code will detect modulus overflow (negative value) and stop with a warning. Default stage count should stay ≤17 for Long safety.

## Assumptions

1. Spark 3.5.1 is compatible with Scala 3.5.0 (need to verify — Spark 3.5.x officially supports Scala 2.12/2.13, not Scala 3.x)
2. The user's machine has enough memory for local Spark execution
3. `data/sieve/` directory will be created by the writer

**Critical assumption #1:** If Spark 3.5.x doesn't support Scala 3.5.0, we may need to:
- Use Spark 4.0 (which adds Scala 3 support) — currently in preview
- Or cross-compile the Spark sub-project to Scala 2.13
- Or skip Spark entirely and use plain Scala with direct file I/O

## Risks

1. **Spark + Scala 3 compatibility** — Spark officially supports Scala 2.12/2.13 as of 3.5.x. Scala 3 support may require Spark 4.0 preview. This needs validation before implementation.
2. **Long overflow at stage 18+** — Documented limit. The code detects and stops.
3. **CSV sharding** — `coalesce(1)` handles this but could be slow for very large gap arrays. Alternative: direct `java.io.PrintWriter` for small files.
4. **Spark startup overhead** (~5-10s for local mode) — acceptable for the use case.
5. **Memory for large stages** — Stage 15 has ~5M gaps, stage 17 has ~350M gaps. Spark's managed memory handles this via disk spilling.

## Validation

1. `sbt spark/compile` — confirm compilation
2. `sbt spark/runMain v1.chapter8.SparkSieveRunner 5` — generate 5 stages
3. Inspect CSV output:
   - Stage 0: head=2, gaps=[1], values start [2,3,4,5,...]
   - Stage 1: head=3, gaps=[2], values start [3,5,7,9,...]
   - Stage 2: head=5, gaps=[2,4], values start [5,7,11,13,...]
   - Stage 3: head=7, gaps=[6,4,2,4,2,4,6,2], period=8
   - Stage 4: head=11, period=48
4. `just verify` — confirm Stainless verification unaffected
5. Cross-check stage 3 gaps against chapter6 `SieveSequenceNextLevel` output

## Fallback Options

1. **If Spark + Scala 3 fails:** Use plain Scala with `java.io.PrintWriter` for CSV output. No Spark dependency needed. Same algorithm, just without distributed computation.
2. **If sub-project causes build issues:** Use a separate `spark/build.sbt` (completely independent project, run via `cd spark && sbt run`).
3. **If Long overflows too early:** Use `java.math.BigInteger` for modulus/gaps. Array elements stay as `Long` for as long as possible; switch to `BigInteger` only when needed.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-17 | Ticket created. Goal: Spark sieve data generator. Complete isolation from Stainless required. Separate sbt sub-project chosen. | Awaiting user additions before implementation. |
| 2026-07-20 | Generated Spark output is too large for GitHub (`stage_010/gaps` is several GB), but the first-values output is sample-sized and currently hidden under ignored `spark/data/`. Need generated samples in a separate tracked `spark/samples/` tree. | Update generator to write small samples outside `spark/data/`; preserve existing generated data so stage 10 does not need to be regenerated. |
| 2026-07-20 | Generator now writes samples to `spark/samples/sieve-df/`: first-values gzip plus first 1000 rows for `gaps` and `gaps-2`. Existing local stages 0-10 were sampled without regenerating full data. Sample tree is about 228K. | `just spark-test` passed; `git diff --check` passed. |
