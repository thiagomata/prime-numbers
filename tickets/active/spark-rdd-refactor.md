# Spark RDD Refactor — Eliminate Driver Bottleneck

**Created:** 2026-07-17
**Status:** In progress

## Goal

Eliminate the `.collect()` that brings ALL gap data (T_new elements) to the driver. After this refactor, only O(h) metadata crosses to the driver. All gap data stays on executors and is written to files directly.

## Current Bottleneck

`SparkSievePipeline.scala:51` — `.collect()` brings h BlockResults (containing total T_new gaps + origins) to the driver. At stage 10, T_new ≈ 1B elements (~8GB).

## Strategy

### 1. Split BlockResult into two types

```scala
case class BlockMetadata(
  firstFiltered: Boolean,
  lastFiltered: Boolean,
  tailAccumGap: Long,
  tailAccumCount: Int,
  gapCount: Int          // how many gaps this block produced
) extends Serializable   // O(1) per block — collected to driver

case class BlockGaps(
  gaps: Array[Long],
  origins: Array[String]
) extends Serializable   // T/h per block — stays on executor, written to file
```

### 2. Worker writes gap files directly

Each block k writes its `BlockGaps` to `stage_NNN/block_KKK.csv.gz`. This happens on the executor during `.map()`.

### 3. Driver collects only BlockMetadata

`.collect()` returns `Array[BlockMetadata]` — O(h) data, tiny.

### 4. Driver patches boundary gaps

From BlockMetadata, the driver computes which block files need their first gap patched (carry from previous block). It reads the first line of affected files, computes the merged gap, and rewrites.

### 5. Rotation via offset metadata

The driver computes the rotation index R from the assembled gap counts. Each block knows its global offset. The rotation split point falls within one block — the driver tells that block to split its output.

### 6. Lineage computed on workers

Each block tracks origins during its walk. The origins array is part of BlockGaps (stays on executor). The final lineage CSV is written per-block, same as gaps.

## Files to Change

| File | Change |
|------|--------|
| `SparkSievePipeline.scala` | Split BlockResult, workers write files, driver collects only metadata |
| `SieveDataWriter.scala` | Add per-block file writing, boundary patching |
| `SparkSieveRunner.scala` | Use new pipeline API, pass output dir |
| `SparkSievePipelineSpec.scala` | Add unit tests per transformation |

## Validation

- 27/27 existing tests pass
- New Spark unit tests for: processBlock, assembly, rotation, boundary patching
- `just spark-run 5` produces correct output in `data/sieve-spark/`
