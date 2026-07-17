package v1.chapter8

case class GapRow(index: Int, gap: Long, origin: String, age: Int, mergeCount: Int, mergeAncestors: String, ancestorValues: String) extends Serializable
case class Gap2FocusedRow(index: Int, gap: Long, originalSpan: Int) extends Serializable
case class ValueRow(index: Int, value: Long) extends Serializable
case class StageSummaryRow(stage: Int, head: Long, period: Int, modulus: Long, gapCount: Int, gapsFile: String, gaps2focusedFile: String, valuesFile: String) extends Serializable
case class GapStatsRow(stage: Int, head: Long, period: Int, modulus: Long, gapCount: Int, copyCount: Int, mergeCount: Int, newGapValues: Int, lostGapValues: Int, maxAge: Int, avgAge: Double, twoGapCount: Int, twoGapSurvived: Int) extends Serializable
