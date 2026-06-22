package v1.chapter6.seq.sieve.empirical

import stainless.annotation.extern

@extern
case class OutputRow(
  k: Int,
  p: BigInt,
  pNext: BigInt,
  gLocal: BigInt,
  delta: BigInt,
  extinction: Boolean
)
