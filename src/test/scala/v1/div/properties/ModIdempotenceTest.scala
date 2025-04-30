package v1.div.properties

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers
import v1.div.DivMod

class ModIdempotenceTest extends FlatSpec with Matchers {

  final var pairs: List[(BigInt, BigInt)] = List(
    (BigInt(1),BigInt(2)),
    (BigInt(1),BigInt(-2)),
    (BigInt(-1),BigInt(-2)),
    (BigInt(-1),BigInt(2)),
    (BigInt(10),BigInt(2)),
    (BigInt(10),BigInt(-2)),
    (BigInt(-10),BigInt(-2)),
    (BigInt(-10),BigInt(2)),
    (BigInt(10),BigInt(3)),
    (BigInt(10),BigInt(-3)),
    (BigInt(-10),BigInt(-3)),
    (BigInt(-10),BigInt(3)),
  )

  "modIdempotence" should "hold for any values" in {
    assert(
      pairs.forall(
        pair => ModIdempotence.modIdempotence(pair._1, pair._2)
      )
    )
  }

  "modUniqueDiv" should "hold for any values" in {
    assert(
      pairs.forall(
        pair => {
          val a = DivMod(pair._1, pair._2, 0, pair._1)
          val b = DivMod(pair._1, pair._2, 1, pair._1 - pair._2)
          val c = DivMod(pair._1, pair._2, -1, pair._1 + pair._2)
          ModIdempotence.modUniqueDiv(a, b)
          ModIdempotence.modUniqueDiv(b, a)
          ModIdempotence.modUniqueDiv(b, c)
          ModIdempotence.modUniqueDiv(c, b)
          ModIdempotence.modUniqueDiv(a, c)
          ModIdempotence.modUniqueDiv(c, a)
        }
      )
    )
  }

  "modModPlus" should "hold for any values" in {
    assert(
      pairs.forall(
        pair => {
          ModIdempotence.modModPlus(pair._1, pair._2, 0) &&
            ModIdempotence.modModPlus(pair._1, pair._2, 1) &&
            ModIdempotence.modModPlus(pair._1, pair._2, 10) &&
            ModIdempotence.modModPlus(pair._1, pair._2, -1) &&
            ModIdempotence.modModPlus(pair._1, pair._2, -10)
        }
      )
    )
  }

  "modModMinus" should "hold for any values" in {
    assert(
      pairs.forall(
        pair => {
          ModIdempotence.modModMinus(pair._1, pair._2, 0) &&
            ModIdempotence.modModMinus(pair._1, pair._2, 1) &&
            ModIdempotence.modModMinus(pair._1, pair._2, 10) &&
            ModIdempotence.modModMinus(pair._1, pair._2, -1) &&
            ModIdempotence.modModMinus(pair._1, pair._2, -10)
        }
      )
    )
  }
}