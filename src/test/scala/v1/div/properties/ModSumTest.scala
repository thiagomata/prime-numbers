package v1.div.properties

import org.scalatest.flatspec.FlatSpec
import org.scalatest.funsuite.AnyFunSuiteLike
import org.scalatest.matchers.should.Matchers

class ModSumTest extends FlatSpec with Matchers {

  val pairs: List[(BigInt, BigInt)] = List.apply(
    (BigInt(5),BigInt(2)),
    (BigInt(4),BigInt(2)),
  )

  "sumSymmetricalMods" should "hold" in {
    assert(pairs.forall(
      pair => {
        ModSum.sumSymmetricalMods(pair._1, pair._2)
      })
    )
  }

  "sumAllMods" should "hold" in {
    assert(pairs.forall(
      pair => {
        ModSum.sumAllModsEqualSumOfAllSmallValues(pair._1)
      })
    )
  }
}
