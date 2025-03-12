package v1.div.properties

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers

class ModSmallDividendTest extends FlatSpec with Matchers {

  val pairs: List[(BigInt, BigInt)] = List.apply(
    (BigInt(1),BigInt(2)),
    (BigInt(5),BigInt(10)),
    (BigInt(5),BigInt(13)),
  )

  "modAdd" should "hold for any non b zero pair" in {
    assert(pairs.forall(
      pair => {
        ModSmallDividend.modSmallDividend(pair._1, pair._2)
      })
    )
  }
}
