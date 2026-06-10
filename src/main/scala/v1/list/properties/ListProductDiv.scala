package v1.list.properties

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.Calc
import v1.div.properties.AdditionAndMultiplication.ATimesBSameMod
import v1.div.properties.ModIdentity
import v1.list.ListBoundUtils

object ListProductDiv {

  /**
   * The head of a positive list divides the product of the list.
   *
   * Formally:
   *
   * product(head :: tail) mod head == 0
   *
   * @param elements a non-empty list of positive numbers
   * @return true if the property holds
   */
  def ListProductDiv(
                          elements: List[BigInt]
                        ): Boolean = {

    require(elements.nonEmpty)
    require(ListBoundUtils.allGreaterThan(elements, 0))

    val p = elements.head
    val tailProduct = ListProduct.product(elements.tail)

    assert(
      ListProduct.product(elements) ==
        p * tailProduct
    )

    assert(ModIdentity.modIdentity(p))

    assert(
      ATimesBSameMod(
        BigInt(0),
        p,
        tailProduct
      )
    )

    Calc.mod(
      ListProduct.product(elements),
      p
    ) == BigInt(0)
  }.holds

  /**
   * Every element of a positive list divides the product of the list.
   *
   * Formally:
   *
   * For every element x in elements:
   *
   * product(elements) mod x == 0
   *
   * @param elements a list of positive numbers
   * @return true if the property holds
   */
  def allElementsDivideProduct(
                                elements: List[BigInt]
                              ): Boolean = {

    require(ListBoundUtils.allGreaterThan(elements, 0))

    decreases(elements.size)

    if (elements.isEmpty) {
      true
    } else {

      val p = elements.head
      val tailProduct = ListProduct.product(elements.tail)

      assert(
        ListProduct.product(elements) ==
          p * tailProduct
      )

      assert(ModIdentity.modIdentity(p))

      assert(
        ATimesBSameMod(
          BigInt(0),
          p,
          tailProduct
        )
      )

      assert(
        Calc.mod(
          ListProduct.product(elements),
          p
        ) == BigInt(0)
      )

      allElementsDivideProduct(elements.tail)
    }
  }.holds

  /**
   * A stronger formulation of divisibility:
   * inserting an element into a list guarantees that the
   * resulting product is divisible by that element.
   *
   * product(prefix ++ List(e) ++ suffix) mod e == 0
   *
   * @param prefix prefix list
   * @param e positive factor
   * @param suffix suffix list
   * @return true if the property holds
   */
  def insertedElementDividesProduct(
                                     prefix: List[BigInt],
                                     e: BigInt,
                                     suffix: List[BigInt]
                                   ): Boolean = {

    require(e > 0)
    require(ListBoundUtils.allGreaterThan(prefix, 0))
    require(ListBoundUtils.allGreaterThan(suffix, 0))

    ListProduct.productPullOutElement(
      prefix,
      e,
      suffix
    )

    assert(
      ListProduct.product(
        prefix ++ List(e) ++ suffix
      ) ==
        e * ListProduct.product(
          prefix ++ suffix
        )
    )

    assert(ModIdentity.modIdentity(e))

    assert(
      ATimesBSameMod(
        BigInt(0),
        e,
        ListProduct.product(prefix ++ suffix)
      )
    )

    Calc.mod(
      ListProduct.product(
        prefix ++ List(e) ++ suffix
      ),
      e
    ) == BigInt(0)
  }.holds
}