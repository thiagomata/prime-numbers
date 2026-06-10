package v1.list.properties

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.list.ListBoundUtils

object ListProduct {

  /**
   * Computes the product of all elements in a list.
   *
   * The empty list has product 1, the multiplicative identity.
   *
   * @param list the input list
   * @return the product of all elements in the list
   */
  def product(list: List[BigInt]): BigInt = {
    decreases(list.size)

    if (list.isEmpty) BigInt(1)
    else list.head * product(list.tail)
  }

  /**
   * Product of a singleton list.
   *
   * product(List(x)) == x
   *
   * @param x the element of the singleton list
   * @return true if the property holds
   */
  def singletonProduct(x: BigInt): Boolean = {
    product(List(x)) == x
  }.holds

  /**
   * Lemma proving that a single element can be factored out of the
   * product of a concatenated list.
   *
   * product(listA ++ List(e) ++ listB) == e * product(listA ++ listB)
   *
   * @param listA prefix list
   * @param e     element to factor out
   * @param listB suffix list
   * @return true if the property holds
   */
  def productPullOutElement(
                             listA: List[BigInt],
                             e: BigInt,
                             listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      product(List(e) ++ listB) == e * product(listB)
    } else {
      productPullOutElement(listA.tail, e, listB)
      product(listA ++ List(e) ++ listB) ==
        e * product(listA ++ listB)
    }
  }.holds

  /**
   * Product distributes over list concatenation.
   *
   * product(listA ++ listB) == product(listA) * product(listB)
   *
   * @param listA first list
   * @param listB second list
   * @return true if the property holds
   */
  def productConcatLemma(
                          listA: List[BigInt],
                          listB: List[BigInt]
                        ): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      assert(product(listA) == BigInt(1))
      assert(product(listB) == product(listA) * product(listB))
      assert(listA ++ listB == listB)
    } else {
      productConcatLemma(listA.tail, listB)

      val concatenated = listA ++ listB

      assert(
        concatenated ==
          List(listA.head) ++ listA.tail ++ listB
      )

      assert(
        product(concatenated) ==
          listA.head * product(listA.tail ++ listB)
      )
    }

    product(listA ++ listB) ==
      product(listA) * product(listB)
  }.holds

  /**
   * Product is invariant under swapping concatenated blocks.
   *
   * product(listA ++ listB) == product(listB ++ listA)
   *
   * @param listA first list
   * @param listB second list
   * @return true if the property holds
   */
  def productConcatCommutative(
                                listA: List[BigInt],
                                listB: List[BigInt]
                              ): Boolean = {

    productConcatLemma(listA, listB)
    productConcatLemma(listB, listA)

    assert(
      product(listA ++ listB) ==
        product(listA) * product(listB)
    )

    assert(
      product(listB ++ listA) ==
        product(listB) * product(listA)
    )

    assert(
      product(listA) * product(listB) ==
        product(listB) * product(listA)
    )

    product(listA ++ listB) ==
      product(listB ++ listA)
  }.holds

  /**
   * If every element of the list is strictly positive,
   * then the product is strictly positive.
   *
   * @param elements a list of positive numbers
   * @return true if the property holds
   */
  def positiveProduct(elements: List[BigInt]): Boolean = {
    decreases(elements.size)

    require(ListBoundUtils.allGreaterThan(elements, 0))

    if (elements.isEmpty) {
      product(elements) > 0
    } else {
      positiveProduct(elements.tail)
      assert(product(elements.tail) > 0)
      product(elements) > 0
    }
  }.holds
}