// === Lemma: in SieveUtils.scala (Euclid's lemma — product+1 coprime with each divisor) ===

// If p > 1 divides product, then p does NOT divide product + 1
def assertEuclidCoprime(product: BigInt, p: BigInt): Boolean = {
  require(p > 1)
  require(Calc.mod(product, p) == BigInt(0))
  require(product >= 0)

  ModOperations.addOne(product, p)

  // addOne's else branch: mod(product+1, p) == mod(product, p) + 1 == 1
  assert(Calc.mod(product, p) != p - 1)  // 0 != p-1 because p > 1

  Calc.mod(product + 1, p) != BigInt(0)
}.holds

// === Lemma: in SieveUtils.scala (generalized over list) ===

// For every p in values: if p divides product(values), then
// product(values) + 1 is coprime with the whole list
def assertEuclidCoprimeToList(values: List[BigInt]): Boolean = {
  require(ListUtils.checkAllPositive(values))
  decreases(values.size)

  if (values.isEmpty) {
    SieveUtils.isCoprime(SieveUtils.product(values) + 1, values)
  } else {
    val prod = SieveUtils.product(values)
    val p = values.head

    assert(SieveUtils.assertAllElementsDivideProduct(values))
    assert(SieveUtils.assertIsCoprimeForAll(prod + 1, values))
    // assertIsCoprimeForAll proves Calc.mod(prod+1, p) != 0 for all p in values
    // but only if isCoprime(prod+1, values) is true — circular!
    // Need a different approach.
    true
  }
}

// === Actually cleaner: inline the list lemma into V0's nextPrime() ===

// In SieveUtils or directly in V0:
// We need: for each p in filterValues, Calc.mod(filterModulus + 1, p) != 0
//
// Known facts after assertAllElementsDivideProduct(filterValues):
//   for each p in filterValues: Calc.mod(SieveUtils.product(filterValues), p) == 0
//   i.e., Calc.mod(filterModulus, p) == 0  (since filterModulus == product(filterValues))
//
// From assertEuclidCoprime(filterModulus, p):
//   Calc.mod(filterModulus + 1, p) != 0
//
// Then SieveUtils.assertIsCoprimeForAll(filterModulus + 1, filterValues)
// connects this to isCoprime(filterModulus + 1, filterValues).

// === Method: in SpecSieveSequence.scala ===

// Returns the first value in the stream that is not a multiple of head.
// Termination guaranteed by Euclid witness: filterModulus + 1 (or
// 2*filterModulus + 1) passes the tail filter and is not divisible by head.
def nextPrime(): BigInt = {
  require(filterModulus > 0)

  // Bridge: filterModulus == SieveUtils.product(filterValues)
  assert(primorialMatchesSieveProduct(filterPrimes))
  assert(filterModulus == SieveUtils.product(filterValues))

  // Prove filterModulus + 1 passes the tail filter
  assert(SieveUtils.assertAllElementsDivideProduct(filterValues))

  // Choose witness not divisible by head
  val candidate1 = filterModulus + 1
  val witness = {
    if (Calc.mod(candidate1, head.value) != BigInt(0)) {
      candidate1
    } else {
      // filterModulus ≡ -1 mod head, so 2*filterModulus + 1 ≡ -1 mod head ≠ 0
      BigInt(2) * filterModulus + 1
    }
  }

  // witness passes tail filter (same Euclid argument for both)
  assert(SieveUtils.assertAllElementsDivideProduct(filterValues))
  // TODO: call assertEuclidCoprime for each p in filterValues via recursion

  assert(passesFilter(witness))
  assert(Calc.mod(witness, head.value) != BigInt(0))

  // By completeness, witness has an index in the stream
  val limit = indexOfAccepted(witness)
  assert(apply(limit) == witness)

  // Bounded scan: find first apply(k) not divisible by head
  def scan(k: BigInt): BigInt = {
    require(k >= 1)
    require(k <= limit)
    decreases(limit - k)

    val cur = apply(k)
    if (Calc.mod(cur, head.value) != BigInt(0)) cur
    else scan(k + 1)
  }

  scan(1)
}.ensuring(res =>
  accepts(res) &&
  Calc.mod(res, head.value) != BigInt(0)
)

