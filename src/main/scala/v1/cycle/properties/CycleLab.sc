import v1.cycle.Cycle
import v1.cycle.properties.CycleCheckMod

def createList(values: Array[BigInt]): stainless.collection.List[BigInt] = {
  require(values.length > 0)
  stainless.collection.List.fromScala(values.toList)
}

// 7720
//Cycle(
//    (BigInt("0")),
//    (BigInt("0"),
//    (BigInt("98"),
//    (BigInt("99")
//)
val cycle = Cycle(
  values = createList(Array(BigInt(0))),
//  modIsZeroForAllValues = createList(Array(BigInt(0))),
//  modIsNotZeroForAllValues = createList(Array(BigInt(98))),
//  modIsZeroForSomeValues = createList(Array(BigInt(99))),
)


//  modIsZer
//  Nil[BigInt](),
//  Cons[BigInt](
//    BigInt("14"), Cons[BigInt](BigInt("279"), Cons[BigInt](BigInt("294"), Cons[BigInt](BigInt("303"), Cons[BigInt](BigInt("323"), Cons[BigInt](BigInt("333"), Nil[BigInt]())
//    ))))), Cons[BigInt](BigInt("8"), Nil[BigInt]()))
//  [  Info  ]  Verified: 101 / 1269^C

//SeqProperties.sumAllLoopValuesFromCalc(seq)
//SeqProperties.sumAllLoopValuesFromList(seq)