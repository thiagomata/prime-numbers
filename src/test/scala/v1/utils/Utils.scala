package v1.utils

class Utils{}

def createList(values: Array[BigInt]): stainless.collection.List[BigInt] = {
  require(values.length > 0)
  stainless.collection.List.fromScala(values.toList)
}

