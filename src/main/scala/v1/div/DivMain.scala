package v1.div

import stainless.annotation.extern

object DivMain {

  @extern
  def println(message: String): Unit = {
    scala.Predef.println(message)
  }

  @extern
  def main(args: Array[String]): Unit = {
    val argLenght = args.length

    try {
      if (argLenght == 2) {
        with2Args(args)
        return
      }
      if (argLenght == 4) {
        with4Args(args)
        return
      }
      println("Usage: sbt 'runMain v1.DivMain <a> <b> [<div> <mod>]'")
    } catch {
      case e: NumberFormatException => {
        println("Invalid integer numbers " + args.toList.mkString(", "))
      }
      case e: IllegalArgumentException => {
        println("Invalid div mod numbers " + args.toList.mkString(", "))
      }
    }
  }

  @extern
  private def with2Args(args: Array[String]): Unit = {
    val a = BigInt(args(0))
    val b = BigInt(args(1))
    val divMod = DivMod(a, b, 0, a)
    val result = divMod.solve
    println(s"div: ${result.div.toString()}, mod: ${result.mod.toString()}")
  }

  @extern
  private def with4Args(args: Array[String]): Unit = {
    val a = BigInt(args(0))
    val b = BigInt(args(1))
    val div = BigInt(args(2))
    val mod = BigInt(args(3))
    val divMod = DivMod(a, b, div, mod)
    val result = divMod.solve
    println(s"div: ${result.div.toString()}, mod: ${result.mod.toString()}")
  }
}
