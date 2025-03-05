package v1

import stainless.annotation.extern
import stainless.io.StdOut
import v1.div.DivMod

object DivMain {

  @extern
  def println(message: String): Unit = {
    scala.Predef.println(message)
  }

  @extern
  def main(args: Array[String]): Unit = {
    val argLenght = args.length
    if (argLenght == 2) {
      return with2Args(args)
    }
    if (argLenght == 4) {
      return with4Args(args)
    }
    println("Usage: sbt 'runMain v1.DivMain <a> <b> [<div> <mod>]'")
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
