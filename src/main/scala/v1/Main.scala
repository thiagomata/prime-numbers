package v1

import stainless.annotation.extern
import v1.chapter2.div.DivMod

object Main {

  @extern
  def println(message: String): Unit = {
    scala.Predef.println(message)
  }

  @extern
  def main(args: Array[String]): Unit = {
    val argLenght = args.length

    try {
      if (argLenght == 1 && args(0) == "help") {
        println("Usage:")
        println("  just run <a> <b>           — compute div/mod of a and b")
        println("  just check <a> <b> <d> <m> — verify div/mod with explicit values")
        return
      }
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
