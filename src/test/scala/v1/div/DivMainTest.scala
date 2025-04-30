package v1.div

import org.scalatest.flatspec.FlatSpec

class DivMainTest extends FlatSpec {

  "println" should "say hi" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.println("hi")
    }
    assert(stream.toString() == "hi\n")
  }

  "main with 2 valid numbers: 13 / 2" should "should work" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("13","2"))
    }
    assert(stream.toString() == "div: 6, mod: 1\n")
  }

  "main with 4 valid numbers: 13 2 6 1" should "should work" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("13","2", "6", "1"))
    }
    assert(stream.toString() == "div: 6, mod: 1\n")
  }

  "main with 4 valid numbers: 13 2 0 13" should "should work" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("13", "2", "0", "13"))
    }
    assert(stream.toString() == "div: 6, mod: 1\n")
  }

  "main with 4 invalid numbers: 13 2 10 13" should "should return error" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("13", "2", "10", "13"))
    }
    assert(stream.toString() == "Invalid div mod numbers 13, 2, 10, 13\n")
  }

  "main with too few args" should "say error" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("hello"))
    }
    assert(stream.toString() == "Usage: sbt 'runMain v1.DivMain <a> <b> [<div> <mod>]'\n")
  }

  "main with too many args" should "say error" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("all","these","moments","will","be","lost","in","time"))
    }
    assert(stream.toString() == "Usage: sbt 'runMain v1.DivMain <a> <b> [<div> <mod>]'\n")
  }

  "invalid 1 of 2 numbers" should "should fail" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("hello","1"))
    }
    assert(stream.toString() == "Invalid integer numbers hello, 1\n")
  }

  "invalid 2 of 2 numbers" should "should fail" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("1","hello"))
    }
    assert(stream.toString() == "Invalid integer numbers 1, hello\n")
  }

  "invalid 1 of 4 numbers" should "should fail" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("hello","2","3","4"))
    }
    assert(stream.toString() == "Invalid integer numbers hello, 2, 3, 4\n")
  }

  "invalid 2 of 4 numbers" should "should fail" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("1","hello","3","4"))
    }
    assert(stream.toString() == "Invalid integer numbers 1, hello, 3, 4\n")
  }

  "invalid 3 of 4 numbers" should "should fail" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("1","2","hello","4"))
    }
    assert(stream.toString() == "Invalid integer numbers 1, 2, hello, 4\n")
  }

  "invalid 4 of 4 numbers" should "should fail" in {
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      DivMain.main(Array("1","2","3","hello"))
    }
    assert(stream.toString() == "Invalid integer numbers 1, 2, 3, hello\n")
  }
}
