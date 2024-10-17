package v1

object DivMain {
  @main
  def main(): Unit = {
    val div =    Div(10, 3, 0, 10)
    val solved = div.solve
    assert(solved == v1.Div(10, 3, 3, 1))
  }
}
