package v1

object DivMain {
  @main
  def main(): Unit = {
    val div =    Div(10, 3, 0, 10)
    val simplified = div.solve
    assert(simplified == v1.Div(10, 3, 3, 1))
  }
}
