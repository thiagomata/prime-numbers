package verification

object Helper {

  def check(condition: Boolean): Unit = {
    require(condition)
    assert(condition)
    stainless.proof.check(condition)
  }

  def equality[T](t1: T, t2: T): Boolean = {
    t1 == t2
  }

  def equality[T](t1: T, t2: T, t3: T): Boolean = {
    t1 == t2 && t2 == t3
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5 && t5 == t6
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5 && t5 == t6 && t6 == t7
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T, t8: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5 && t5 == t6 && t6 == t7 && t7 == t8
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T, t8: T, t9: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5 && t5 == t6 && t6 == t7 && t7 == t8 && t8 == t9
  }
}
