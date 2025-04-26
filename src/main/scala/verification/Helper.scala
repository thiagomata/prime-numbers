package verification

implicit class EqualityChecker[A](val a: A) extends AnyVal {
  def === (b: A): Boolean = {
    require(Helper.equals(a, b))
    Helper.equality(a, b)
  }
}

object Helper {

//  def fact(condition: Boolean): Boolean = {
//    assert(condition)
//    condition
//  }

  def equals[T](t1: T, t2: T): Boolean = {
    t1 == t2
  }

  def equality[T](t1: T, t2: T): Boolean = {
    require(equals(t1,t2))
    assert(equals(t1,t2))
    equals(t1,t2)
  }

  def equals[T](t1: T, t2: T, t3: T): Boolean = {
    t1 == t2 && t2 == t3
  }

  def equality[T](t1: T, t2: T, t3: T): Boolean = {
    require(equals(t1,t2,t3))
    assert(equals(t1,t2,t3))
    equals(t1,t2,t3)
  }

  def equals[T](t1: T, t2: T, t3: T, t4: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T): Boolean = {
    require(equals(t1,t2,t3,t4))
    assert(equals(t1,t2,t3,t4))
    equals(t1,t2,t3,t4)
  }

  def equals[T](t1: T, t2: T, t3: T, t4: T, t5: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T): Boolean = {
    require(equals(t1,t2,t3,t4,t5))
    assert(equals(t1,t2,t3,t4,t5))
    equals(t1,t2,t3,t4,t5)
  }

  def equals[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5 && t5 == t6
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T): Boolean = {
    require(equals(t1,t2,t3,t4,t5,t6))
    assert(equals(t1,t2,t3,t4,t5,t6))
    equals(t1,t2,t3,t4,t5,t6)
  }

  def equals[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5 && t5 == t6 && t6 == t7
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T): Boolean = {
    require(equals(t1,t2,t3,t4,t5,t6,t7))
    assert(equals(t1,t2,t3,t4,t5,t6,t7))
    equals(t1,t2,t3,t4,t5,t6,t7)
  }

  def equals[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T, t8: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5 && t5 == t6 && t6 == t7 && t7 == t8
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T, t8: T): Boolean = {
    require(equals(t1,t2,t3,t4,t5,t6,t7,t8))
    assert(equals(t1,t2,t3,t4,t5,t6,t7,t8))
    equals(t1,t2,t3,t4,t5,t6,t7,t8)
  }

  def equals[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T, t8: T, t9: T): Boolean = {
    t1 == t2 && t2 == t3 && t3 == t4 && t4 == t5 && t5 == t6 && t6 == t7 && t7 == t8 && t8 == t9
  }

  def equality[T](t1: T, t2: T, t3: T, t4: T, t5: T, t6: T, t7: T, t8: T, t9: T): Boolean = {
    require(equals(t1,t2,t3,t4,t5,t6,t7,t8,t9))
    assert(equals(t1,t2,t3,t4,t5,t6,t7,t8,t9))
    equals(t1,t2,t3,t4,t5,t6,t7,t8,t9)
  }
}
