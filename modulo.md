# Proving Properties of Division and Modulo using Formal Verification

## Abstract

The division and modulo operations are fundamental elements in the study of programming and mathematics.
Prime numbers, modular arithmetic, and cryptography are some of the areas where these operations are used.
In this article, we show how to prove some properties of these operations using the recursive definition of the division and modulo operations, such as the unique remainder, modulo idempotence, and distributivity over addition and subtraction. 
We used Scala Stainless to verify these properties. 
Since these proofs are available in the source code, we can use them as a base to prove other properties related to the division and modulo operations.

## Introduction

Formal verification is a technique used to prove that a program or a system satisfies a specification.
> In the context of hardware and software systems, formal verification is the act of proving or disproving 
> the correctness of a system with respect to a certain formal specification or property, 
> using formal methods of mathematics. 
> [[1]](#ref1)
> [[2]](#ref2)
> The verification of these systems is done by ensuring the existence of a formal proof of a mathematical model of the system.

In this article, we will show how to prove some properties of the division and modulo operations using formal verification.
To do that, we will use [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html).

> The Stainless program verifier collects a list of top-level functions, and verifies the validity of their contracts. 
> Essentially, for each function, it will (try to) prove that the postcondition always holds, assuming a given precondition does hold.
> It attempts to prove it using a combination of an internal algorithm and external automated theorem proving.
> Stainless will also verify for each call site that the precondition of the invoked function cannot be violated.
> Stainless supports verification of a significant part of the Scala language, described in Pure Scala and Imperative.
> [[3]](#ref3)


## Limitations

The implementation presented in this article is limited to the division and modulo operations for integers. 
It goals is to make available a set of proofs that can be verified and used as a base to prove other properties related to the division and modulo operations.
Therefore, the implementation is optimized to correctness and not to performance.

The use of BigInt in the implementation focused on unbounded integers, without the need to worry about overflow or underflow issues. But, they are still constrained by the memory available in the system. 
Similarly, some proofs are using the recursive definition of the division and modulo operations, which could trigger a stack overflow for large numbers. Those issues do not invalidate the mathematical properties proved in this article, which are the main focus of this article.

## Traditional Definition

Given integers $dividend$ and $divisor$ where $divisor \neq 0$, the division algorithm determines integers $quotient$ and $remainder$ such that:

```math
\begin{aligned}
\forall \text{ } dividend, divisor & \in \mathbb{N} : divisor\neq 0  \\
& \exists ! \\
\text{quotient} & = \left\lfloor \frac{\text{dividend}}{\text{divisor}} \right\rfloor \implies   \\
dividend & = divisor \cdot quotient + \text{remainder} \\
dividend \text{ mod } divisor & = remainder \\
dividend \text{ div } divisor & = quotient \\
\text { where } 0 & \leq \text{remainder} < |b|
\end{aligned}
```

## Recursive Definition

Some properties of the division and modulo can be proved using the recursive definition of the division and modulo operations.
The recursive definition of the division and modulo operations are:


We define $DivMod(a, b, div, mod)$ such that:

```math
\begin{aligned}
\forall \text{ } a, b, div, mod \in \mathbb{Z} : b \neq 0, a = \text{div} \cdot b + \text{mod}
\end{aligned}
```

The solved $DivMod$ are those where the remainder $mod$ satisfies:

```math
\begin{cases}
0 \leq \text{mod} < b & \text{if } b > 0, \\
0 \leq \text{mod} < -b & \text{if } b < 0.
\end{cases}
```

### Recursive Formula

```math
\begin{aligned}
\text{DivMod.solve}(a, b, \text{div}, \text{mod}) =
\begin{cases}
\text{DivMod}(a, b, \text{div}, \text{mod}) & \text{if } 0 \leq \text{mod} < |b|, \\
\text{DivMod.solve}(a, b, \text{div} + \text{sign}(b), \text{mod} - |b|) & \text{if } \text{mod} \geq |b|, \\
\text{DivMod.solve}(a, b, \text{div} - \text{sign}(b), \text{mod} + |b|) & \text{if } \text{mod} < 0. \\
\end{cases} \\
\end{aligned}
```

We can see the described [recursive definition on Scala](
./src/main/scala/v1/div/DivMod.scala
), as follows:

<details>
<summary>./src/main/scala/v1/div/DivMod.scala</summary>

```scala
package v1.div

import stainless.lang.*
import verification.Helper.assert

import scala.language.postfixOps

case class DivMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt) {
  require(div * b + mod == a)
  require(b != 0)

  def absB: BigInt = if (b > 0) b else -b
  def isValid: Boolean = div * b + mod == a
  def isFinal: Boolean = if (b > 0) mod < b && mod >= 0 else mod < -b && mod >= 0

  def solve: DivMod = {
    if (this.isFinal) return this

    val result = if (mod > 0) then reduceMod else increaseMod
    (assert(result.isFinal && result.isValid))
    (assert(result.a == a && result.b == b))
    result
  }.ensuring(res => res.isFinal && res.isValid && res.a == a && res.b == b)

  def reduceMod: DivMod = {
    require(mod >= 0)
    decreases(mod)

    if (isFinal) return this

    val next = if (b > 0) then ModLessB else ModPlusB

    val result = next.reduceMod
    (assert(result.isFinal && result.isValid))
    (assert(result.mod < mod))
    (assert(result.a == a && result.b == b))
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def increaseMod: DivMod = {
    require(mod < 0) //                                               since mod is negative, it is not final
    decreases(-mod) //                                                mod should increase every iteration

    val next = if (b < 0) then ModLessB else ModPlusB //              increase the mod by abs(b)
    val result = if (next.isFinal) then next else next.increaseMod // repeat until mod is final
    (assert(result.isFinal && result.isValid)) //                     result is final and valid
    (assert(result.a == a && result.b == b)) //                       result has the same a and b as the original DivMod
    (assert(result.mod >= 0)) //                                      result has a non-negative mod
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def ModPlusB: DivMod = {
    (assert(div * b + mod == a))
    (assert(div * b - b + mod + b == a))  //         adding +b and -b does not change the value
    (assert((div - 1) * b + (mod + b) == a)) //      isolating div - 1 and mod + b
    val next = DivMod(a, b, div - 1, mod + b) //     is valid because next.div * next.b + next.mod == next.a as proved above
    (assert(next.a == a && next.b == b)) //          next.a and next.b are the same as the original DivMod
    (assert(next.mod == mod + b)) //                 next.mod is the same as the original DivMod plus b
    (assert(next.div == div - 1)) //                 next.div is the same as the original DivMod minus 1
    (assert(next.isValid)) //                        next is valid
    next
  }

  def ModLessB: DivMod = {
    assert(div * b + mod == a)
    assert(div * b + b + mod - b == a) //          adding -b and +b does not change the value
    assert((div + 1) * b + (mod - b) == a) //      isolating div + 1 and mod - b
    val next = DivMod(a, b, div + 1, mod - b) //   is valid because next.div * next.b + next.mod == next.a as proved above
    assert(next.a == a && next.b == b) //          next.a and next.b are the same as the original DivMod
    assert(next.mod == mod - b) //                 next.mod is the same as the original DivMod minus b
    assert(next.div == div + 1) //                 next.div is the same as the original DivMod plus 1
    assert(next.isValid) //                        next is valid
    next
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case that: DivMod =>
        ( that.a == this.a &&
          that.b == this.b &&
          that.div == this.div &&
          that.mod == this.mod ) ||
          ( that.solve == this.solve ) // we also consider two DivMod equal if they are the same after solving
      case _ => false
    }
  }
}
```
</details>

### Creating the Division and Module Operations

As we can see in the class [Calc](
./src/main/scala/v1/Calc.scala
), we can define the division and module operations by extracting these properties from the solved $DivMod$ as follows:

<details>
<summary>./src/main/scala/v1/Calc.scala</summary>

```scala
object Calc {

  def div(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    assert(a == 0 * b + a)
    val result = DivMod(a, b, 0, a)
    val solved = result.solve
    solved.div
  }

  def mod(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    assert(a == 0 * b + a)
    val result = DivMod(a, b, 0, a)
    val solved = result.solve
    solved.mod
  }.ensuring(
    mod => {
      val smallMod = if ( b > 0 ) 0 <= mod && mod < b else true
      val validMod = mod == DivMod(a, b, 0, a).solve.mod
      smallMod && validMod
    }
  )
}
```

</details>

## Some Important Properties of Modulo and Division

### Trivial Case

If the dividend is smaller than the divisor, the result of the modulos operation should be the dividend value and the division result should be zero.

```math
\begin{aligned}
& \forall \text{ } a,b \in \mathbb{N} : b \neq 0 \\
& a < b \implies a \text{ mod } b & = a \\
& a < b \implies a \text{ div } b & = 0 \\
\end{aligned}
```

We can check that since $DivMod(a, b, 0, a)$ is the final solution for the division operation.
That verification is available in [ModSmallDividend](./src/main/scala/v1/div/properties/ModSmallDividend.scala) and described below:

<details>
<summary>
./src/main/scala/v1/div/properties/ModSmallDividend.scala
</summary>

```scala
object ModSmallDividend {
  def modSmallDividend(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)
    require(b > a)
    require(a >= 0)
    val x = DivMod(a, b, 0, a)
    assert(x.isFinal)
    assert(x == x.solve)
    assert(x.mod == a)
    assert(x.div == 0)
    assert(Calc.mod(a, b) == x.mod)
    assert(Calc.div(a, b) == 0)
    Calc.mod(a, b) == a &&
    Calc.div(a, b) == 0
  }.holds
}
```

</details>


### Identity

The modulo of every number by itself is zero and the division of every number by itself is one.

```math
\begin{aligned}
\forall \text{ } n \in \mathbb{N} : n & \neq 0 \\
n \text{ mod } n & = 0 \\
n \text{ div } n & = 1 \\
\end{aligned}
```


We can prove this property using the recursive definition of the division and module operations. 
As the following [long proof](
./src/main/scala/v1/div/properties/ModIdentity.scala#longProof
) code example:

#### ModIdentity - Long Proof
<details>
<summary> ./src/main/scala/v1/div/properties/ModIdentity.scala#longProof </summary>

```scala
  def longProof(n: BigInt): Boolean = {
    require(n != 0)
    assert(!DivMod(a = n, b = n, div = 0, mod = n).isFinal)

    if (n > 0) {
      equality(
        DivMod(a=n, b=n, div=0, mod=n).solve,               // is equals to
        DivMod(a=n, b=n, div=0, mod=n).reduceMod.solve,     // is equals to
        DivMod(a=n, b=n, div=0, mod=n).ModLessB.reduceMod,  // is equals to
        DivMod(a=n, b=n, div=1, mod=0).reduceMod,           // is equals to
        DivMod(a=n, b=n, div=1, mod=0)
      )
      // since
      assert(DivMod(a=n, b=n, div=1, mod=0).isFinal)
    } else {
      equality(
        DivMod(a=n, b=n, div=0, mod=n).solve,                 // is equals to
        DivMod(a=n, b=n, div=0, mod=n).increaseMod.solve,     // is equals to
        DivMod(a=n, b=n, div=0, mod=n).ModPlusB.increaseMod,  // is equals to
        DivMod(a=n, b=n, div=1, mod=0)
      )
      // since
      assert(DivMod(a=n, b=n, div=1, mod=0).isFinal)
    }
    DivMod(a=n, b=n, div=0, mod=n).solve == DivMod(a=n, b=n, div=1, mod=0)
  }.holds
```

</details>

#### ModIdentity - Short Proof

But we don't need to manually do all these transformations.
Scala Stainless can verify that property holds in 
[ModIdentity](
./src/main/scala/v1/div/properties/ModIdentity.scala
) with no issues as follows:

```scala
  def modIdentity(a: BigInt): Boolean = {
    require(a != 0)
    Calc.mod(a, a) == 0
  }.holds
```

Similary, in the next sections, we will prove other properties of the division and module operations using only the amount of evidences required to Scala Stainless to verify that they hold.

### Addition

```math
\begin{aligned}
\forall a,b,div,mod \in \mathbb{Z} & : a = \text{div} \cdot b + \text{mod}, b \neq 0 \\ 
DivMod(a,b, div + 1, mod - b).solve & = DivMod(a,b, div, mod).solve \\
DivMod(a,b, div - 1, mod + b).solve & = DivMod(a,b, div, mod).solve \\
& \therefore \\
a \text{ mod } b = (a + b) \text{ mod } b & = (a - b) \text{ mod } b \\
1 + (a \text{ div } b) & = (a + b) \text{ div } b \\
1 - (a \text{ div } b) & = (a - b) \text{ div } b \\
\end{aligned}
```

As proved in [MoreDivLessMod](
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#MoreDivLessMod
) and [LessDivMoreMod](
./src/main/scala/v1/div/properties/DivModAdditionAndMultiplication.scala#LessDivMoreMod
) and shown the code below, the division result is the same for the same dividend and divisor, regardless of the div and mod values, as long $a = b \cdot div + mod$.

#### AdditionAndMultiplication - MoreDivLessMod

<details>
<summary>
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#MoreDivLessMod
</summary>


```scala
  def MoreDivLessMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    val div1 = DivMod(a, b, div, mod)
    val div2 = DivMod(a, b, div + 1, mod - b)

    if (div1.isFinal) assert(!div2.isFinal && div2.solve == div1.solve)
    if (div2.isFinal) assert(!div1.isFinal && div1.solve == div2.solve)

    if (div1.mod < 0) {
      assert(div1.solve == div1.increaseMod)
      if (b > 0) {
        equality(
          div2.solve, //       is equals to
          div2.increaseMod, // is equals to
          div1.increaseMod, // is equals to
          div1.solve
        )
      } else {
        equality(
          div1.increaseMod, // is equals to
          div2.solve, //       is equals to
          div1.solve
        )
      }
      assert(div1.solve == div2.solve)
    }
    if (div1.mod > 0 && ! div1.isFinal && ! div2.isFinal) {
      if (b > 0 ) {
        assert(div2.mod < div1.mod)
        equality(
          div1.solve, //       is equals to
          div1.reduceMod, //   is equals to
          div2.solve
        )
      } else {
        assert(div2.mod > div1.mod)
        equality(
          div2.solve, //     is equals to
          div2.reduceMod, // is equals to
          div2.solve
        )
      }
    }
    assert(div1.solve == div2.solve)
    DivMod(a,b, div + 1, mod - b).solve.mod == DivMod(a,b, div, mod).solve.mod
  }.holds
```

</details>

#### AdditionAndMultiplication - LessDivMoreMod

<details>
<summary>
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#LessDivMoreMod
</summary>


```scala
  def LessDivMoreMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)

    equality(
      a,                         // is equals to
      div * b + mod,             // is equals to
      (div - 1) * b + (mod + b)
    )
    MoreDivLessMod(a, b, div - 1, mod + b)

    DivMod(a, b, div, mod).solve == DivMod(a, b, div - 1, mod + b).solve
  }.holds
```

</details>


### Adding or Removing Multiples of Divisor

As a directly consequence of these properties, we can extend the $DivMod$ with the following properties:

```math
\begin{aligned}
\forall \text{ } a, b, div, mod, m \in \mathbb{Z} & : b \neq 0, a = b \cdot div + mod \\
& \therefore \\
DivMod(a,b, div + m, mod - m * b).solve & = DivMod(a,b, div, mod).solve \\
DivMod(a,b, div - m, mod + m * b).solve & = DivMod(a,b, div, mod).solve \\
& \therefore \\
mod(a + m \cdot b, b) & = mod(a, b) \\
div(a + m \cdot b, b) & = div(a, b) + m \\
mod(a - m \cdot b, b) & = mod(a, b) \\
div(a - m \cdot b, b) & = div(a, b) - m \\
\end{aligned}
```

### Unique Remainder

There is only one single remainder value for every $a, b$ pair.

```math
\begin{aligned}
  \forall \text{ } a, b, r & \in \mathbb{Z} \\
  \quad \exists ! \, r \mid 0 \leq r < |b| & \implies \quad  a = \left\lfloor \frac{a}{b} \right\rfloor \cdot b + r
\end{aligned}
```


in other words, two $DivMod$ instances with the same dividend $a$ and divisor $b$ will have the same solution.

```math
\begin{aligned}
\forall a, b,divX, modX, divY, modY & \in \mathbb{N}, \\ 
\text{where } b & \neq 0 \text{, } \\
a & = b \cdot divX + modX \text{ and } \\
a & = b \cdot divX + modY \text{ then } \\
DivMod(a, b, divX, modX).solve & = DivMod(a, b, divY, modY).solve \\
\end{aligned}
```

For every $a, b$ pair, with any $divX, modX, divY, modY$, there is always the same and single solution for the division operation.
That is proved in the [unique remainder property](
./src/main/scala/v1/div/properties/ModIdempotence.scala#modUnique
) as shown below:

#### ModIdempotence - Mod Uniue

<details>
<summary>./src/main/scala/v1/div/properties/ModIdempotence.scala#modUnique</summary>


```scala
  def modUniqueDiv(x: DivMod, y: DivMod): Boolean = {
    require(x.isValid)
    require(y.isValid)
    require(x.a == y.a)
    require(x.b == y.b)
    require(x.b != 0)
    assert(modUnique(x.a, x.b, x.div, x.mod, y.div, y.mod))
    x.solve == y.solve
  }.holds

  def modUnique(a: BigInt, b: BigInt, divx: BigInt, modx: BigInt, divy: BigInt, mody: BigInt): Boolean = {
    require(b != 0)
    val divDiff = divx - divy
    val absDivDiff = if (divDiff < 0) -divDiff else divDiff
    decreases(absDivDiff)
    require(divx * b + modx == a)
    require(divy * b + mody == a)

    val x = DivMod(a, b, divx, modx)
    val y = DivMod(a, b, divy, mody)

    if (divx == divy) {
      assert(modx == mody)
      assert(x == y)
    }
    if (divx < divy) {
      AdditionAndMultiplication.MoreDivLessMod(a, b, divx, modx)
      val next =  DivMod(a, b, divx + 1, modx - b)
      assert(x.solve == next.solve)
      modUnique(a, b, divx + 1, modx - b, divy, mody)
      assert(x.solve == y.solve)
    }
    if (divx > divy) {
      AdditionAndMultiplication.LessDivMoreMod(a, b, divx, modx)
      val next =  DivMod(a, b, divx - 1, modx + b)
      assert(x.solve == next.solve)
      modUnique(a, b, divx - 1, modx + b, divy, mody)
      assert(x.solve == y.solve)
    }
    assert(x.solve == y.solve)

    DivMod(a, b, divx, modx).solve == DivMod(a, b, divy, mody).solve
  }.holds
```

</details>

### Modulo Idempotence

```math
\begin{aligned}
\forall \text{ } a,b & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b & = ( a \text{ mod } b ) \text{ mod } b \\
\end{aligned}
```

The proof of the modulo idempotence property is available in the [ModIdempotence](./src/main/scala/v1/div/properties/ModIdempotence.scala#modIdempotence) as follows:

#### ModIdempotence - Mod Idempotence

<details>
<summary>
./src/main/scala/v1/div/properties/ModIdempotence.scala#modIdempotence
</summary>

```scala
  def modIdempotence(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    val div = DivMod(a, b, 0, a)
    if (a >= 0) {
      assert(modIdempotencePositiveA(a, b))
      assert(mod(a, b) == mod(mod(a, b), b))
    } else {
      assert(modIdempotencePositiveA(-a, b))
      val divModNegative = DivMod(a, b, 0, a)
      val solvedNegative = divModNegative.solve
      assert(a == solvedNegative.div * b + solvedNegative.mod)
      assert(solvedNegative.mod >= 0)
      assert(solvedNegative.mod <= solvedNegative.absB)
      assert(mod(a, b) == mod(mod(a, b), b))
    }
    mod(a, b) == mod(mod(a, b), b)
  }

  def modIdempotencePositiveA(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(a >= 0)

    val divMod = DivMod(a, b, 0, a)

    val solved = divMod.solve
    assert(solved.isFinal)
    assert(solved.b == divMod.b)
    assert(solved.a == divMod.a)
    assert(divMod.absB > 0)
    assert(solved.mod < divMod.absB)
    assert(solved.mod >= 0)

    val result = solved.mod
    assert(result <= a)
    assert(result < divMod.absB)
    assert(result == mod(a, b))

    assert(mod(result, b) == result)
    assert(mod(a, b) == mod(result, b))
    mod(a, b) == mod(mod(a, b), b)
  }.holds
```

</details>

### Distributivity over Addition and Subtraction


The distributive properties are proved in the [ModOperations](
./src/main//scala/v1/div/properties/ModOperations.scala
), as shown as follows:

#### Modulo Rule for Addition

```math
\begin{aligned}
\forall \text{ } a,b,c & \in \mathbb{Z} : b \neq 0 \\
( a + c ) \text{ mod } b & = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b \\
( a + c ) \text{ div } b & = a \text{ div } b + c \text{ div } b + ( a \text{ mod } b + c \text{ mod } b ) \text{ div } b \\
\end{aligned}
```

Proved at [ModOperations#modAdd](
./src/main//scala/v1/div/properties/ModOperations.scala#modAdd
) as follows:

<details>
<summary>
./src/main/scala/v1/div/properties/ModOperations.scala#modAdd
 </summary>

```scala
  /**
   * mod(a + c, b) == mod(mod(a, b) + mod(c, b), b) &&
   * div(a + c, b) == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b)
   *
   * @param a BigInt First dividend
   * @param b BigInt Divisor
   * @param c BigInt Second dividend
   * @return Boolean if the properties hold
   */
  def modAdd(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val x = DivMod(a, b, 0, a)
    val solvedX = x.solve
    assert(solvedX.isFinal && solvedX.isValid)
    assert(solvedX.mod < x.absB)
    assert(solvedX.a == a)
    assert(solvedX.b == b)
    assert(solvedX.a == solvedX.b * solvedX.div + solvedX.mod)
    assert(solvedX.a - solvedX.b * solvedX.div == solvedX.mod)

    val y = DivMod(c, b, 0, c)
    val solvedY = y.solve
    assert(solvedY.isFinal && solvedY.isValid)
    assert(solvedY.mod < x.absB)
    assert(solvedY.a == c)
    assert(solvedY.b == b)
    assert(solvedY.a == solvedY.b * solvedY.div + solvedY.mod)
    assert(solvedY.a - solvedY.b * solvedY.div == solvedY.mod)

    val xy = DivMod(a + c, b, 0, a + c)
    val solvedXY = xy.solve
    assert(solvedXY.isFinal && solvedXY.isValid)
    assert(solvedXY.mod < x.absB)
    assert(solvedXY.a == a + c)
    assert(solvedXY.b == b)
    assert(solvedXY.a == solvedXY.b * solvedXY.div + solvedXY.mod)
    assert(a + c == b * solvedXY.div + solvedXY.mod)

    val z = DivMod(solvedX.mod + solvedY.mod, b, 0, solvedX.mod + solvedY.mod)
    assert(z.a == z.b * z.div + z.mod)
    assert(z.a == solvedX.mod + solvedY.mod)
    assert(z.b == b)
    assert(z.mod == solvedX.mod + solvedY.mod)
    assert(z.div == 0)
    assert(z.a == z.b * z.div + z.mod)

    val solvedZ = z.solve
    assert(solvedZ.isValid && solvedZ.isFinal)
    assert(solvedZ.mod < x.absB)
    assert(modUniqueDiv(z, solvedZ))
    assert(z.solve.mod == solvedZ.mod)

    assert(solvedX.mod + solvedY.mod == b * solvedZ.div + solvedZ.mod)
    assert(solvedX.a - solvedX.b * solvedX.div + solvedY.a - solvedY.b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    assert(a - b * solvedX.div + c - b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    assert(a + c == b * solvedZ.div + b * solvedX.div + b * solvedY.div + solvedZ.mod)

    val bigDiv = solvedZ.div + solvedX.div + solvedY.div
    assert(a + c == b * bigDiv + solvedZ.mod)

    val w = DivMod(a + c, b, bigDiv, solvedZ.mod)
    assert(solvedZ.mod < x.absB)
    assert(w.mod == solvedZ.mod)
    assert(w.isFinal)
    assert(w.solve == w)

    assert(b != 0)
    assert(AdditionAndMultiplication.ATimesBSameMod(a + c, b, bigDiv))
    assert(mod(a + c, b) == mod(a + c + b * bigDiv, b))
    assert(w.isValid)
    assert(xy.isValid)
    assert(w.a == xy.a)
    assert(w.b == xy.b)
    assert(modUniqueDiv(w, xy))
    assert(w.solve == xy.solve)

    equality(
      w.solve.mod,        // is equals to
      xy.solve.mod,       // is equals to
      mod(a + c, b),      // is equals to
      solvedZ.mod,        // is equals to
      mod(mod(a, b) + mod(c, b), b)
    )

    assert(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
    assert(div(a + c, b) == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b))

    mod(a + c, b) == mod(mod(a, b) + mod(c, b), b) &&
      div(a + c, b) == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b)
  }.holds

```

</details>

#### Modulo Rule for Subtraction

```math
\begin{aligned}
\forall \text{ } a,b,c & \in \mathbb{Z} : b \neq 0 \\
( a - c ) \text{ mod } b & = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b \\
( a - c ) \text{ div } b & = a \text{ div } b - c \text{ div } b + ( a \text{ mod } b - c \text{ mod } b ) \text{ div } b \\
\end{aligned}
```

Proved at [ModOperations#modLess](
./src/main//scala/v1/div/properties/ModOperations.scala#modLess
) as follows:

<details>
<summary>
./src/main/scala/v1/div/properties/ModOperations.scala#modLess
 </summary>

```scala
  /**
   * mod(a - c, b) == mod(mod(a, b) - mod(c, b), b) &&
   * div(a - c, b) == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b)
   *
   * @param a BigInt First dividend
   * @param b BigInt Divisor
   * @param c BigInt Second dividend
   * @return Boolean if the properties hold
   */
  def modLess(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val x = a - c
    assert(modAdd(x, b, c))

    assert(x == b * div(x, b) + mod(x, b))
    assert(a == b * div(a, b) + mod(a, b))
    assert(c == b * div(c, b) + mod(c, b))

    equality(
      x,                                                            // is equal to
      a - c,                                                        // is equal to
      (a) - (c),                                                    // is equal to
      (b * div(a, b) + mod(a, b)) - (b * div(c, b) + mod(c, b)),    // is equal to
      b * div(a, b) + mod(a, b) - b * div(c, b) - mod(c, b),        // is equal to
      b * div(a, b) - b * div(c, b) + mod(a, b) - mod(c, b),        // is equal to
      b * (div(a, b) - div(c, b)) + mod(a, b) - mod(c, b),          // is equal to
      b * div(x, b) + mod(x, b),                                    // is equal to
      b * div(a - c, b) + mod(a - c, b)
    )

    assert(a == b * div(a, b) + mod(a, b))
    assert(c == b * div(c, b) + mod(c, b))
    equality(
      a - c,                                                        // is equal to
      b * div(a, b) + mod(a, b) - (b * div(c, b) + mod(c, b)),      // is equal to
      b * div(a, b) + mod(a, b) - b * div(c, b) - mod(c, b),        // is equal to
      b * div(a, b) - b * div(c, b) + mod(a, b) - mod(c, b),        // is equal to
    )
    assert(mod(a - c, b) == mod(b * (div(a, b) - div(c, b)) + mod(a, b) - mod(c, b), b))
    val m = div(a, b) - div(c, b)
    val others = mod(a, b) - mod(c, b)
    assert(mod(a - c, b) == mod(b * m + others, b))
    AdditionAndMultiplication.ATimesBSameMod(others, b, m)
    assert(mod(b * m + others, b) == mod(others, b))
    assert(mod(a - c, b) == mod(mod(a, b) - mod(c, b), b))

    assert(div(x + c, b) == div(x, b) + div(c, b) + div(mod(x, b) + mod(c, b), b))
    assert(div(a - c + c, b) == div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b))
    assert(div(a, b) == div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b))
    assert(div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b) == div(a, b))
    assert(div(a - c, b) + div(mod(a - c, b) + mod(c, b), b) == div(a, b) - div(c, b))
    assert(div(a - c, b) == div(a, b) - div(c, b) - div(mod(a - c, b) + mod(c, b), b))
    assert(div(a - c, b) == div(a, b) - div(c, b) - div(mod(mod(a, b) - mod(c, b), b) + mod(c, b), b))

    val absB = if (b < 0) -b else b
    val sign = if (b < 0) BigInt(-1) else BigInt(1)

    assert(ModIdempotence.modModMinus(a, b, c))
    assert(
      mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) ||
      mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) + b ||
      mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) - b
    )
    assert(
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) - mod(c, b) + mod(c, b) ||
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) - mod(c, b) + b + mod(c, b) ||
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) - mod(c, b) - b + mod(c, b)
    )
    assert(
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) ||
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) + b ||
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) - b
    )

    mod(a - c, b) == mod(mod(a, b) - mod(c, b), b) &&
    div(a - c, b) == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b)
  }.holds
```

</details>


#### Modular Shift Invariance under Divisible Base


```math
\begin{aligned}
\forall \text{ } a,b,c & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b = 0 & \implies ( a + c ) \text{ mod } b = c \text{ mod } b \\
a \text{ mod } b = 0 & \implies ( a - c ) \text{ mod } b = c \text{ mod } b \\
\end{aligned}
```

Proved at [ModOperations#modZeroPlusC](
./src/main//scala/v1/div/properties/ModOperations.scala#modZeroPlusC
) as follows:

<details>
<summary>
./src/main/scala/v1/div/properties/ModOperations.scala#modZeroPlusC
 </summary>

```scala
  /**
   * if mod(a, b) == 0 and c >= 0 then
   * mod(a + c, b) == mod(c, b) &&
   * mod(a + c, b) == mod(mod(c, b), b)
   *
   * @param a BigInt First dividend
   * @param b BigInt Divisor
   * @param c BigInt Second dividend
   * @return Boolean if the properties hold
   */
  def modZeroPlusC(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)
    require(c >= 0)
    require(mod(a, b) == 0)

    modAdd(a, b, c)
    assert(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
    assert(mod(a + c, b) == mod(0 + mod(c, b), b))
    assert(mod(a + c, b) == mod(mod(c, b), b))

    assert(ModIdempotence.modIdempotence(c, b))
    assert(mod(mod(c, b), b) == mod(c, b))
    assert(mod(a + c, b) == mod(c, b))

    mod(a + c, b) == mod(c, b) &&
    mod(a + c, b) == mod(mod(c, b), b)
  }.holds
```

</details>

### Unit-Step Modulo-Division Increment Law

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{N} : b \neq 0 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ mod } b = 0 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ mod } b = (a \text{ mod } b) + 1 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ div } b = (a \text{ div } b) + 1 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ div } b = a \text{ div } b \\
\end{aligned}
```

Proved at [ModOperations#addOne](
./src/main//scala/v1/div/properties/ModOperations.scala#addOne
) as follows:

<details>
<summary>
./src/main/scala/v1/div/properties/ModOperations.scala#addOne
 </summary>

```scala
  /**
   * if b == 1             then mod(a + 1, b) == mod(a,b) and div(a + 1, b) == div(a, b) + 1
   * if mod(a, b) == b - 1 then mod(a + 1, b) == 0        and div(a + 1, b) == div(a, b) + 1
   * otherwise             then mod(a + 1, b) == mod(a, b) + 1 and div(a + 1, b) == div(a, b)
   *
   * alternatively
   *
   * if mod(a, b) == b - 1 then mod(a + 1, b) == 0        and div(a + 1, b) == div(a, b) + 1
   * else                       mod(a + 1, b) == mod(a, b) + 1 and div(a + 1, b) == div(a, b)
   *
   * @param a BigInt dividend
   * @param b BigInt divisor
   * @return Boolean if the properties hold
   */
  def addOne(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)
    require(a >= 0)

    if (b == 1) {
      assert(mod(a, b) == 0)
      assert(mod(a + 1, b) == 0)
      assert(mod(a + 1, b) == mod(a,b))
      assert(div(a + 1, b) == div(a, b) + 1)
      return
        mod(a + 1, b) == mod(a,b) &&
        div(a + 1, b) == div(a, b) + 1
    }

    if (mod(a, b) == b - 1) {
      assert(mod(a + 1, b) == 0)
      assert(div(a + 1, b) == div(a, b) + 1)
      return
        mod(a + 1, b) == 0 &&
        div(a + 1, b) == div(a, b) + 1
    }

    assert(mod(a + 1, b) == mod(a, b) + 1)
    assert(div(a + 1, b) == div(a, b))
    mod(a + 1, b) == mod(a, b) + 1 &&
    div(a + 1, b) == div(a, b)
  }.holds
 ````
</details>

## Conclusion

The division and module operations are fundamental in computer science and mathematics.
In this article, we have shown how to prove some properties of these operations
using the recursive definition of the division and modulo operations and formal verification on Scala Stainless,
with available proofs in the source code.

These properties are:

```math
\begin{aligned}
\forall \text{ } a, b, c, m & \in \mathbb{Z} : b \neq 0 \\
b > a \geq 0 \implies a \text{ div } b & = 0 \\
b > a \geq 0 \implies a \text{ mod } b & = a \\
b \text{ mod } b                   & = 0 \\
b \text{ div } b                   & = 1 \\
( a + b \cdot m ) \text{ mod } b   & = a \text{ mod } b \\
( a - b \cdot m ) \text{ mod } b   & = a \text{ mod } b \\
(a \text{ mod } b) \text{ mod } b  & = a \text{ mod } b \\
(a + b) \text{ div } b             & = (a \text{ div } b) + 1 \\
(a - b) \text{ div } b             & = (a \text{ div } b) - 1 \\
(a + b \cdot m ) \text{ div } b    & = (a \text{ div } b) + m \\
(a - b \cdot m ) \text{ div } b    & = (a \text{ div } b) - m \\
(a + c) \text{ div } b             & = (a \text{ div } b) + (c \text{ div } b) + (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } b) \\
(a - c) \text{ div } b             & = (a \text{ div } b) - (c \text{ div } b) + (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } b) \\
(a + c) \text{ mod } b             & = ((a \text{ mod } b) + (c \text{ mod } b)) \text{ mod } b \\
(a - c) \text{ mod } b             & = ((a \text{ mod } b) - (c \text{ mod } b)) \text{ mod } b \\
(a + c) \text{ mod } b             & = (a \text{ mod } b) + (c \text{ mod } b) - b \cdot (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } c) \\
(a - c) \text{ mod } b             & = (a \text{ mod } b) - (c \text{ mod } b) - b \cdot (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } c) \\
\end{aligned}
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{N} : b \neq 0 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ mod } b = 0 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ mod } b = (a \text{ mod } b) + 1 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ div } b = (a \text{ div } b) + 1 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ div } b = a \text{ div } b \\
\end{aligned}
````
Those properties could be verified by the Scala Stainless as we can see in the code bellow from the [Summary.scala](
 ./src/main/scala/v1/div/properties/Summary.scala
) file.   

#### Summary

<details>
<summary>
./src/main/scala/v1/div/properties/Summary.scala
</summary>

```scala
package v1.div.properties

import stainless.lang.*
import verification.Helper.assert
import v1.Calc
import v1.Calc.{div, mod}

object Summary {
 def PropertySummary(a: BigInt, b: BigInt, c: BigInt, m: BigInt): Boolean = {
  require(b != 0)
  require(m >= 0)

  if (a >= 0 && b > a) {
   assert(ModSmallDividend.modSmallDividend(a, b))
  }

  assert(ModIdempotence.modIdempotence(a, b))
  assert(ModIdentity.modIdentity(b))
  assert(AdditionAndMultiplication.APlusBSameModPlusDiv(a, b))
  assert(AdditionAndMultiplication.ALessBSameModDecreaseDiv(a, b))
  assert(AdditionAndMultiplication.ATimesBSameMod(a, b, m))

  assert(AdditionAndMultiplication.ALessMultipleTimesBSameMod(a, b, m))
  assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(a, b, m))

  assert(ModOperations.modAdd(a, b, c))
  assert(ModOperations.modLess(a, b, c))

  assert(ModIdempotence.modModPlus(a, b, c))
  assert(ModIdempotence.modModMinus(a, b, c))

  assert(if  a >= 0 && b > 0 then ModOperations.addOne(a, b) else true)

  assert(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
  assert(mod(a - c, b) == mod(mod(a, b) - mod(c, b), b))
  assert(if a >= 0 && b > a then div(a,b) == 0 else true)
  assert(if a >= 0 && b > a then mod(a,b) == a else true)
  assert(if b > 0 then mod(mod(a, b), b) == mod(a, b) else true)
  assert(mod(b, b)         == 0)
  assert(div(b, b)         == 1)
  assert(mod(a + b * m, b) == mod(a, b))
  assert(mod(a - b * m, b) == mod(a, b))
  assert(div(a + b, b)     == div(a, b) + 1)
  assert(div(a - b, b)     == div(a, b) - 1)
  assert(div(a + b * m, b) == div(a, b) + m)
  assert(div(a - b * m, b) == div(a, b) - m)
  assert(div(a + c, b)     == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b))
  assert(div(a - c, b)     == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b))
  assert(mod(a + c, b)     == mod(mod(a, b) + mod(c, b), b))
  assert(mod(a - c, b)     == mod(mod(a, b) - mod(c, b), b))
  assert(mod(a + c, b)     == mod(a, b) + mod(c, b) - b * div(mod(a, b) + mod(c, b), b))
  assert(mod(a - c, b)     == mod(a, b) - mod(c, b) - b * div(mod(a, b) - mod(c, b), b))
  assert(if a >= 0 && b > 0 && mod(a, b) != b - 1 then mod(a + 1, b) == mod(a, b) + 1 else true)
  assert(if a >= 0 && b > 0 && mod(a, b) == b - 1 then mod(a + 1, b) == 0 else true)
  assert(if a >= 0 && b > 0 && mod(a, b) != b - 1 then div(a + 1, b) == div(a, b) else true)
  assert(if a >= 0 && b > 0 && mod(a, b) == b - 1 then div(a + 1, b) == div(a, b) + 1 else true)

  (if a >= 0 && b > a then div(a,b) == 0 else true)  &&
          (if a >= 0 && b > a then mod(a,b) == a else true)  &&
          mod(b, b)         == 0                             &&
          div(b, b)         == 1                             &&
          mod(a + b * m, b) == mod(a, b)                     &&
          mod(a - b * m, b) == mod(a, b)                     &&
          mod(mod(a, b), b) == mod(a, b)                     &&
          div(a + b, b)     == div(a, b) + 1                 &&
          div(a - b, b)     == div(a, b) - 1                 &&
          div(a + b * m, b) == div(a, b) + m                 &&
          div(a - b * m, b) == div(a, b) - m                 &&
          div(a + c, b)     == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b)     &&
          div(a - c, b)     == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b)     &&
          mod(a + c, b)     == mod(mod(a, b) + mod(c, b), b)                             &&
          mod(a - c, b)     == mod(mod(a, b) - mod(c, b), b)                             &&
          mod(a + c, b)     == mod(a, b) + mod(c, b) - b * div(mod(a, b) + mod(c, b), b) &&
          mod(a - c, b)     == mod(a, b) - mod(c, b) - b * div(mod(a, b) - mod(c, b), b) &&
          (if a >= 0 && b > 0 && mod(a, b) != b - 1 then mod(a + 1, b) == mod(a, b) + 1 else true) &&
          (if a >= 0 && b > 0 && mod(a, b) == b - 1 then mod(a + 1, b) == 0 else true) &&
          (if a >= 0 && b > 0 && mod(a, b) != b - 1 then div(a + 1, b) == div(a, b) else true) &&
          (if a >= 0 && b > 0 && mod(a, b) == b - 1 then div(a + 1, b) == div(a, b) + 1 else true)
 }.holds
}
```
</details>

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
[Formal Verification - Wikipedia, 2024](https://en.wikipedia.org/wiki/Formal_verification)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
 Sanghavi, Alok (May 21, 2010). "What is formal verification?". EE Times Asia.

<a name="ref3" id="ref3" href="#ref3">[3]</a>
[Stainless - Program Verification, 2024](https://epfl-lara.github.io/stainless/intro.html)

## Appendices

### Scala Stainless Verification Log Output

```bash
java 21.0.7-zulu is already installed.

Using java version 21.0.7-zulu in this shell.

[ Info  ] Compiling with standard Scala 3.3.3 compiler front end...
[ Info  ] Finished compiling                                       

[ Info  ] Preprocessing the symbols...                             
[ Info  ] Preprocessing finished                                   

[ Info  ] Running phase ConstructsUsage                            
[ Info  ] Running phase PartialFunctions                           
[ Info  ] Running phase XlangLowering                              
[ Info  ] Running phase InnerClasses                               
[ Info  ] Running phase Laws                                       
[ Info  ] Running phase SuperInvariants                            
[ Info  ] Running phase SuperCalls                                 
[ Info  ] Running phase Sealing                                    
[ Info  ] Running phase MethodLifting                              
[ Info  ] Running phase MergeInvariants                            
[ Info  ] Running phase FieldAccessors                             
[ Info  ] Running phase ValueClasses                               
[ Info  ] Running phase MethodsLowering                            
[ Info  ] Running phase ExceptionLifting                           
[ Info  ] Running phase EffectElaboration                          
[ Info  ] Running phase AntiAliasing                               
[ Info  ] Running phase ReturnElimination                          
[ Info  ] Running phase ImperativeCodeElimination                  
[ Info  ] Running phase ImperativeCleanup                          
[ Info  ] Running phase AdtSpecialization                          
[ Info  ] Running phase RefinementLifting                          
[ Info  ] Running phase TypeEncoding                               
[ Info  ] Running phase InvariantInitialization                    
[ Info  ] Running phase FunctionClosure                            
[ Info  ] Running phase FunctionSpecialization                     
[ Info  ] Running phase UnfoldOpaque                               
[ Info  ] Running phase CallSiteInline                             
[ Info  ] Running phase ChooseInjector                             
[ Info  ] Running phase ChooseEncoder                              
[ Info  ] Running phase FunctionInlining                           
[ Info  ] Running phase TraceInductElimination                     
[ Info  ] Running phase SizedADTExtraction                         
[ Info  ] Running phase InductElimination                          
[ Info  ] Running phase MeasureInference                           
[ Info  ] Inferring measure for sum...                  

Warning ] The Z3 native interface is not available. Falling back onto smt-z3.

[ Info  ] Inferring measure for ++...
[ Info  ] Inferring measure for last...
[ Info  ] Inferring measure for apply...
[ Info  ] Running phase PartialEvaluation
[ Info  ] Finished lowering the symbols  

[ Info  ] Generating VCs for 170 functions...
[ Info  ] Finished generating VCs            
[ Info  ] Starting verification...

[ Info  ] Verified: 2723 / 2723
[ Info  ] Done in 60.53s
[ Info  ]   ┌───────────────────┐
[ Info  ] ╔═╡ stainless summary ╞══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗
[ Info  ] ║ └───────────────────┘                                                                                                                                                                                                                          ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:75:17:              ALessBSameModDecreaseDiv                        class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:78:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:79:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
  ```

<details>
<summary>...</summary>

  ```bash
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:80:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:81:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:82:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:83:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:84:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:85:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:87:16:              ALessBSameModDecreaseDiv                        class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:88:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:89:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:90:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:91:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:92:5:               ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:94:5:               ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](mod(a, b), solve(inp... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:94:5:               ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](mod(a, b), solve(inp... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:95:7:               ALessBSameModDecreaseDiv                        precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:99:5:               ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](div(a, b), solve(inp... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:99:5:               ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](div(a, b), solve(inp... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:100:7:              ALessBSameModDecreaseDiv                        precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:105:20:             ALessBSameModDecreaseDiv                        class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:106:5:              ALessBSameModDecreaseDiv                        precond. (call modUniqueDiv(next, nextZero) (require 1/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:106:5:              ALessBSameModDecreaseDiv                        precond. (call modUniqueDiv(next, nextZero) (require 2/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:106:5:              ALessBSameModDecreaseDiv                        precond. (call modUniqueDiv(next, nextZero) (require 3/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:106:5:              ALessBSameModDecreaseDiv                        precond. (call modUniqueDiv(next, nextZero) (require 4/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:106:5:              ALessBSameModDecreaseDiv                        precond. (call modUniqueDiv(next, nextZero) (require 5/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:108:5:              ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](solve(input).mod, so... (require 1/5))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:108:5:              ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](solve(input).mod, so... (require 2/5))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:108:5:              ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](solve(input).mod, so... (require 3/5))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:108:5:              ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](solve(input).mod, so... (require 4/5))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:108:5:              ALessBSameModDecreaseDiv                        precond. (call equality[BigInt](solve(input).mod, so... (require 5/5))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:111:7:              ALessBSameModDecreaseDiv                        class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:113:7:              ALessBSameModDecreaseDiv                        precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:114:7:              ALessBSameModDecreaseDiv                        precond. (call mod(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:117:5:              ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:117:12:             ALessBSameModDecreaseDiv                        precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:117:30:             ALessBSameModDecreaseDiv                        precond. (call mod(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:118:19:             ALessBSameModDecreaseDiv                        precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:118:37:             ALessBSameModDecreaseDiv                        precond. (call mod(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:120:5:              ALessBSameModDecreaseDiv                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:121:19:             ALessBSameModDecreaseDiv                        precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:121:41:             ALessBSameModDecreaseDiv                        precond. (call div(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:123:5:              ALessBSameModDecreaseDiv                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:164:7:              ALessMultipleTimesBSameMod                      precond. (call ALessBSameModDecreaseDiv(a, b))                          trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:165:7:              ALessMultipleTimesBSameMod                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:165:14:             ALessMultipleTimesBSameMod                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:165:32:             ALessMultipleTimesBSameMod                      precond. (call mod(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:166:7:              ALessMultipleTimesBSameMod                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:166:14:             ALessMultipleTimesBSameMod                      measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:166:14:             ALessMultipleTimesBSameMod                      precond. (call ALessMultipleTimesBSameMod(a - b, b, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:166:14:             ALessMultipleTimesBSameMod                      precond. (call ALessMultipleTimesBSameMod(a - b, b, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:167:7:              ALessMultipleTimesBSameMod                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:167:14:             ALessMultipleTimesBSameMod                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:167:32:             ALessMultipleTimesBSameMod                      precond. (call mod(a - b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:168:7:              ALessMultipleTimesBSameMod                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:168:14:             ALessMultipleTimesBSameMod                      precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:168:36:             ALessMultipleTimesBSameMod                      precond. (call div(a - b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:171:5:              ALessMultipleTimesBSameMod                      postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:171:5:              ALessMultipleTimesBSameMod                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:171:22:             ALessMultipleTimesBSameMod                      precond. (call mod(a - b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:172:7:              ALessMultipleTimesBSameMod                      precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:172:28:             ALessMultipleTimesBSameMod                      precond. (call div(a - b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:172:41:             ALessMultipleTimesBSameMod                      non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:13:17:              APlusBSameModPlusDiv                            class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:16:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:17:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:18:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:19:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:20:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:21:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:22:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:23:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:25:16:              APlusBSameModPlusDiv                            class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:26:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:27:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:28:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:29:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:30:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:32:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](mod(a, b), solve(inp... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:32:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](mod(a, b), solve(inp... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:33:7:               APlusBSameModPlusDiv                            precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:38:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](div(a, b), solve(inp... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:38:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](div(a, b), solve(inp... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:39:7:               APlusBSameModPlusDiv                            precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:44:20:              APlusBSameModPlusDiv                            class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:45:5:               APlusBSameModPlusDiv                            precond. (call modUniqueDiv(next, nextZero) (require 1/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:45:5:               APlusBSameModPlusDiv                            precond. (call modUniqueDiv(next, nextZero) (require 2/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:45:5:               APlusBSameModPlusDiv                            precond. (call modUniqueDiv(next, nextZero) (require 3/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:45:5:               APlusBSameModPlusDiv                            precond. (call modUniqueDiv(next, nextZero) (require 4/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:45:5:               APlusBSameModPlusDiv                            precond. (call modUniqueDiv(next, nextZero) (require 5/5))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:46:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:46:12:              APlusBSameModPlusDiv                            precond. (call mod(solved.a + solved.b, solved.b))                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:47:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:48:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:49:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:49:12:              APlusBSameModPlusDiv                            precond. (call mod(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:51:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](solve(input).mod, ne... (require 1/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:51:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](solve(input).mod, ne... (require 2/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:51:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](solve(input).mod, ne... (require 3/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:51:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](solve(input).mod, ne... (require 4/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:51:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](solve(input).mod, ne... (require 5/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:51:5:               APlusBSameModPlusDiv                            precond. (call equality[BigInt](solve(input).mod, ne... (require 6/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:56:7:               APlusBSameModPlusDiv                            class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:57:7:               APlusBSameModPlusDiv                            precond. (call mod(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:58:7:               APlusBSameModPlusDiv                            precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:61:19:              APlusBSameModPlusDiv                            precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:61:37:              APlusBSameModPlusDiv                            precond. (call mod(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:62:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:62:12:              APlusBSameModPlusDiv                            precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:62:30:              APlusBSameModPlusDiv                            precond. (call mod(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:64:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:65:5:               APlusBSameModPlusDiv                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:65:12:              APlusBSameModPlusDiv                            precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:65:34:              APlusBSameModPlusDiv                            precond. (call div(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:66:19:              APlusBSameModPlusDiv                            precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:66:41:              APlusBSameModPlusDiv                            precond. (call div(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:69:5:               APlusBSameModPlusDiv                            postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:146:7:              APlusMultipleTimesBSameMod                      precond. (call APlusBSameModPlusDiv(a, b))                              trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:147:7:              APlusMultipleTimesBSameMod                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:147:14:             APlusMultipleTimesBSameMod                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:147:32:             APlusMultipleTimesBSameMod                      precond. (call mod(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:148:7:              APlusMultipleTimesBSameMod                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:148:14:             APlusMultipleTimesBSameMod                      measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:148:14:             APlusMultipleTimesBSameMod                      precond. (call APlusMultipleTimesBSameMod(a + b, b, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:148:14:             APlusMultipleTimesBSameMod                      precond. (call APlusMultipleTimesBSameMod(a + b, b, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:149:7:              APlusMultipleTimesBSameMod                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:149:14:             APlusMultipleTimesBSameMod                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:149:32:             APlusMultipleTimesBSameMod                      precond. (call mod(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:150:7:              APlusMultipleTimesBSameMod                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:150:14:             APlusMultipleTimesBSameMod                      precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:150:36:             APlusMultipleTimesBSameMod                      precond. (call div(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:153:5:              APlusMultipleTimesBSameMod                      postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:153:5:              APlusMultipleTimesBSameMod                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:153:22:             APlusMultipleTimesBSameMod                      precond. (call mod(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:154:5:              APlusMultipleTimesBSameMod                      precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:154:26:             APlusMultipleTimesBSameMod                      precond. (call div(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:154:39:             APlusMultipleTimesBSameMod                      non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:130:7:              ATimesBSameMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:131:7:              ATimesBSameMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:131:14:             ATimesBSameMod                                  precond. (call APlusMultipleTimesBSameMod(a, b, m) (require 1/2))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:131:14:             ATimesBSameMod                                  precond. (call APlusMultipleTimesBSameMod(a, b, m) (require 2/2))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:133:7:              ATimesBSameMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:134:7:              ATimesBSameMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:134:14:             ATimesBSameMod                                  precond. (call ALessMultipleTimesBSameMod(a, b, -m) (require 1/2))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:134:14:             ATimesBSameMod                                  precond. (call ALessMultipleTimesBSameMod(a, b, -m) (require 2/2))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:136:5:              ATimesBSameMod                                  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:136:5:              ATimesBSameMod                                  precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:136:23:             ATimesBSameMod                                  precond. (call mod(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:137:7:              ATimesBSameMod                                  precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:137:29:             ATimesBSameMod                                  precond. (call div(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:227:5:              LessDivMoreMod                                  precond. (call equality[BigInt](a, div * b + mod, (d... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:227:5:              LessDivMoreMod                                  precond. (call equality[BigInt](a, div * b + mod, (d... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:232:5:              LessDivMoreMod                                  precond. (call MoreDivLessMod(a, b, div - BigInt("1"... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:232:5:              LessDivMoreMod                                  precond. (call MoreDivLessMod(a, b, div - BigInt("1"... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:234:5:              LessDivMoreMod                                  class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:234:5:              LessDivMoreMod                                  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:234:37:             LessDivMoreMod                                  class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:269:5:              LessDivMoreModManyTimes                         precond. (call LessDivMoreMod(a, b, div, mod) (require 1/2))            trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:269:5:              LessDivMoreModManyTimes                         precond. (call LessDivMoreMod(a, b, div, mod) (require 2/2))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:271:7:              LessDivMoreModManyTimes                         measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:271:7:              LessDivMoreModManyTimes                         precond. (call LessDivMoreModManyTimes(a, b, div - B... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:271:7:              LessDivMoreModManyTimes                         precond. (call LessDivMoreModManyTimes(a, b, div - B... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:271:7:              LessDivMoreModManyTimes                         precond. (call LessDivMoreModManyTimes(a, b, div - B... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:272:7:              LessDivMoreModManyTimes                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:272:14:             LessDivMoreModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:272:54:             LessDivMoreModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:274:5:              LessDivMoreModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:274:5:              LessDivMoreModManyTimes                         postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:274:33:             LessDivMoreModManyTimes                         non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:274:47:             LessDivMoreModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:65:5:                                             ModLessB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:66:5:                                             ModLessB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:67:5:                                             ModLessB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:68:16:                                            ModLessB                                        class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:69:5:                                             ModLessB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:70:5:                                             ModLessB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:71:5:                                             ModLessB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:72:5:                                             ModLessB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:53:6:                                             ModPlusB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:54:6:                                             ModPlusB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:55:6:                                             ModPlusB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:56:16:                                            ModPlusB                                        class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:57:6:                                             ModPlusB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:58:6:                                             ModPlusB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:59:6:                                             ModPlusB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:60:6:                                             ModPlusB                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:178:16:             MoreDivLessMod                                  class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:179:16:             MoreDivLessMod                                  class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:181:23:             MoreDivLessMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:182:23:             MoreDivLessMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:185:7:              MoreDivLessMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:185:28:             MoreDivLessMod                                  precond. (call increaseMod(div1))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:187:9:              MoreDivLessMod                                  precond. (call equality[DivMod](solve(div2), increas... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:187:9:              MoreDivLessMod                                  precond. (call equality[DivMod](solve(div2), increas... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:187:9:              MoreDivLessMod                                  precond. (call equality[DivMod](solve(div2), increas... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:189:11:             MoreDivLessMod                                  precond. (call increaseMod(div2))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:190:11:             MoreDivLessMod                                  precond. (call increaseMod(div1))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:194:9:              MoreDivLessMod                                  precond. (call equality[DivMod](increaseMod(div1), s... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:194:9:              MoreDivLessMod                                  precond. (call equality[DivMod](increaseMod(div1), s... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:195:11:             MoreDivLessMod                                  precond. (call increaseMod(div1))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:200:7:              MoreDivLessMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:204:9:              MoreDivLessMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:205:9:              MoreDivLessMod                                  precond. (call equality[DivMod](solve(div1), reduceM... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:205:9:              MoreDivLessMod                                  precond. (call equality[DivMod](solve(div1), reduceM... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:207:11:             MoreDivLessMod                                  precond. (call reduceMod(div1))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:211:9:              MoreDivLessMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:212:9:              MoreDivLessMod                                  precond. (call equality[DivMod](solve(div2), reduceM... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:212:9:              MoreDivLessMod                                  precond. (call equality[DivMod](solve(div2), reduceM... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:214:11:             MoreDivLessMod                                  precond. (call reduceMod(div2))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:219:5:              MoreDivLessMod                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:220:5:              MoreDivLessMod                                  class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:220:5:              MoreDivLessMod                                  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:220:48:             MoreDivLessMod                                  class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:243:5:              MoreDivLessModManyTimes                         precond. (call MoreDivLessMod(a, b, div, mod) (require 1/2))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:243:5:              MoreDivLessModManyTimes                         precond. (call MoreDivLessMod(a, b, div, mod) (require 2/2))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:252:7:              MoreDivLessModManyTimes                         precond. (call MoreDivLessMod(a, b, prevDiv, prevMod) (require 1/2))    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:252:7:              MoreDivLessModManyTimes                         precond. (call MoreDivLessMod(a, b, prevDiv, prevMod) (require 2/2))    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:254:7:              MoreDivLessModManyTimes                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:254:14:             MoreDivLessModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:254:54:             MoreDivLessModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:255:7:              MoreDivLessModManyTimes                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:255:14:             MoreDivLessModManyTimes                         measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:255:14:             MoreDivLessModManyTimes                         precond. (call MoreDivLessModManyTimes(a, b, div, mo... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:255:14:             MoreDivLessModManyTimes                         precond. (call MoreDivLessModManyTimes(a, b, div, mo... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:255:14:             MoreDivLessModManyTimes                         precond. (call MoreDivLessModManyTimes(a, b, div, mo... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:255:54:             MoreDivLessModManyTimes                         non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:257:7:              MoreDivLessModManyTimes                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:257:14:             MoreDivLessModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:257:56:             MoreDivLessModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:260:5:              MoreDivLessModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:260:5:              MoreDivLessModManyTimes                         postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:260:47:             MoreDivLessModManyTimes                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:14:7:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:14:14:                                PropertySummary                                 precond. (call modSmallDividend(a, b) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:14:14:                                PropertySummary                                 precond. (call modSmallDividend(a, b) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:14:14:                                PropertySummary                                 precond. (call modSmallDividend(a, b) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:17:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:17:12:                                PropertySummary                                 precond. (call modIdempotence(a, b))                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:18:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:18:12:                                PropertySummary                                 precond. (call modIdentity(b))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:19:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:19:12:                                PropertySummary                                 precond. (call APlusBSameModPlusDiv(a, b))                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:20:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:20:12:                                PropertySummary                                 precond. (call ALessBSameModDecreaseDiv(a, b))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:21:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:21:12:                                PropertySummary                                 precond. (call ATimesBSameMod(a, b, m))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:23:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:23:12:                                PropertySummary                                 precond. (call ALessMultipleTimesBSameMod(a, b, m) (require 1/2))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:23:12:                                PropertySummary                                 precond. (call ALessMultipleTimesBSameMod(a, b, m) (require 2/2))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:12:                                PropertySummary                                 precond. (call APlusMultipleTimesBSameMod(a, b, m) (require 1/2))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:12:                                PropertySummary                                 precond. (call APlusMultipleTimesBSameMod(a, b, m) (require 2/2))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:26:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:26:12:                                PropertySummary                                 precond. (call modAdd(a, b, c))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:27:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:27:12:                                PropertySummary                                 precond. (call modLess(a, b, c))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:29:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:29:12:                                PropertySummary                                 precond. (call modModPlus(a, b, c))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:30:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:30:12:                                PropertySummary                                 precond. (call modModMinus(a, b, c))                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:32:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:32:12:                                PropertySummary                                 precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:32:29:                                PropertySummary                                 precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:32:33:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:32:45:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:12:                                PropertySummary                                 precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:29:                                PropertySummary                                 precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:33:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:45:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:36:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:35:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:35:36:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:26:                                PropertySummary                                 precond. (call mod(mod(a, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:30:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:47:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:37:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:37:12:                                PropertySummary                                 precond. (call mod(b, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:38:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:38:12:                                PropertySummary                                 precond. (call div(b, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:39:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:39:12:                                PropertySummary                                 precond. (call mod(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:39:33:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:40:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:40:12:                                PropertySummary                                 precond. (call mod(a - b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:40:33:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:12:                                PropertySummary                                 precond. (call div(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:33:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:12:                                PropertySummary                                 precond. (call div(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:33:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:12:                                PropertySummary                                 precond. (call div(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:33:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:12:                                PropertySummary                                 precond. (call div(a - b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:33:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:12:                                PropertySummary                                 precond. (call div(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:33:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:45:                                PropertySummary                                 precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:57:                                PropertySummary                                 precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:61:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:73:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:12:                                PropertySummary                                 precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:33:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:45:                                PropertySummary                                 precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:57:                                PropertySummary                                 precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:61:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:73:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:12:                                PropertySummary                                 precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:33:                                PropertySummary                                 precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:37:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:49:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:12:                                PropertySummary                                 precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:33:                                PropertySummary                                 precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:37:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:49:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:12:                                PropertySummary                                 precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:33:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:45:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:61:                                PropertySummary                                 precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:65:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:77:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:5:                                 PropertySummary                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:12:                                PropertySummary                                 precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:33:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:45:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:61:                                PropertySummary                                 precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:65:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:77:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:52:5:                                 PropertySummary                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:52:30:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:53:30:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:54:5:                                 PropertySummary                                 precond. (call mod(b, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:55:5:                                 PropertySummary                                 precond. (call div(b, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:56:5:                                 PropertySummary                                 precond. (call mod(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:56:26:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:57:5:                                 PropertySummary                                 precond. (call mod(a - b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:57:26:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:58:5:                                 PropertySummary                                 precond. (call mod(mod(a, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:58:9:                                 PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:58:26:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:59:5:                                 PropertySummary                                 precond. (call div(a + b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:59:26:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:60:5:                                 PropertySummary                                 precond. (call div(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:60:26:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:61:5:                                 PropertySummary                                 precond. (call div(a + b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:61:26:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:62:5:                                 PropertySummary                                 precond. (call div(a - b * m, b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:62:26:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:63:5:                                 PropertySummary                                 precond. (call div(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:63:26:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:63:38:                                PropertySummary                                 precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:63:50:                                PropertySummary                                 precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:63:54:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:63:66:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:5:                                 PropertySummary                                 precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:26:                                PropertySummary                                 precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:38:                                PropertySummary                                 precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:50:                                PropertySummary                                 precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:54:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:66:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:5:                                 PropertySummary                                 precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:26:                                PropertySummary                                 precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:30:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:42:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:66:5:                                 PropertySummary                                 precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:66:26:                                PropertySummary                                 precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:66:30:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:66:42:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:5:                                 PropertySummary                                 precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:26:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:38:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:54:                                PropertySummary                                 precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:58:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:70:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:5:                                 PropertySummary                                 precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:26:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:38:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:54:                                PropertySummary                                 precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:58:                                PropertySummary                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:70:                                PropertySummary                                 precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:23:15:                                acc                                             non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:27:12:                                acc                                             precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:27:26:                                acc                                             measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:27:35:                                acc                                             precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:27:46:                                acc                                             precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:86:7:                    accessTailShift                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:87:58:                   accessTailShift                                 precond. (call tail[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:88:5:                    accessTailShift                                 precond. (call apply[T](tail[T](list), position))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:88:5:                    accessTailShift                                 precond. (call tail[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:88:28:                   accessTailShift                                 precond. (call apply[T](list, position + BigInt("1")))                  valid from cache            0.0 ║
[ Info  ] ║                                                                                        addOne                                          postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║                                                                                        addOne                                          postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:232:7:                          addOne                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:232:14:                         addOne                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:233:7:                          addOne                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:233:14:                         addOne                                          precond. (call mod(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:234:7:                          addOne                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:234:14:                         addOne                                          precond. (call mod(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:234:31:                         addOne                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:235:7:                          addOne                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:235:14:                         addOne                                          precond. (call div(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:235:31:                         addOne                                          precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:237:9:                          addOne                                          precond. (call mod(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:237:26:                         addOne                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:238:9:                          addOne                                          precond. (call div(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:238:26:                         addOne                                          precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:241:9:                          addOne                                          body assertion: match exhaustiveness                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:241:9:                          addOne                                          postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:241:9:                          addOne                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:242:7:                          addOne                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:242:14:                         addOne                                          precond. (call mod(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:243:7:                          addOne                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:243:14:                         addOne                                          precond. (call div(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:243:31:                         addOne                                          precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:245:9:                          addOne                                          precond. (call mod(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:246:9:                          addOne                                          precond. (call div(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:246:26:                         addOne                                          precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:249:5:                          addOne                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:249:5:                          addOne                                          body assertion: match exhaustiveness                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:249:5:                          addOne                                          postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:249:12:                         addOne                                          precond. (call mod(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:249:29:                         addOne                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:250:5:                          addOne                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:250:12:                         addOne                                          precond. (call div(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:250:29:                         addOne                                          precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:251:5:                          addOne                                          postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:251:5:                          addOne                                          precond. (call mod(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:251:22:                         addOne                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:252:5:                          addOne                                          precond. (call div(a + BigInt("1"), b))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:252:22:                         addOne                                          precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:231:27:                       afterMethodListAndZeroModCountAreOnSync         precond. (call checkMod(cycle, dividend))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:233:33:                       afterMethodListAndZeroModCountAreOnSync         precond. (call allModValuesAreZero(cycleAfterCheck, ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:237:16:                       afterMethodListAndZeroModCountAreOnSync         precond. (call noModValuesAreZero(cycleAfterCheck, d...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:241:16:                       afterMethodListAndZeroModCountAreOnSync         precond. (call someModValuesAreZero(cycleAfterCheck,...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:250:7:                        afterMethodListAndZeroModCountAreOnSync         precond. (call allModValuesAreZero(cycleAfterCheck, ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:251:10:                       afterMethodListAndZeroModCountAreOnSync         precond. (call noModValuesAreZero(cycleAfterCheck, d...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:252:10:                       afterMethodListAndZeroModCountAreOnSync         precond. (call someModValuesAreZero(cycleAfterCheck,...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:254:8:                        afterMethodListAndZeroModCountAreOnSync         precond. (call noModValuesAreZero(cycleAfterCheck, d...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:255:10:                       afterMethodListAndZeroModCountAreOnSync         precond. (call allModValuesAreZero(cycleAfterCheck, ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:256:10:                       afterMethodListAndZeroModCountAreOnSync         precond. (call someModValuesAreZero(cycleAfterCheck,...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:258:7:                        afterMethodListAndZeroModCountAreOnSync         precond. (call someModValuesAreZero(cycleAfterCheck,...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:259:10:                       afterMethodListAndZeroModCountAreOnSync         precond. (call allModValuesAreZero(cycleAfterCheck, ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:260:10:                       afterMethodListAndZeroModCountAreOnSync         precond. (call noModValuesAreZero(cycleAfterCheck, d...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:80:5:                                            allModValuesAreZero                             precond. (call countModZero(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:80:5:                                            allModValuesAreZero                             precond. (call countModZero(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:80:5:                                            allModValuesAreZero                             precond. (call countModZero(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:96:13:                        allModZeroPropagate                             precond. (call countModZero(cycle.values, dividendA) (require 1/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:96:13:                        allModZeroPropagate                             precond. (call countModZero(cycle.values, dividendA) (require 2/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:96:13:                        allModZeroPropagate                             precond. (call countModZero(cycle.values, dividendA) (require 3/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:97:13:                        allModZeroPropagate                             precond. (call countModZero(cycle.values, dividendB) (require 1/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:97:13:                        allModZeroPropagate                             precond. (call countModZero(cycle.values, dividendB) (require 2/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:97:13:                        allModZeroPropagate                             precond. (call countModZero(cycle.values, dividendB) (require 3/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:101:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:102:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:103:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:105:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:106:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:107:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:109:18:                       allModZeroPropagate                             precond. (call checkMod(cycle, dividendA))                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:110:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:111:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:111:12:                       allModZeroPropagate                             precond. (call allModValuesAreZero(cycleA, dividendA))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:112:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:112:12:                       allModZeroPropagate                             precond. (call allModValuesAreZero(cycleA, dividendB))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:113:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:114:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:115:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:116:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:117:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:117:12:                       allModZeroPropagate                             precond. (call countModZero(cycle, dividendB) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:117:12:                       allModZeroPropagate                             precond. (call countModZero(cycle, dividendB) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:117:12:                       allModZeroPropagate                             precond. (call countModZero(cycle, dividendB) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:119:18:                       allModZeroPropagate                             precond. (call checkMod(cycleA, dividendB))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:120:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:121:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:121:12:                       allModZeroPropagate                             precond. (call allModValuesAreZero(cycleB, dividendA))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:122:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:122:12:                       allModZeroPropagate                             precond. (call allModValuesAreZero(cycleB, dividendB))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:123:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:124:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:125:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:126:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:127:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:128:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:129:5:                        allModZeroPropagate                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:131:5:                        allModZeroPropagate                             postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:131:5:                        allModZeroPropagate                             precond. (call allModValuesAreZero(cycleB, dividendA))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:132:7:                        allModZeroPropagate                             precond. (call allModValuesAreZero(cycleB, dividendB))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:190:13:                                          appendForAll                                    precond. (call countModZero(cycle.values, dividend) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:190:13:                                          appendForAll                                    precond. (call countModZero(cycle.values, dividend) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:190:13:                                          appendForAll                                    precond. (call countModZero(cycle.values, dividend) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:193:5:                                           appendForAll                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:193:12:                                          appendForAll                                    precond. (call tail[BigInt](newList))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:194:5:                                           appendForAll                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:194:12:                                          appendForAll                                    precond. (call head[BigInt](newList))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:195:5:                                           appendForAll                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:195:12:                                          appendForAll                                    precond. (call checkZeroForAll(newList, cycle.values) (require 1/3))    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:195:12:                                          appendForAll                                    precond. (call checkZeroForAll(newList, cycle.values) (require 2/3))    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:195:12:                                          appendForAll                                    precond. (call checkZeroForAll(newList, cycle.values) (require 3/3))    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:197:5:                                           appendForAll                                    class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:208:13:                                          appendForNone                                   precond. (call countModZero(cycle.values, dividend) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:208:13:                                          appendForNone                                   precond. (call countModZero(cycle.values, dividend) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:208:13:                                          appendForNone                                   precond. (call countModZero(cycle.values, dividend) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:211:5:                                           appendForNone                                   body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:211:12:                                          appendForNone                                   precond. (call tail[BigInt](newList))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:212:5:                                           appendForNone                                   body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:212:12:                                          appendForNone                                   precond. (call head[BigInt](newList))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:213:5:                                           appendForNone                                   body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:213:12:                                          appendForNone                                   precond. (call checkZeroForNone(newList, cycle.values) (require 1/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:213:12:                                          appendForNone                                   precond. (call checkZeroForNone(newList, cycle.values) (require 2/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:213:12:                                          appendForNone                                   precond. (call checkZeroForNone(newList, cycle.values) (require 3/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:215:5:                                           appendForNone                                   class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:226:13:                                          appendForSome                                   precond. (call countModZero(cycle.values, dividend) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:226:13:                                          appendForSome                                   precond. (call countModZero(cycle.values, dividend) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:226:13:                                          appendForSome                                   precond. (call countModZero(cycle.values, dividend) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:227:13:                                          appendForSome                                   precond. (call countModZero(cycle.values, dividend) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:227:13:                                          appendForSome                                   precond. (call countModZero(cycle.values, dividend) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:227:13:                                          appendForSome                                   precond. (call countModZero(cycle.values, dividend) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:230:5:                                           appendForSome                                   body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:230:12:                                          appendForSome                                   precond. (call tail[BigInt](newList))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:231:5:                                           appendForSome                                   body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:231:12:                                          appendForSome                                   precond. (call head[BigInt](newList))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:232:5:                                           appendForSome                                   body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:232:12:                                          appendForSome                                   precond. (call checkZeroForSome(newList, cycle.values) (require 1/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:232:12:                                          appendForSome                                   precond. (call checkZeroForSome(newList, cycle.values) (require 2/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:232:12:                                          appendForSome                                   precond. (call checkZeroForSome(newList, cycle.values) (require 3/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:234:5:                                           appendForSome                                   class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/Seq.scala:18:7:                                                apply                                           precond. (call apply[BigInt](thiss.previous, index))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/Seq.scala:21:23:                                               apply                                           precond. (call apply(thiss.loop, loopIndex))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/Seq.scala:22:37:                                               apply                                           measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/Seq.scala:22:37:                                               apply                                           precond. (call apply(thiss, index - BigInt("1")))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/Seq.scala:22:48:                                               apply                                           non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:43:17:                                           apply                                           precond. (call mod(value, size[BigInt](thiss.values)))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:44:5:                                            apply                                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:45:5:                                            apply                                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:46:5:                                            apply                                           precond. (call apply[BigInt](thiss.values, index))                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:105:5:                                           apply                                           class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/CycleIntegral.scala:16:7:                           apply                                           precond. (call apply(thiss.cycle, BigInt("0")))                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/CycleIntegral.scala:18:7:                           apply                                           precond. (call apply(thiss.cycle, position))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/CycleIntegral.scala:18:25:                          apply                                           measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/CycleIntegral.scala:18:25:                          apply                                           precond. (call apply(thiss, position - BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/CycleIntegral.scala:18:31:                          apply                                           non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:29:18:                                    apply                                           class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:30:5:                                     apply                                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:31:5:                                     apply                                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:32:5:                                     apply                                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:33:18:                                    apply                                           precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:33:40:                                    apply                                           precond. (call apply(integralValues(thiss), divMod.mod) (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:33:40:                                    apply                                           precond. (call apply(integralValues(thiss), divMod.mod) (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:33:40:                                    apply                                           precond. (call apply(integralValues(thiss), divMod.mod) (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:11:7:                                 apply                                           non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:16:7:                                 apply                                           precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:18:7:                                 apply                                           measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:18:7:                                 apply                                           precond. (call apply(Integral(tail[BigInt](thiss.lis... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:18:7:                                 apply                                           precond. (call apply(Integral(tail[BigInt](thiss.lis... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:18:7:                                 apply                                           precond. (call apply(Integral(tail[BigInt](thiss.lis... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:18:16:                                apply                                           precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:18:27:                                apply                                           precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:95:7:                                 assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:95:14:                                assertAccDiffMatchesList                        precond. (call assertAccDifferenceEqualsTailHead(thiss))                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:96:7:                                 assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:96:14:                                assertAccDiffMatchesList                        precond. (call apply(thiss, BigInt("0")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:96:14:                                assertAccDiffMatchesList                        precond. (call apply(thiss, BigInt("0")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:96:14:                                assertAccDiffMatchesList                        precond. (call apply(thiss, BigInt("0")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:96:26:                                assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), BigInt("0")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:97:7:                                 assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:97:14:                                assertAccDiffMatchesList                        precond. (call apply(thiss, BigInt("1")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:97:14:                                assertAccDiffMatchesList                        precond. (call apply(thiss, BigInt("1")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:97:14:                                assertAccDiffMatchesList                        precond. (call apply(thiss, BigInt("1")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:97:26:                                assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), BigInt("1")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:98:7:                                 assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:99:9:                                 assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position + ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:99:29:                                assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:99:46:                                assertAccDiffMatchesList                        precond. (call apply[BigInt](thiss.list, position + ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:100:9:                                assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:100:26:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:100:26:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:100:26:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:103:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:104:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:105:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:108:27:                               assertAccDiffMatchesList                        precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:108:38:                               assertAccDiffMatchesList                        precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:109:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:110:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:110:14:                               assertAccDiffMatchesList                        precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:111:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:111:14:                               assertAccDiffMatchesList                        measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:111:14:                               assertAccDiffMatchesList                        precond. (call assertAccDiffMatchesList(next, positi... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:111:14:                               assertAccDiffMatchesList                        precond. (call assertAccDiffMatchesList(next, positi... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:114:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:114:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:114:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:114:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:114:37:                               assertAccDiffMatchesList                        precond. (call apply(next, position - BigInt("1")) (require 1/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:114:37:                               assertAccDiffMatchesList                        precond. (call apply(next, position - BigInt("1")) (require 2/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:114:37:                               assertAccDiffMatchesList                        precond. (call apply(next, position - BigInt("1")) (require 3/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:115:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:115:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:115:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:115:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:115:37:                               assertAccDiffMatchesList                        precond. (call apply(next, position) (require 1/3))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:115:37:                               assertAccDiffMatchesList                        precond. (call apply(next, position) (require 2/3))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:115:37:                               assertAccDiffMatchesList                        precond. (call apply(next, position) (require 3/3))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:117:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:117:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:117:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:117:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:117:33:                               assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:118:7:                                assertAccDiffMatchesList                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:118:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:118:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:118:14:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:118:37:                               assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position + ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:120:5:                                assertAccDiffMatchesList                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:120:5:                                assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position + ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:120:25:                               assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:120:42:                               assertAccDiffMatchesList                        precond. (call apply[BigInt](thiss.list, position + ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:121:7:                                assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position + ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:121:28:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:121:28:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:121:28:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position + BigInt("1")) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:122:7:                                assertAccDiffMatchesList                        precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:122:24:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:122:24:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:122:24:                               assertAccDiffMatchesList                        precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:122:30:                               assertAccDiffMatchesList                        non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:63:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:63:12:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail(thiss)))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:63:12:                                assertAccDifferenceEqualsTailHead               precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:63:25:                                assertAccDifferenceEqualsTailHead               precond. (call head(Integral(tail[BigInt](thiss.list...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:63:34:                                assertAccDifferenceEqualsTailHead               precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:63:45:                                assertAccDifferenceEqualsTailHead               precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:64:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:64:12:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail(thiss)))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:64:12:                                assertAccDifferenceEqualsTailHead               precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:64:25:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail[BigInt](thiss.list)))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:64:25:                                assertAccDifferenceEqualsTailHead               precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:64:42:                                assertAccDifferenceEqualsTailHead               precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:65:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:65:12:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail(thiss)))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:65:12:                                assertAccDifferenceEqualsTailHead               precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:65:29:                                assertAccDifferenceEqualsTailHead               precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:65:43:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail[BigInt](thiss.list)))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:65:43:                                assertAccDifferenceEqualsTailHead               precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:65:60:                                assertAccDifferenceEqualsTailHead               precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:65:72:                                assertAccDifferenceEqualsTailHead               precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:66:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:66:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](acc(thiss), BigInt("1")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:66:22:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail(thiss)))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:66:22:                                assertAccDifferenceEqualsTailHead               precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:67:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:67:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:67:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:67:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:67:24:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail(thiss)))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:67:24:                                assertAccDifferenceEqualsTailHead               precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:68:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:68:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](acc(thiss), BigInt("0")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:68:22:                                assertAccDifferenceEqualsTailHead               precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:69:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:69:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:69:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:69:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:69:24:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail(thiss)))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:69:24:                                assertAccDifferenceEqualsTailHead               precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:70:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:70:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](thiss.list, BigInt("1")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:70:23:                                assertAccDifferenceEqualsTailHead               precond. (call head[BigInt](tail[BigInt](thiss.list)))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:70:23:                                assertAccDifferenceEqualsTailHead               precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:72:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:72:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("0")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:72:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("0")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:72:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("0")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:72:25:                                assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](acc(thiss), BigInt("0")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:73:5:                                 assertAccDifferenceEqualsTailHead               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:73:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:73:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:73:12:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:73:25:                                assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](acc(thiss), BigInt("1")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:75:5:                                 assertAccDifferenceEqualsTailHead               postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:75:5:                                 assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:75:5:                                 assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:75:5:                                 assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("1")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:75:16:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("0")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:75:16:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("0")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:75:16:                                assertAccDifferenceEqualsTailHead               precond. (call apply(thiss, BigInt("0")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:75:28:                                assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](thiss.list, BigInt("1")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:76:7:                                 assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](acc(thiss), BigInt("1")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:76:16:                                assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](acc(thiss), BigInt("0")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:76:28:                                assertAccDifferenceEqualsTailHead               precond. (call apply[BigInt](thiss.list, BigInt("1")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:140:5:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:143:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:143:14:                               assertAccMatchesApply                           precond. (call apply(thiss, BigInt("0")) (require 1/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:143:14:                               assertAccMatchesApply                           precond. (call apply(thiss, BigInt("0")) (require 2/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:143:14:                               assertAccMatchesApply                           precond. (call apply(thiss, BigInt("0")) (require 3/3))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:143:26:                               assertAccMatchesApply                           precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:144:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:144:14:                               assertAccMatchesApply                           precond. (call apply[BigInt](acc(thiss), BigInt("0")))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:144:24:                               assertAccMatchesApply                           precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:145:7:                                assertAccMatchesApply                           precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:145:24:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:145:24:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:145:24:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:147:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:148:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:149:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:151:27:                               assertAccMatchesApply                           precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:151:38:                               assertAccMatchesApply                           precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:152:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:152:14:                               assertAccMatchesApply                           precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:154:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:154:14:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:154:14:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:154:14:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:154:33:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 1/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:154:33:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 2/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:154:33:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 3/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:155:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:155:26:                               assertAccMatchesApply                           precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:156:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:156:14:                               assertAccMatchesApply                           precond. (call tail[BigInt](acc(thiss)))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:158:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:159:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:160:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:161:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:161:14:                               assertAccMatchesApply                           precond. (call assertTailShiftPosition[BigInt](acc(t... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:161:14:                               assertAccMatchesApply                           precond. (call assertTailShiftPosition[BigInt](acc(t... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:162:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:162:14:                               assertAccMatchesApply                           precond. (call apply[BigInt](tail[BigInt](acc(thiss)...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:162:14:                               assertAccMatchesApply                           precond. (call tail[BigInt](acc(thiss)))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:162:40:                               assertAccMatchesApply                           precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:163:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:163:14:                               assertAccMatchesApply                           precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:163:31:                               assertAccMatchesApply                           precond. (call apply[BigInt](tail[BigInt](acc(thiss)...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:163:31:                               assertAccMatchesApply                           precond. (call tail[BigInt](acc(thiss)))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:164:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:164:14:                               assertAccMatchesApply                           precond. (call apply[BigInt](tail[BigInt](acc(thiss)...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:164:14:                               assertAccMatchesApply                           precond. (call tail[BigInt](acc(thiss)))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:164:40:                               assertAccMatchesApply                           precond. (call apply[BigInt](acc(next), position - B...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:166:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:166:14:                               assertAccMatchesApply                           precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:166:31:                               assertAccMatchesApply                           precond. (call apply[BigInt](acc(next), position - B...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:167:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:167:14:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:167:14:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:167:14:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:167:33:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 1/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:167:33:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 2/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:167:33:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 3/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:169:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:169:14:                               assertAccMatchesApply                           measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:169:14:                               assertAccMatchesApply                           precond. (call assertAccMatchesApply(next, position ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:169:14:                               assertAccMatchesApply                           precond. (call assertAccMatchesApply(next, position ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:170:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:170:14:                               assertAccMatchesApply                           precond. (call apply[BigInt](acc(next), position - B...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:170:40:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 1/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:170:40:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 2/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:170:40:                               assertAccMatchesApply                           precond. (call apply(next, position - BigInt("1")) (require 3/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:171:7:                                assertAccMatchesApply                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:171:14:                               assertAccMatchesApply                           precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:171:31:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:171:31:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:171:31:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:173:5:                                assertAccMatchesApply                           postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:173:5:                                assertAccMatchesApply                           precond. (call apply[BigInt](acc(thiss), position))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:173:22:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:173:22:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:173:22:                               assertAccMatchesApply                           precond. (call apply(thiss, position) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:173:28:                               assertAccMatchesApply                           non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:53:27:                   assertAppendToSlice                             precond. (call apply[BigInt](list, to))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:55:5:                    assertAppendToSlice                             postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:55:5:                    assertAppendToSlice                             precond. (call slice(list, from, to) (require 1/3))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:55:5:                    assertAppendToSlice                             precond. (call slice(list, from, to) (require 2/3))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:55:5:                    assertAppendToSlice                             precond. (call slice(list, from, to) (require 3/3))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:56:7:                    assertAppendToSlice                             precond. (call slice(list, from, to - BigInt("1")) (require 1/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:56:7:                    assertAppendToSlice                             precond. (call slice(list, from, to - BigInt("1")) (require 2/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:56:7:                    assertAppendToSlice                             precond. (call slice(list, from, to - BigInt("1")) (require 3/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:56:51:                   assertAppendToSlice                             precond. (call apply[BigInt](list, to))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:38:12:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:43:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:43:14:                          assertCycleAccEqualsCycleIntegral               precond. (call div(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:44:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:44:14:                          assertCycleAccEqualsCycleIntegral               precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:45:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:45:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), BigIn... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:45:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), BigIn... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:45:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), BigIn... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:45:44:                          assertCycleAccEqualsCycleIntegral               precond. (call head[BigInt](cycleAcc.cycle.values))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:46:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:46:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, BigInt("0")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:46:29:                          assertCycleAccEqualsCycleIntegral               precond. (call div(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:46:51:                          assertCycleAccEqualsCycleIntegral               precond. (call last(integralValues(cycleAcc)))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:46:82:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), mod(p... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:46:82:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), mod(p... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:46:82:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), mod(p... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:46:106:                         assertCycleAccEqualsCycleIntegral               precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:47:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:47:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, BigInt("0")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:47:33:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), BigIn... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:47:33:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), BigIn... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:47:33:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(integralValues(cycleAcc), BigIn... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:48:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:48:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, BigInt("0")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:48:29:                          assertCycleAccEqualsCycleIntegral               precond. (call head[BigInt](cycleAcc.cycle.values))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:50:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:50:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, BigInt("0")))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:50:34:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:51:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:51:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, BigInt("0")))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:51:34:                          assertCycleAccEqualsCycleIntegral               precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:51:61:                          assertCycleAccEqualsCycleIntegral               precond. (call mod(BigInt("0"), size))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:52:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:52:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, BigInt("0")))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:52:34:                          assertCycleAccEqualsCycleIntegral               precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:53:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:53:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, BigInt("0")))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:53:34:                          assertCycleAccEqualsCycleIntegral               precond. (call head[BigInt](cycleIntegral.cycle.values))                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:55:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:55:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:55:36:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:57:7:                           assertCycleAccEqualsCycleIntegral               measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:57:7:                           assertCycleAccEqualsCycleIntegral               precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 1/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:57:7:                           assertCycleAccEqualsCycleIntegral               precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 2/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:57:7:                           assertCycleAccEqualsCycleIntegral               precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 3/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:57:7:                           assertCycleAccEqualsCycleIntegral               precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 4/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:57:7:                           assertCycleAccEqualsCycleIntegral               precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 5/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:57:7:                           assertCycleAccEqualsCycleIntegral               precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 6/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:63:7:                           assertCycleAccEqualsCycleIntegral               precond. (call assertSimplifiedDiffValuesMatchCycle(...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:65:9:                           assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:65:9:                           assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:65:30:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position - BigInt("1")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:66:11:                          assertCycleAccEqualsCycleIntegral               precond. (call apply[BigInt](cycleAcc.cycle.values, ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:66:33:                          assertCycleAccEqualsCycleIntegral               precond. (call mod(position, size(integralValues(cyc...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:68:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:70:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:70:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:70:36:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position - BigInt("1")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:70:61:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc.cycle, position))                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:72:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:72:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position - BigInt("1")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:72:40:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:74:7:                           assertCycleAccEqualsCycleIntegral               precond. (call assertDiffEqualsCycleValue(cycleInteg...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:75:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:75:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:75:41:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:75:71:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:77:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:77:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:77:47:                          assertCycleAccEqualsCycleIntegral               precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:77:74:                          assertCycleAccEqualsCycleIntegral               precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:78:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:78:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc.cycle, position))                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:78:42:                          assertCycleAccEqualsCycleIntegral               precond. (call apply[BigInt](cycleAcc.cycle.values, ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:78:64:                          assertCycleAccEqualsCycleIntegral               precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:79:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:80:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:80:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply[BigInt](cycleAcc.cycle.values, ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:80:36:                          assertCycleAccEqualsCycleIntegral               precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:80:60:                          assertCycleAccEqualsCycleIntegral               precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:80:87:                          assertCycleAccEqualsCycleIntegral               precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:81:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:81:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc.cycle, position))                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:81:42:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc.cycle, position))                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:83:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:83:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:83:41:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:83:71:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:84:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:84:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:84:41:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position - BigInt("1")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:84:71:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:85:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:85:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:85:41:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position - BigInt("1")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:85:71:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc.cycle, position))                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:87:14:                          assertCycleAccEqualsCycleIntegral               body assertion                                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:87:14:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:87:36:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:89:5:                           assertCycleAccEqualsCycleIntegral               postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:89:5:                           assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleAcc, position))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:89:27:                          assertCycleAccEqualsCycleIntegral               precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:89:41:                          assertCycleAccEqualsCycleIntegral               non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:96:7:      assertCycleIntegralEqualsSliceSum               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:98:7:      assertCycleIntegralEqualsSliceSum               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:98:14:     assertCycleIntegralEqualsSliceSum               measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:98:14:     assertCycleIntegralEqualsSliceSum               precond. (call assertCycleIntegralEqualsSliceSum(cyc... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:98:14:     assertCycleIntegralEqualsSliceSum               precond. (call assertCycleIntegralEqualsSliceSum(cyc... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:99:7:      assertCycleIntegralEqualsSliceSum               body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:99:14:     assertCycleIntegralEqualsSliceSum               precond. (call assertCycleIntegralEqualsSumSmallPosi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:99:14:     assertCycleIntegralEqualsSliceSum               precond. (call assertCycleIntegralEqualsSumSmallPosi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:99:14:     assertCycleIntegralEqualsSliceSum               precond. (call assertCycleIntegralEqualsSumSmallPosi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:101:5:     assertCycleIntegralEqualsSliceSum               postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:101:19:    assertCycleIntegralEqualsSliceSum               precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:101:19:    assertCycleIntegralEqualsSliceSum               precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:102:7:     assertCycleIntegralEqualsSliceSum               precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:102:21:    assertCycleIntegralEqualsSliceSum               non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:25:62:     assertCycleIntegralEqualsSumFirstPosition       precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:26:5:      assertCycleIntegralEqualsSumFirstPosition       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:28:76:     assertCycleIntegralEqualsSumFirstPosition       precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:29:5:      assertCycleIntegralEqualsSumFirstPosition       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:29:69:     assertCycleIntegralEqualsSumFirstPosition       precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:30:5:      assertCycleIntegralEqualsSumFirstPosition       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:30:12:     assertCycleIntegralEqualsSumFirstPosition       precond. (call apply(cycleIntegral, BigInt("0")))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:30:61:     assertCycleIntegralEqualsSumFirstPosition       precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:31:5:      assertCycleIntegralEqualsSumFirstPosition       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:31:25:     assertCycleIntegralEqualsSumFirstPosition       precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:31:25:     assertCycleIntegralEqualsSumFirstPosition       precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:32:5:      assertCycleIntegralEqualsSumFirstPosition       postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:32:19:     assertCycleIntegralEqualsSumFirstPosition       precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:32:19:     assertCycleIntegralEqualsSumFirstPosition       precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:32:63:     assertCycleIntegralEqualsSumFirstPosition       precond. (call apply(cycleIntegral, BigInt("0")))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:48:27:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:48:27:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:48:82:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:50:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:50:12:     assertCycleIntegralEqualsSumSmallPositions      precond. (call assertNextPosition(cycleIntegral, pos...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:51:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:51:12:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:51:39:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:51:71:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:52:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:52:12:     assertCycleIntegralEqualsSumSmallPositions      precond. (call smallValueInCycle(cycleIntegral.cycle... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:52:12:     assertCycleIntegralEqualsSumSmallPositions      precond. (call smallValueInCycle(cycleIntegral.cycle... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:52:12:     assertCycleIntegralEqualsSumSmallPositions      precond. (call smallValueInCycle(cycleIntegral.cycle... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:53:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:53:12:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:53:45:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:54:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:54:26:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:54:26:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:54:81:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:56:16:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:56:16:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:58:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:58:23:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:60:28:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:61:24:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:63:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:64:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:65:5:      assertCycleIntegralEqualsSumSmallPositions      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:65:12:     assertCycleIntegralEqualsSumSmallPositions      precond. (call assertNextPosition(cycleIntegral, pos...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:66:5:      assertCycleIntegralEqualsSumSmallPositions      precond. (call equality[BigInt](apply(cycleIntegral,... (require 1/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:66:5:      assertCycleIntegralEqualsSumSmallPositions      precond. (call equality[BigInt](apply(cycleIntegral,... (require 2/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:66:5:      assertCycleIntegralEqualsSumSmallPositions      precond. (call equality[BigInt](apply(cycleIntegral,... (require 3/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:66:5:      assertCycleIntegralEqualsSumSmallPositions      precond. (call equality[BigInt](apply(cycleIntegral,... (require 4/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:66:5:      assertCycleIntegralEqualsSumSmallPositions      precond. (call equality[BigInt](apply(cycleIntegral,... (require 5/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:66:5:      assertCycleIntegralEqualsSumSmallPositions      precond. (call equality[BigInt](apply(cycleIntegral,... (require 6/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:67:7:      assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:68:7:      assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:68:39:     assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:69:7:      assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:70:7:      assertCycleIntegralEqualsSumSmallPositions      precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:73:21:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:73:21:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:76:5:      assertCycleIntegralEqualsSumSmallPositions      postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:76:19:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:76:19:     assertCycleIntegralEqualsSumSmallPositions      precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:77:7:      assertCycleIntegralEqualsSumSmallPositions      precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:105:5:                          assertCycleIntegralMatchCycleAccDef             precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 1/6))  valid from cache            3.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:105:5:                          assertCycleIntegralMatchCycleAccDef             precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 2/6))  valid             U:smt-z3  0.4 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:105:5:                          assertCycleIntegralMatchCycleAccDef             precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 3/6))  valid             U:smt-z3  0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:105:5:                          assertCycleIntegralMatchCycleAccDef             precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 4/6))  valid             U:smt-z3  0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:105:5:                          assertCycleIntegralMatchCycleAccDef             precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 5/6))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:105:5:                          assertCycleIntegralMatchCycleAccDef             precond. (call assertCycleAccEqualsCycleIntegral(cyc... (require 6/6))  valid             U:smt-z3  0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:112:12:                         assertCycleIntegralMatchCycleAccDef             body assertion                                                          valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:112:12:                         assertCycleIntegralMatchCycleAccDef             precond. (call apply(cycleAcc, position))                               valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:112:34:                         assertCycleIntegralMatchCycleAccDef             precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:114:7:                          assertCycleIntegralMatchCycleAccDef             body assertion                                                          valid             U:smt-z3  0.2 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:114:7:                          assertCycleIntegralMatchCycleAccDef             precond. (call apply(cycleAcc, position))                               valid             U:smt-z3  0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:114:29:                         assertCycleIntegralMatchCycleAccDef             precond. (call div(position, size))                                     valid             U:smt-z3  0.2 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:114:51:                         assertCycleIntegralMatchCycleAccDef             precond. (call last(integralValues(cycleAcc)))                          valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:115:7:                          assertCycleIntegralMatchCycleAccDef             precond. (call apply(integralValues(cycleAcc), mod(p... (require 1/3))  valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:115:7:                          assertCycleIntegralMatchCycleAccDef             precond. (call apply(integralValues(cycleAcc), mod(p... (require 2/3))  valid             U:smt-z3  0.2 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:115:7:                          assertCycleIntegralMatchCycleAccDef             precond. (call apply(integralValues(cycleAcc), mod(p... (require 3/3))  valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:115:31:                         assertCycleIntegralMatchCycleAccDef             precond. (call mod(position, size))                                     valid             U:smt-z3  0.2 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:118:5:                          assertCycleIntegralMatchCycleAccDef             postcondition                                                           valid             U:smt-z3  0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:118:5:                          assertCycleIntegralMatchCycleAccDef             precond. (call apply(cycleIntegral, position))                          valid             U:smt-z3  0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:119:7:                          assertCycleIntegralMatchCycleAccDef             precond. (call div(position, size))                                     valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:119:29:                         assertCycleIntegralMatchCycleAccDef             precond. (call last(integralValues(cycleAcc)))                          valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:120:9:                          assertCycleIntegralMatchCycleAccDef             precond. (call apply(integralValues(cycleAcc), mod(p... (require 1/3))  valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:120:9:                          assertCycleIntegralMatchCycleAccDef             precond. (call apply(integralValues(cycleAcc), mod(p... (require 2/3))  valid             U:smt-z3  0.2 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:120:9:                          assertCycleIntegralMatchCycleAccDef             precond. (call apply(integralValues(cycleAcc), mod(p... (require 3/3))  valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:120:33:                         assertCycleIntegralMatchCycleAccDef             precond. (call mod(position, size))                                     valid             U:smt-z3  0.1 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAccProperties.scala:120:37:                         assertCycleIntegralMatchCycleAccDef             non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:116:5:                      assertCycleOfPosEqualsCycleOfModPos             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:116:12:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call apply(cycle, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:116:31:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call apply(cycle, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:117:5:                      assertCycleOfPosEqualsCycleOfModPos             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:117:12:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call apply(cycle, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:117:31:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call apply[BigInt](cycle.values, mod(posit...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:117:44:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:119:5:                      assertCycleOfPosEqualsCycleOfModPos             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:119:12:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call modIdempotence(position, size))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:120:5:                      assertCycleOfPosEqualsCycleOfModPos             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:120:12:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call mod(mod(position, size), size))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:120:21:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:120:55:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:121:5:                      assertCycleOfPosEqualsCycleOfModPos             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:121:5:                      assertCycleOfPosEqualsCycleOfModPos             postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:121:12:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call apply(cycle, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:121:31:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call apply(cycle, mod(position, size)))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:121:37:                     assertCycleOfPosEqualsCycleOfModPos             precond. (call mod(position, size))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:123:5:     assertDiffEqualsCycleValue                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:123:12:    assertDiffEqualsCycleValue                      precond. (call apply(cycleIntegral, position + BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:123:43:    assertDiffEqualsCycleValue                      precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:123:69:    assertDiffEqualsCycleValue                      precond. (call apply(cycleIntegral.cycle, position +...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:124:5:     assertDiffEqualsCycleValue                      postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:124:5:     assertDiffEqualsCycleValue                      precond. (call apply(cycleIntegral, position + BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:124:35:    assertDiffEqualsCycleValue                      precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:124:62:    assertDiffEqualsCycleValue                      precond. (call apply(cycleIntegral.cycle, position +...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:298:24:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call getModValuesAsList(cycleIntegral, pos...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:299:23:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:299:23:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:302:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:302:63:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:303:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:303:63:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:306:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call smallValueInCycle(cycleIntegral.cycle... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:306:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call smallValueInCycle(cycleIntegral.cycle... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:306:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call smallValueInCycle(cycleIntegral.cycle... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:307:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:307:14:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:307:54:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:309:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:309:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call assertFirstValuesAsSliceEqualsModValu... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:309:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call assertFirstValuesAsSliceEqualsModValu... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:310:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:310:14:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call assertAppendToSlice(cycleIntegral.cyc... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:310:14:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call assertAppendToSlice(cycleIntegral.cyc... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:310:14:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call assertAppendToSlice(cycleIntegral.cyc... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:312:30:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call getModValuesAsList(cycleIntegral, pos...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:313:30:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:313:30:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:315:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:315:55:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:316:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:316:55:    assertFirstValuesAsSliceEqualsModValuesAsListt  precond. (call apply[BigInt](cycleIntegral.cycle.val...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:316:82:    assertFirstValuesAsSliceEqualsModValuesAsListt  non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:318:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:319:7:     assertFirstValuesAsSliceEqualsModValuesAsListt  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:321:5:     assertFirstValuesAsSliceEqualsModValuesAsListt  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:45:5:                                     assertFirstValuesMatchIntegral                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:45:12:                                    assertFirstValuesMatchIntegral                  precond. (call modSmallDividend(position, size(integ... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:45:12:                                    assertFirstValuesMatchIntegral                  precond. (call modSmallDividend(position, size(integ... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:45:12:                                    assertFirstValuesMatchIntegral                  precond. (call modSmallDividend(position, size(integ... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:46:5:                                     assertFirstValuesMatchIntegral                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:46:12:                                    assertFirstValuesMatchIntegral                  precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:47:5:                                     assertFirstValuesMatchIntegral                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:47:12:                                    assertFirstValuesMatchIntegral                  precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:49:5:                                     assertFirstValuesMatchIntegral                  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:49:5:                                     assertFirstValuesMatchIntegral                  precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:49:24:                                    assertFirstValuesMatchIntegral                  precond. (call apply(integralValues(thiss), position) (require 1/3))    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:49:24:                                    assertFirstValuesMatchIntegral                  precond. (call apply(integralValues(thiss), position) (require 2/3))    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:49:24:                                    assertFirstValuesMatchIntegral                  precond. (call apply(integralValues(thiss), position) (require 3/3))    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:224:5:     assertIntegralCycleEqualsSumOfModlValuesAsList  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:224:12:    assertIntegralCycleEqualsSumOfModlValuesAsList  precond. (call assertSumModValueAsListEqualsIntegral...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:225:25:    assertIntegralCycleEqualsSumOfModlValuesAsList  precond. (call getModValuesAsList(iCycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:226:5:     assertIntegralCycleEqualsSumOfModlValuesAsList  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:226:5:     assertIntegralCycleEqualsSumOfModlValuesAsList  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:249:5:                                assertLast                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:250:9:                                assertLast                                      precond. (call last(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:251:9:                                assertLast                                      precond. (call last[BigInt](acc(thiss)))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:253:5:                                assertLast                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:253:12:                               assertLast                                      precond. (call assertLastEqualsLastPosition[BigInt](...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:254:5:                                assertLast                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:255:5:                                assertLast                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:256:7:                                assertLast                                      precond. (call last[BigInt](acc(thiss)))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:257:7:                                assertLast                                      precond. (call apply[BigInt](acc(thiss), size[BigInt...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:259:5:                                assertLast                                      precond. (call assertAccMatchesApply(thiss, size(thi... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:259:5:                                assertLast                                      precond. (call assertAccMatchesApply(thiss, size(thi... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:260:5:                                assertLast                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:261:7:                                assertLast                                      precond. (call apply[BigInt](acc(thiss), size(thiss)...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:262:7:                                assertLast                                      precond. (call apply(thiss, size(thiss) - BigInt("1")) (require 1/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:262:7:                                assertLast                                      precond. (call apply(thiss, size(thiss) - BigInt("1")) (require 2/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:262:7:                                assertLast                                      precond. (call apply(thiss, size(thiss) - BigInt("1")) (require 3/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:264:5:                                assertLast                                      postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:264:5:                                assertLast                                      precond. (call apply(thiss, size(thiss) - BigInt("1")) (require 1/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:264:5:                                assertLast                                      precond. (call apply(thiss, size(thiss) - BigInt("1")) (require 2/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:264:5:                                assertLast                                      precond. (call apply(thiss, size(thiss) - BigInt("1")) (require 3/3))   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:264:24:                               assertLast                                      precond. (call last(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:164:5:     assertLastElementBeforeLoop                     precond. (call assertCycleIntegralEqualsSliceSum(iCy... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:164:5:     assertLastElementBeforeLoop                     precond. (call assertCycleIntegralEqualsSliceSum(iCy... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:165:5:     assertLastElementBeforeLoop                     postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:165:5:     assertLastElementBeforeLoop                     precond. (call apply(iCycle, size(iCycle) - BigInt(...)                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:165:46:    assertLastElementBeforeLoop                     precond. (call getFirstValuesAsSlice(iCycle, size(iC... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:165:46:    assertLastElementBeforeLoop                     precond. (call getFirstValuesAsSlice(iCycle, size(iC... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:93:15:                   assertLastEqualsLastPosition                    non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:96:7:                    assertLastEqualsLastPosition                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:96:14:                   assertLastEqualsLastPosition                    precond. (call head[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:96:27:                   assertLastEqualsLastPosition                    precond. (call last[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:98:7:                    assertLastEqualsLastPosition                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:98:14:                   assertLastEqualsLastPosition                    measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:98:14:                   assertLastEqualsLastPosition                    precond. (call assertLastEqualsLastPosition[T](tail[...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:98:43:                   assertLastEqualsLastPosition                    precond. (call tail[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:99:7:                    assertLastEqualsLastPosition                    precond. (call assertTailShiftPosition[T](list, size... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:99:7:                    assertLastEqualsLastPosition                    precond. (call assertTailShiftPosition[T](list, size... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:100:7:                   assertLastEqualsLastPosition                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:100:14:                  assertLastEqualsLastPosition                    precond. (call last[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:100:27:                  assertLastEqualsLastPosition                    precond. (call apply[T](list, size[T](list) - BigInt...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:102:5:                   assertLastEqualsLastPosition                    postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:102:5:                   assertLastEqualsLastPosition                    precond. (call last[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:102:18:                  assertLastEqualsLastPosition                    precond. (call apply[T](list, size[T](list) - BigInt...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:224:15:                               assertLastEqualsSum                             non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:227:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:227:14:                               assertLastEqualsSum                             precond. (call last(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:227:22:                               assertLastEqualsSum                             precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:228:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:228:14:                               assertLastEqualsSum                             precond. (call last(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:230:27:                               assertLastEqualsSum                             precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:230:38:                               assertLastEqualsSum                             precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:231:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:231:14:                               assertLastEqualsSum                             measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:231:14:                               assertLastEqualsSum                             precond. (call assertLastEqualsSum(next))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:232:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:232:14:                               assertLastEqualsSum                             precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:233:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:233:14:                               assertLastEqualsSum                             precond. (call last[BigInt](tail(thiss)))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:233:14:                               assertLastEqualsSum                             precond. (call tail(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:233:32:                               assertLastEqualsSum                             precond. (call last[BigInt](acc(next)))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:234:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:234:14:                               assertLastEqualsSum                             precond. (call last(next))                                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:234:27:                               assertLastEqualsSum                             precond. (call last[BigInt](acc(next)))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:235:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:235:14:                               assertLastEqualsSum                             precond. (call last(next))                                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:235:27:                               assertLastEqualsSum                             precond. (call last(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:236:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:236:14:                               assertLastEqualsSum                             precond. (call last(next))                                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:237:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:237:14:                               assertLastEqualsSum                             precond. (call last(next))                                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:237:34:                               assertLastEqualsSum                             precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:238:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:238:14:                               assertLastEqualsSum                             precond. (call last(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:238:34:                               assertLastEqualsSum                             precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:239:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:239:60:                               assertLastEqualsSum                             precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:240:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:240:14:                               assertLastEqualsSum                             precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:240:73:                               assertLastEqualsSum                             precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:240:87:                               assertLastEqualsSum                             precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:241:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:241:14:                               assertLastEqualsSum                             precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:242:7:                                assertLastEqualsSum                             body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:242:14:                               assertLastEqualsSum                             precond. (call last(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:244:5:                                assertLastEqualsSum                             postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:244:5:                                assertLastEqualsSum                             precond. (call last(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:105:7:     assertNextPosition                              postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:107:5:     assertNextPosition                              precond. (call apply(cycleIntegral, position))                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:107:32:    assertNextPosition                              precond. (call apply(cycleIntegral, position - BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:107:62:    assertNextPosition                              precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:148:5:     assertSameDiffAfterCycle                        precond. (call assertDiffEqualsCycleValue(iCycle, a))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:149:5:     assertSameDiffAfterCycle                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:149:12:    assertSameDiffAfterCycle                        precond. (call apply(iCycle, b))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:149:24:    assertSameDiffAfterCycle                        precond. (call apply(iCycle, a))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:149:37:    assertSameDiffAfterCycle                        precond. (call apply(iCycle.cycle, b))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:151:5:     assertSameDiffAfterCycle                        precond. (call assertDiffEqualsCycleValue(iCycle, c))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:152:5:     assertSameDiffAfterCycle                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:152:12:    assertSameDiffAfterCycle                        precond. (call apply(iCycle, d))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:152:24:    assertSameDiffAfterCycle                        precond. (call apply(iCycle, c))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:152:37:    assertSameDiffAfterCycle                        precond. (call apply(iCycle.cycle, d))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:154:5:     assertSameDiffAfterCycle                        precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 1/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:154:5:     assertSameDiffAfterCycle                        precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 2/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:154:5:     assertSameDiffAfterCycle                        precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 3/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:154:5:     assertSameDiffAfterCycle                        precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 4/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:155:5:     assertSameDiffAfterCycle                        precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 1/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:155:5:     assertSameDiffAfterCycle                        precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 2/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:155:5:     assertSameDiffAfterCycle                        precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 3/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:155:5:     assertSameDiffAfterCycle                        precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 4/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:157:5:     assertSameDiffAfterCycle                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:157:12:    assertSameDiffAfterCycle                        precond. (call apply(iCycle.cycle, d))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:157:31:    assertSameDiffAfterCycle                        precond. (call apply(iCycle.cycle, b))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:158:5:     assertSameDiffAfterCycle                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:158:12:    assertSameDiffAfterCycle                        precond. (call apply(iCycle.cycle, c))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:158:31:    assertSameDiffAfterCycle                        precond. (call apply(iCycle.cycle, a))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:160:5:     assertSameDiffAfterCycle                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:160:5:     assertSameDiffAfterCycle                        precond. (call apply(iCycle, b))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:160:17:    assertSameDiffAfterCycle                        precond. (call apply(iCycle, a))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:160:30:    assertSameDiffAfterCycle                        precond. (call apply(iCycle, d))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:160:42:    assertSameDiffAfterCycle                        precond. (call apply(iCycle, c))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:68:5:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:69:5:                                     assertSimplifiedDiffValuesMatchCycle            precond. (call addOne(position, size(integralValues(... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:69:5:                                     assertSimplifiedDiffValuesMatchCycle            precond. (call addOne(position, size(integralValues(... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:71:9:                                     assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:75:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:75:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call assertLastEqualsLastPosition[BigInt](...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:76:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:76:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call assertAccMatchesApply(integralValues(... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:76:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call assertAccMatchesApply(integralValues(... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:77:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:77:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call assertLastEqualsSum(integralValues(th...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:78:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:79:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:79:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call last[BigInt](acc(integralValues(thiss))))                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:79:41:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:80:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:80:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:80:37:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply[BigInt](acc(integralValues(this...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:81:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:81:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:81:37:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:81:37:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:81:37:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:85:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:85:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:86:7:                                     assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:86:14:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call div(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:86:61:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:90:7:                                     assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:90:7:                                     assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:91:9:                                     assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:92:9:                                     assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:92:51:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:93:11:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:93:11:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:93:11:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:93:26:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:95:9:                                     assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:95:51:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:96:11:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:96:11:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:96:11:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:100:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:100:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call assertAccMatchesApply(integralValues(... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:100:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call assertAccMatchesApply(integralValues(... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:101:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:101:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call assertLastEqualsSum(integralValues(th...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:102:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:104:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:104:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:104:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:104:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:104:63:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply[BigInt](acc(integralValues(this...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:105:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:105:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply[BigInt](acc(integralValues(this...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:105:65:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last[BigInt](acc(integralValues(thiss))))                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:109:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:109:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:110:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call div(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:110:55:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:111:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:111:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:111:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:111:26:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:117:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:117:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:118:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:120:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:120:51:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:121:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:121:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:121:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:125:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:125:51:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:126:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:132:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 1/7))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:132:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 2/7))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:132:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 3/7))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:132:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 4/7))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:132:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 5/7))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:132:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 6/7))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:132:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 7/7))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:133:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:133:31:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:136:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:136:59:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:137:17:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:137:17:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:137:17:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:137:32:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:141:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:141:55:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:142:17:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:142:17:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:142:17:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:146:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:146:61:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:147:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:147:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:147:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:147:28:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:149:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:149:55:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:150:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:150:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:150:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:153:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:153:55:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:154:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:155:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:155:55:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:156:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:156:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:156:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:156:28:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:157:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:157:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:157:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:162:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:163:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:163:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:163:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:163:28:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:164:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:164:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:164:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), size(int... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:165:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), BigInt(...  (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:165:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), BigInt(...  (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:165:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), BigInt(...  (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:166:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:167:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:169:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), BigInt(...  (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:169:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), BigInt(...  (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:169:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), BigInt(...  (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:171:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call head[BigInt](thiss.cycle.values))                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:174:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:175:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:175:31:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:175:50:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call head[BigInt](thiss.cycle.values))                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:183:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:183:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:183:61:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:184:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:184:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:184:61:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:188:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:188:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:189:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:189:51:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:190:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:190:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:190:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:190:26:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:196:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:196:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:197:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call div(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:197:55:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:198:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:198:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:198:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:198:26:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:201:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:201:14:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:202:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:202:51:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:203:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:203:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:203:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:203:26:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:209:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:209:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:209:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call equality[BigInt](apply(thiss, positio... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:210:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:210:31:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:213:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:213:53:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:214:15:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:214:15:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:214:15:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:214:30:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:218:11:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:218:53:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:219:15:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:219:15:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:219:15:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:219:30:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:223:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:223:55:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:224:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:224:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:224:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:224:28:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:226:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call div(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:226:55:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call last(integralValues(thiss)))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:227:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:227:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:227:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:227:28:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:230:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:230:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:230:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:230:28:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:231:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:231:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:231:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), mod(posi... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:231:28:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:236:15:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:237:15:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position, size(integralValues(thi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:238:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:240:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:241:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:241:31:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:242:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), b) (require 1/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:242:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), b) (require 2/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:242:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), b) (require 3/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:243:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), a) (require 1/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:243:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), a) (require 2/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:243:13:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), a) (require 3/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:246:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call assertAccDiffMatchesList(integralValu... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:246:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call assertAccDiffMatchesList(integralValu... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:247:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:248:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), b) (require 1/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:248:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), b) (require 2/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:248:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), b) (require 3/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:248:29:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), a) (require 1/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:248:29:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), a) (require 2/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:248:29:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(integralValues(thiss), a) (require 3/3))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:248:50:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply[BigInt](thiss.cycle.values, b))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:250:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:251:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:251:31:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:251:50:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply[BigInt](thiss.cycle.values, b))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:253:7:                                    assertSimplifiedDiffValuesMatchCycle            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:254:9:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:254:31:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:254:50:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply[BigInt](thiss.cycle.values, mod...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:254:63:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:258:5:                                    assertSimplifiedDiffValuesMatchCycle            postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:258:5:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position + BigInt("1")))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:258:27:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call apply(thiss, position))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:259:7:                                    assertSimplifiedDiffValuesMatchCycle            precond. (call apply[BigInt](thiss.cycle.values, mod...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/acc/CycleAcc.scala:259:20:                                   assertSimplifiedDiffValuesMatchCycle            precond. (call mod(position + BigInt("1"), size(inte...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:194:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:195:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:198:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:199:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:200:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:202:27:                               assertSizeAccEqualsSizeList                     precond. (call tail[BigInt](list))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:202:38:                               assertSizeAccEqualsSizeList                     precond. (call head(current))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:204:7:                                assertSizeAccEqualsSizeList                     measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:205:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:206:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:206:34:                               assertSizeAccEqualsSizeList                     precond. (call head(current))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:207:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:208:7:                                assertSizeAccEqualsSizeList                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:208:18:                               assertSizeAccEqualsSizeList                     precond. (call tail[BigInt](list))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:208:36:                               assertSizeAccEqualsSizeList                     non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:210:5:                                assertSizeAccEqualsSizeList                     postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:189:7:     assertSumModValueAsListEqualsIntegralCycleLoop  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:189:14:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:189:48:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call getModValuesAsList(iCycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:190:7:     assertSumModValueAsListEqualsIntegralCycleLoop  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:190:7:     assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:190:27:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle.cycle, BigInt("0")))                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:191:9:     assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:191:43:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call getModValuesAsList(iCycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:194:9:     assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call assertSameDiffAfterCycle(iCycle, posi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:195:9:     assertSumModValueAsListEqualsIntegralCycleLoop  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:195:16:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position - size(iCycle)))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:195:49:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, (position - size(iCycle...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:195:87:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:195:106:   assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position - BigInt("1")))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:196:9:     assertSumModValueAsListEqualsIntegralCycleLoop  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:196:16:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position - BigInt("1")))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:196:39:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position - size(iCycle)))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:196:72:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, (position - size(iCycle...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:196:110:   assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:197:9:     assertSumModValueAsListEqualsIntegralCycleLoop  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:197:16:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position - BigInt("1")))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:197:39:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle.cycle, position - size(i...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:197:79:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:198:9:     assertSumModValueAsListEqualsIntegralCycleLoop  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:198:16:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 1/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:198:16:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 2/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:198:16:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 3/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:198:16:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call valueMatchAfterManyLoopsInBoth(iCycle... (require 4/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:200:7:     assertSumModValueAsListEqualsIntegralCycleLoop  measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:200:7:     assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call assertSumModValueAsListEqualsIntegral...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:201:7:     assertSumModValueAsListEqualsIntegralCycleLoop  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:201:14:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position - BigInt("1")))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:201:52:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call getModValuesAsList(iCycle, position -...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:202:7:     assertSumModValueAsListEqualsIntegralCycleLoop  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:202:51:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call getModValuesAsList(iCycle, position -...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:202:93:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle.cycle, position))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:203:7:     assertSumModValueAsListEqualsIntegralCycleLoop  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:203:7:     assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:203:27:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle.cycle, position))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:203:52:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position - BigInt("1")))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:204:9:     assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call apply(iCycle, position))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:204:43:    assertSumModValueAsListEqualsIntegralCycleLoop  precond. (call getModValuesAsList(iCycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:204:70:    assertSumModValueAsListEqualsIntegralCycleLoop  non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:76:7:                    assertTailShiftPosition                         postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:76:7:                    assertTailShiftPosition                         precond. (call apply[T](list, position))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:76:25:                   assertTailShiftPosition                         precond. (call head[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:78:7:                    assertTailShiftPosition                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:78:28:                   assertTailShiftPosition                         precond. (call head[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:78:42:                   assertTailShiftPosition                         precond. (call tail[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:79:7:                    assertTailShiftPosition                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:79:15:                   assertTailShiftPosition                         precond. (call apply[T](list, position))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:79:33:                   assertTailShiftPosition                         precond. (call apply[T](list, position))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:80:7:                    assertTailShiftPosition                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:80:14:                   assertTailShiftPosition                         measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:80:14:                   assertTailShiftPosition                         precond. (call assertTailShiftPosition[T](tail[T](li... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:80:14:                   assertTailShiftPosition                         precond. (call assertTailShiftPosition[T](tail[T](li... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:80:38:                   assertTailShiftPosition                         precond. (call tail[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:81:7:                    assertTailShiftPosition                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:81:14:                   assertTailShiftPosition                         precond. (call apply[T](list, position))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:81:38:                   assertTailShiftPosition                         precond. (call apply[T](tail[T](list), position - Bi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:81:38:                   assertTailShiftPosition                         precond. (call tail[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:82:7:                    assertTailShiftPosition                         postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:82:7:                    assertTailShiftPosition                         precond. (call apply[T](list, position))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:82:25:                   assertTailShiftPosition                         precond. (call apply[T](tail[T](list), position - Bi...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:82:25:                   assertTailShiftPosition                         precond. (call tail[T](list))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:82:35:                   assertTailShiftPosition                         non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:26:7:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a, b) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:26:7:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a, b) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:26:7:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a, b) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:28:7:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a, b) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:28:7:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a, b) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:28:7:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a, b) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:29:9:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a - BigInt("1"), b) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:29:9:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a - BigInt("1"), b) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:29:9:                                  checkAllPreviousValues                          precond. (call modSmallDividend(a - BigInt("1"), b) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:31:5:                                  checkAllPreviousValues                          postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:31:5:                                  checkAllPreviousValues                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:31:22:                                 checkAllPreviousValues                          non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:55:5:                                            checkMod                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:60:26:                                           checkMod                                        precond. (call countModZero(thiss.values, dividend) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:60:26:                                           checkMod                                        precond. (call countModZero(thiss.values, dividend) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:60:26:                                           checkMod                                        precond. (call countModZero(thiss.values, dividend) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:63:9:                                            checkMod                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:63:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:63:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:63:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:64:9:                                            checkMod                                        precond. (call appendForAll(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:64:9:                                            checkMod                                        precond. (call appendForAll(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:64:9:                                            checkMod                                        precond. (call appendForAll(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:67:9:                                            checkMod                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:67:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:67:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:67:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:68:9:                                            checkMod                                        precond. (call appendForNone(thiss, dividend) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:68:9:                                            checkMod                                        precond. (call appendForNone(thiss, dividend) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:68:9:                                            checkMod                                        precond. (call appendForNone(thiss, dividend) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:71:9:                                            checkMod                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:71:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:71:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:71:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:72:9:                                            checkMod                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:72:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:72:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:72:16:                                           checkMod                                        precond. (call countModZero(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:73:9:                                            checkMod                                        precond. (call appendForSome(thiss, dividend) (require 1/4))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:73:9:                                            checkMod                                        precond. (call appendForSome(thiss, dividend) (require 2/4))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:73:9:                                            checkMod                                        precond. (call appendForSome(thiss, dividend) (require 3/4))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:73:9:                                            checkMod                                        precond. (call appendForSome(thiss, dividend) (require 4/4))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:71:7:                                  checkValueShift                                 precond. (call modSmallDividend(a, b) (require 1/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:71:7:                                  checkValueShift                                 precond. (call modSmallDividend(a, b) (require 2/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:71:7:                                  checkValueShift                                 precond. (call modSmallDividend(a, b) (require 3/3))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:72:7:                                  checkValueShift                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:72:7:                                  checkValueShift                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:74:7:                                  checkValueShift                                 precond. (call modLess(a, b, b))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:75:7:                                  checkValueShift                                 precond. (call equality[BigInt](mod(a - b, b), mod(m... (require 1/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:75:7:                                  checkValueShift                                 precond. (call equality[BigInt](mod(a - b, b), mod(m... (require 2/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:75:7:                                  checkValueShift                                 precond. (call equality[BigInt](mod(a - b, b), mod(m... (require 3/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:75:7:                                  checkValueShift                                 precond. (call equality[BigInt](mod(a - b, b), mod(m... (require 4/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:76:9:                                  checkValueShift                                 precond. (call mod(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:77:9:                                  checkValueShift                                 precond. (call mod(mod(a, b) - mod(b, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:77:13:                                 checkValueShift                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:77:25:                                 checkValueShift                                 precond. (call mod(b, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:78:9:                                  checkValueShift                                 precond. (call mod(mod(a, b) - BigInt("0"), b))                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:78:13:                                 checkValueShift                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:79:9:                                  checkValueShift                                 precond. (call mod(mod(a, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:79:13:                                 checkValueShift                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:80:9:                                  checkValueShift                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:82:7:                                  checkValueShift                                 body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:82:14:                                 checkValueShift                                 precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:82:26:                                 checkValueShift                                 precond. (call mod(a - b, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:83:7:                                  checkValueShift                                 measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:83:7:                                  checkValueShift                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:83:7:                                  checkValueShift                                 precond. (call checkValueShift(a - b, b) (require 1/2))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:83:7:                                  checkValueShift                                 precond. (call checkValueShift(a - b, b) (require 2/2))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:83:23:                                 checkValueShift                                 non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:184:5:                                           checkZeroForAll                                 precond. (call loop(values, modIsZeroForAllValues) (require 2/2))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:259:5:                                           checkZeroForNone                                precond. (call loop(values, modIsZeroForNoneValues) (require 2/2))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:162:5:                                           checkZeroForSome                                precond. (call loop(values, modIsZeroForSomeValues))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:115:18:                         compareTwoSeqLoop                               precond. (call apply(seq.loop, loopPosition))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:116:14:                         compareTwoSeqLoop                               measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:116:14:                         compareTwoSeqLoop                               precond. (call compareTwoSeqLoop(from, to - BigInt(...  (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:116:14:                         compareTwoSeqLoop                               precond. (call compareTwoSeqLoop(from, to - BigInt(...  (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:116:38:                         compareTwoSeqLoop                               non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:96:7:                           compareTwoSeqPos                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:96:14:                          compareTwoSeqPos                                precond. (call prevValuesMatchLoop(seq, to) (require 1/2))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:96:14:                          compareTwoSeqPos                                precond. (call prevValuesMatchLoop(seq, to) (require 2/2))              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:98:7:                           compareTwoSeqPos                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:98:14:                          compareTwoSeqPos                                precond. (call apply(seq, to - BigInt("1")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:98:29:                          compareTwoSeqPos                                precond. (call apply(seq, to))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:98:39:                          compareTwoSeqPos                                precond. (call apply(seq.loop, loopPosition))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:99:18:                          compareTwoSeqPos                                precond. (call apply(seq.loop, loopPosition))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:100:7:                          compareTwoSeqPos                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:100:14:                         compareTwoSeqPos                                precond. (call apply(seq, to - BigInt("1")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:100:29:                         compareTwoSeqPos                                precond. (call apply(seq, to))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:101:7:                          compareTwoSeqPos                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:101:14:                         compareTwoSeqPos                                precond. (call apply(seq, to - BigInt("1")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:101:36:                         compareTwoSeqPos                                precond. (call apply(seq, to))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:102:7:                          compareTwoSeqPos                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:102:22:                         compareTwoSeqPos                                precond. (call apply(seq, to))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:102:32:                         compareTwoSeqPos                                precond. (call apply(seq, to - BigInt("1")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:103:7:                          compareTwoSeqPos                                precond. (call apply(seq, to))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:103:17:                         compareTwoSeqPos                                precond. (call apply(seq, to - BigInt("1")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:103:31:                         compareTwoSeqPos                                measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:103:31:                         compareTwoSeqPos                                precond. (call compareTwoSeqPos(from, to - BigInt(...   (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:103:31:                         compareTwoSeqPos                                precond. (call compareTwoSeqPos(from, to - BigInt(...   (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:103:54:                         compareTwoSeqPos                                non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:16:17:                                      convert                                         non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:21:9:                                       convert                                         measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:21:9:                                       convert                                         precond. (call convert(values, {   assert(((index & ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:21:9:                                       convert                                         precond. (call convert(values, {   assert(((index & ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:22:11:                                      convert                                         body assertion: Subtraction overflow                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:23:31:                                      convert                                         array index within bounds                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:23:31:                                      convert                                         body assertion: Subtraction overflow                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:38:5:                                            countModZero                                    precond. (call countModZero(thiss.values, dividend) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:38:5:                                            countModZero                                    precond. (call countModZero(thiss.values, dividend) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:38:5:                                            countModZero                                    precond. (call countModZero(thiss.values, dividend) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:28:5:                                       createList                                      precond. (call convert(values, values.length, Nil[Bi... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListBuilder.scala:28:5:                                       createList                                      precond. (call convert(values, values.length, Nil[Bi... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/Calc.scala:11:18:                                                  div                                             class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:94:5:                                       equality                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:94:5:                                       equality                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:36:5:                                       equality                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:36:5:                                       equality                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:78:5:                                       equality                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:78:5:                                       equality                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:49:5:                                       equality                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:49:5:                                       equality                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:63:5:                                       equality                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:63:5:                                       equality                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:129:5:                                      equality                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:129:5:                                      equality                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:111:5:                                      equality                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:111:5:                                      equality                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:25:5:                                       equality                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/verification/Helper.scala:26:5:                                       equality                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:78:18:                                            equals                                          precond. (call get[DivMod](InstanceOf[Object, DivMod...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:78:18:                                            equals                                          precond. (call get[DivMod](InstanceOf[Object, DivMod...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:78:18:                                            equals                                          precond. (call get[DivMod](InstanceOf[Object, DivMod...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:78:18:                                            equals                                          precond. (call get[DivMod](InstanceOf[Object, DivMod...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:78:18:                                            equals                                          precond. (call get[DivMod](InstanceOf[Object, DivMod...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:28:21:                        evaluatedInSomeList                             precond. (call checkMod(cycle, dividend))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:30:5:                         evaluatedInSomeList                             postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:21:7:                       findValueInCycle                                postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:24:5:                       findValueInCycle                                precond. (call apply(cycle, key))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:24:19:                      findValueInCycle                                precond. (call apply[BigInt](cycle.values, mod(key, ...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:24:32:                      findValueInCycle                                precond. (call mod(key, size(cycle)))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:19:7:                           firstValuesMatchFirstPosInLoop                  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:19:7:                           firstValuesMatchFirstPosInLoop                  precond. (call apply(seq, pos))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:19:19:                          firstValuesMatchFirstPosInLoop                  precond. (call apply(seq.loop, BigInt("0")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:21:7:                           firstValuesMatchFirstPosInLoop                  postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:21:7:                           firstValuesMatchFirstPosInLoop                  precond. (call apply(seq, pos))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:21:19:                          firstValuesMatchFirstPosInLoop                  precond. (call apply[BigInt](seq.previous, size[BigI...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:21:57:                          firstValuesMatchFirstPosInLoop                  precond. (call apply(seq.loop, BigInt("0")))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:10:7:                           firstValuesMatchPrev                            postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:13:5:                           firstValuesMatchPrev                            precond. (call apply[BigInt](seq.previous, pos))                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:13:26:                          firstValuesMatchPrev                            precond. (call apply(seq, pos))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:11:20:                        forAnyCheckModValuesRemains                     precond. (call checkMod(cycle, dividend))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:12:5:                         forAnyCheckModValuesRemains                     postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:236:7:     getFirstValuesAsSlice                           precond. (call slice(cycleIntegral.cycle.values, Big... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:236:7:     getFirstValuesAsSlice                           precond. (call slice(cycleIntegral.cycle.values, Big... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:236:7:     getFirstValuesAsSlice                           precond. (call slice(cycleIntegral.cycle.values, Big... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:240:7:     getFirstValuesAsSlice                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:240:14:    getFirstValuesAsSlice                           precond. (call assertAppendToSlice(list, BigInt("0")... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:240:14:    getFirstValuesAsSlice                           precond. (call assertAppendToSlice(list, BigInt("0")... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:240:14:    getFirstValuesAsSlice                           precond. (call assertAppendToSlice(list, BigInt("0")... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:242:7:     getFirstValuesAsSlice                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:243:9:     getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position) (require 1/3))        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:243:9:     getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position) (require 2/3))        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:243:9:     getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position) (require 3/3))        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:244:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position - B... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:244:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position - B... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:244:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position - B... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:244:58:    getFirstValuesAsSlice                           precond. (call apply[BigInt](list, position))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:247:7:     getFirstValuesAsSlice                           precond. (call equality[List[BigInt]](result, ++[Big... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:247:7:     getFirstValuesAsSlice                           precond. (call equality[List[BigInt]](result, ++[Big... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:247:7:     getFirstValuesAsSlice                           precond. (call equality[List[BigInt]](result, ++[Big... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:250:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position) (require 1/3))        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:250:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position) (require 2/3))        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:250:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position) (require 3/3))        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:252:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position - B... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:252:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position - B... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:252:11:    getFirstValuesAsSlice                           precond. (call slice(list, BigInt("0"), position - B... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:252:58:    getFirstValuesAsSlice                           precond. (call apply[BigInt](list, position))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:253:9:     getFirstValuesAsSlice                           measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:253:9:     getFirstValuesAsSlice                           precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:253:9:     getFirstValuesAsSlice                           precond. (call getFirstValuesAsSlice(cycleIntegral, ... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:253:68:    getFirstValuesAsSlice                           precond. (call apply[BigInt](list, position))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:253:73:    getFirstValuesAsSlice                           non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:272:7:     getModValuesAsList                              precond. (call smallValueInCycle(cycleIntegral.cycle... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:272:7:     getModValuesAsList                              precond. (call smallValueInCycle(cycleIntegral.cycle... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:272:7:     getModValuesAsList                              precond. (call smallValueInCycle(cycleIntegral.cycle... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:276:7:     getModValuesAsList                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:276:56:    getModValuesAsList                              precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:277:48:    getModValuesAsList                              precond. (call apply(cycleIntegral.cycle, BigInt("0")))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:279:18:    getModValuesAsList                              measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:279:18:    getModValuesAsList                              precond. (call getModValuesAsList(cycleIntegral, pos...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:280:7:     getModValuesAsList                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:280:57:    getModValuesAsList                              precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:281:20:    getModValuesAsList                              precond. (call apply(cycleIntegral.cycle, position))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/integral/properties/CycleIntegralProperties.scala:281:40:    getModValuesAsList                              non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:38:5:                                 head                                            precond. (call head[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:58:21:                        ifInAllModAll                                   precond. (call checkMod(cycle, dividend))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:60:7:                         ifInAllModAll                                   postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:60:7:                         ifInAllModAll                                   precond. (call countModZero(evalCycle, dividend) (require 1/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:60:7:                         ifInAllModAll                                   precond. (call countModZero(evalCycle, dividend) (require 2/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:60:7:                         ifInAllModAll                                   precond. (call countModZero(evalCycle, dividend) (require 3/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:62:7:                         ifInAllModAll                                   postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:62:7:                         ifInAllModAll                                   precond. (call countModZero(evalCycle, dividend) (require 1/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:62:7:                         ifInAllModAll                                   precond. (call countModZero(evalCycle, dividend) (require 2/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:62:7:                         ifInAllModAll                                   precond. (call countModZero(evalCycle, dividend) (require 3/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:84:21:                        ifInNoneModNone                                 precond. (call checkMod(cycle, dividend))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:86:7:                         ifInNoneModNone                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:86:7:                         ifInNoneModNone                                 precond. (call countModZero(evalCycle, dividend) (require 1/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:86:7:                         ifInNoneModNone                                 precond. (call countModZero(evalCycle, dividend) (require 2/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:86:7:                         ifInNoneModNone                                 precond. (call countModZero(evalCycle, dividend) (require 3/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:88:7:                         ifInNoneModNone                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:88:7:                         ifInNoneModNone                                 precond. (call countModZero(evalCycle, dividend) (require 1/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:88:7:                         ifInNoneModNone                                 precond. (call countModZero(evalCycle, dividend) (require 2/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:88:7:                         ifInNoneModNone                                 precond. (call countModZero(evalCycle, dividend) (require 3/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:70:21:                        ifInSomeModSome                                 precond. (call checkMod(cycle, dividend))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:72:7:                         ifInSomeModSome                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:72:7:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 1/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:72:7:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 2/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:72:7:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 3/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:73:9:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 1/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:73:9:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 2/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:73:9:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 3/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:75:7:                         ifInSomeModSome                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:75:7:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 1/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:75:7:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 2/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:75:7:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 3/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:76:9:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 1/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:76:9:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 2/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:76:9:                         ifInSomeModSome                                 precond. (call countModZero(evalCycle, dividend) (require 3/3))         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:42:15:                                            increaseMod                                     non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:45:51:                                            increaseMod                                     measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:45:51:                                            increaseMod                                     precond. (call increaseMod(next))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:46:6:                                             increaseMod                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:47:6:                                             increaseMod                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:48:6:                                             increaseMod                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:49:5:                                             increaseMod                                     postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:119:7:                                           isValid                                         precond. (call checkZeroForAll(modIsZeroForAllValues... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:119:7:                                           isValid                                         precond. (call checkZeroForAll(modIsZeroForAllValues... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:119:7:                                           isValid                                         precond. (call checkZeroForAll(modIsZeroForAllValues... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:120:7:                                           isValid                                         precond. (call checkZeroForSome(modIsZeroForSomeValu... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:120:7:                                           isValid                                         precond. (call checkZeroForSome(modIsZeroForSomeValu... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:120:7:                                           isValid                                         precond. (call checkZeroForSome(modIsZeroForSomeValu... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:121:7:                                           isValid                                         precond. (call checkZeroForNone(modIsZeroForNoneValu... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:121:7:                                           isValid                                         precond. (call checkZeroForNone(modIsZeroForNoneValu... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:121:7:                                           isValid                                         precond. (call checkZeroForNone(modIsZeroForNoneValu... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:33:5:                                 last                                            precond. (call last[BigInt](acc(thiss)))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:43:5:                    listAddValueTail                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:44:5:                    listAddValueTail                                postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:15:15:                   listCombine                                     non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:18:7:                    listCombine                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:19:7:                    listCombine                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:20:7:                    listCombine                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:21:7:                    listCombine                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:23:7:                    listCombine                                     measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:23:19:                   listCombine                                     precond. (call tail[BigInt](listA))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:25:7:                    listCombine                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:25:30:                   listCombine                                     precond. (call head[BigInt](listA))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:25:45:                   listCombine                                     precond. (call tail[BigInt](listA))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:26:23:                   listCombine                                     precond. (call tail[BigInt](listA))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:26:44:                   listCombine                                     precond. (call head[BigInt](listA))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:28:5:                    listCombine                                     postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:10:7:                    listSumAddValue                                 postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:34:5:                    listSwap                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:35:5:                    listSwap                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:36:5:                    listSwap                                        body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/properties/ListUtilsProperties.scala:37:5:                    listSwap                                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:17:5:                             longProof                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:17:13:                            longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:20:7:                             longProof                                       precond. (call equality[DivMod](solve(DivMod(n, n, B... (require 1/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:20:7:                             longProof                                       precond. (call equality[DivMod](solve(DivMod(n, n, B... (require 2/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:20:7:                             longProof                                       precond. (call equality[DivMod](solve(DivMod(n, n, B... (require 3/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:20:7:                             longProof                                       precond. (call equality[DivMod](solve(DivMod(n, n, B... (require 4/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:21:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:22:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:22:9:                             longProof                                       precond. (call reduceMod(DivMod(n, n, BigInt("0"), n)))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:23:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:23:9:                             longProof                                       precond. (call reduceMod(ModLessB(DivMod(n, n, BigIn...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:24:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:24:9:                             longProof                                       precond. (call reduceMod(DivMod(n, n, BigInt("1"), B...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:25:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:28:7:                             longProof                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:28:14:                            longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:30:7:                             longProof                                       precond. (call equality[DivMod](solve(DivMod(n, n, B... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:30:7:                             longProof                                       precond. (call equality[DivMod](solve(DivMod(n, n, B... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:30:7:                             longProof                                       precond. (call equality[DivMod](solve(DivMod(n, n, B... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:31:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:32:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:32:9:                             longProof                                       precond. (call increaseMod(DivMod(n, n, BigInt("0"),...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:33:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:33:9:                             longProof                                       precond. (call increaseMod(ModPlusB(DivMod(n, n, Big...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:34:9:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:37:7:                             longProof                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:37:14:                            longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:39:5:                             longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:39:5:                             longProof                                       postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:39:45:                            longProof                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:152:17:                                          loop                                            non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:155:7:                                           loop                                            body assertion: match exhaustiveness                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:155:22:                                          loop                                            precond. (call head[BigInt](list))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:156:7:                                           loop                                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:157:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:157:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:157:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:159:35:                                          loop                                            measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:159:35:                                          loop                                            precond. (call loop(values, tail[BigInt](list)))                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:159:40:                                          loop                                            precond. (call tail[BigInt](list))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:172:17:                                          loop                                            non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:177:7:                                           loop                                            body assertion: match exhaustiveness                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:177:22:                                          loop                                            precond. (call head[BigInt](list))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:178:7:                                           loop                                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:179:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:179:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:179:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:181:35:                                          loop                                            measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:181:35:                                          loop                                            precond. (call loop(values, tail[BigInt](list)) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:181:40:                                          loop                                            precond. (call tail[BigInt](list))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:249:17:                                          loop                                            non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:253:7:                                           loop                                            body assertion: match exhaustiveness                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:253:22:                                          loop                                            precond. (call head[BigInt](list))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:254:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:254:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:254:20:                                          loop                                            precond. (call countModZero(values, dividend) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:256:35:                                          loop                                            measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:256:35:                                          loop                                            precond. (call loop(values, tail[BigInt](list)) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:256:40:                                          loop                                            precond. (call tail[BigInt](list))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:266:17:                                          loop                                            non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:268:7:                                           loop                                            body assertion: match exhaustiveness                                    trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:268:19:                                          loop                                            precond. (call head[BigInt](listLoop))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:269:30:                                          loop                                            measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:269:35:                                          loop                                            precond. (call tail[BigInt](listLoop))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:279:17:                                          loop                                            non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:281:7:                                           loop                                            body assertion: match exhaustiveness                                    trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:281:19:                                          loop                                            precond. (call head[BigInt](listLoop))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:282:30:                                          loop                                            measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:282:35:                                          loop                                            precond. (call tail[BigInt](listLoop))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:131:17:                                          loopModfact                                     non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:136:7:                                           loopModfact                                     body assertion: match exhaustiveness                                    trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:136:21:                                          loopModfact                                     precond. (call head[BigInt](loopList))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:137:35:                                          loopModfact                                     precond. (call mod(current, dividend))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:138:7:                                           loopModfact                                     measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:138:19:                                          loopModfact                                     precond. (call tail[BigInt](loopList))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/Calc.scala:18:18:                                                  mod                                             class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/Calc.scala:24:29:                                                  mod                                             class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/Calc.scala:25:7:                                                   mod                                             postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:25:13:                          modAdd                                          class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:27:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:28:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:29:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:30:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:31:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:32:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:34:13:                          modAdd                                          class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:36:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:37:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:38:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:39:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:40:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:41:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:43:14:                          modAdd                                          class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:45:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:46:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:47:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:48:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:49:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:50:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:52:13:                          modAdd                                          class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:53:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:54:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:55:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:56:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:57:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:58:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:61:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:62:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:63:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:63:12:                          modAdd                                          precond. (call modUniqueDiv(z, solvedZ) (require 1/5))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:63:12:                          modAdd                                          precond. (call modUniqueDiv(z, solvedZ) (require 2/5))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:63:12:                          modAdd                                          precond. (call modUniqueDiv(z, solvedZ) (require 3/5))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:63:12:                          modAdd                                          precond. (call modUniqueDiv(z, solvedZ) (require 4/5))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:63:12:                          modAdd                                          precond. (call modUniqueDiv(z, solvedZ) (require 5/5))                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:64:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:66:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:67:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:68:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:69:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:72:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:74:13:                          modAdd                                          class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:75:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:76:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:77:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:78:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:80:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:81:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:81:12:                          modAdd                                          precond. (call ATimesBSameMod(a + c, b, bigDiv))                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:82:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:82:12:                          modAdd                                          precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:82:29:                          modAdd                                          precond. (call mod((a + c) + b * bigDiv, b))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:83:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:84:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:85:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:86:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:87:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:87:12:                          modAdd                                          precond. (call modUniqueDiv(w, xy) (require 1/5))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:87:12:                          modAdd                                          precond. (call modUniqueDiv(w, xy) (require 2/5))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:87:12:                          modAdd                                          precond. (call modUniqueDiv(w, xy) (require 3/5))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:87:12:                          modAdd                                          precond. (call modUniqueDiv(w, xy) (require 4/5))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:87:12:                          modAdd                                          precond. (call modUniqueDiv(w, xy) (require 5/5))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:88:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:90:5:                           modAdd                                          precond. (call equality[BigInt](solve(w).mod, solve(... (require 1/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:90:5:                           modAdd                                          precond. (call equality[BigInt](solve(w).mod, solve(... (require 2/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:90:5:                           modAdd                                          precond. (call equality[BigInt](solve(w).mod, solve(... (require 3/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:90:5:                           modAdd                                          precond. (call equality[BigInt](solve(w).mod, solve(... (require 4/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:93:7:                           modAdd                                          precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:95:7:                           modAdd                                          precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:95:11:                          modAdd                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:95:23:                          modAdd                                          precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:98:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:98:12:                          modAdd                                          precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:98:29:                          modAdd                                          precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:98:33:                          modAdd                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:98:45:                          modAdd                                          precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:99:5:                           modAdd                                          body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:99:12:                          modAdd                                          precond. (call div(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:99:29:                          modAdd                                          precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:99:41:                          modAdd                                          precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:99:53:                          modAdd                                          precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:99:57:                          modAdd                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:99:69:                          modAdd                                          precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:101:5:                          modAdd                                          postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:101:5:                          modAdd                                          precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:101:22:                         modAdd                                          precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:101:26:                         modAdd                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:101:38:                         modAdd                                          precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:102:7:                          modAdd                                          precond. (call div(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:102:24:                         modAdd                                          precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:102:36:                         modAdd                                          precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:102:48:                         modAdd                                          precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:102:52:                         modAdd                                          precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:102:64:                         modAdd                                          precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:11:15:                         modIdempotence                                  class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:13:7:                          modIdempotence                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:13:14:                         modIdempotence                                  precond. (call modIdempotencePositiveA(a, b) (require 1/2))             trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:13:14:                         modIdempotence                                  precond. (call modIdempotencePositiveA(a, b) (require 2/2))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:14:7:                          modIdempotence                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:14:14:                         modIdempotence                                  precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:14:27:                         modIdempotence                                  precond. (call mod(mod(a, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:14:31:                         modIdempotence                                  precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:16:7:                          modIdempotence                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:16:14:                         modIdempotence                                  precond. (call modIdempotencePositiveA(-a, b) (require 1/2))            trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:16:14:                         modIdempotence                                  precond. (call modIdempotencePositiveA(-a, b) (require 2/2))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:17:28:                         modIdempotence                                  class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:19:7:                          modIdempotence                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:20:7:                          modIdempotence                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:21:7:                          modIdempotence                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:22:7:                          modIdempotence                                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:22:14:                         modIdempotence                                  precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:22:27:                         modIdempotence                                  precond. (call mod(mod(a, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:22:31:                         modIdempotence                                  precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:24:5:                          modIdempotence                                  precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:24:18:                         modIdempotence                                  precond. (call mod(mod(a, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:24:22:                         modIdempotence                                  precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:31:18:                         modIdempotencePositiveA                         class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:34:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:35:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:36:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:37:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:38:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:39:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:42:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:43:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:44:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:44:22:                         modIdempotencePositiveA                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:46:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:46:12:                         modIdempotencePositiveA                         precond. (call mod(result, b))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:47:5:                          modIdempotencePositiveA                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:47:12:                         modIdempotencePositiveA                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:47:25:                         modIdempotencePositiveA                         precond. (call mod(result, b))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:48:5:                          modIdempotencePositiveA                         postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:48:5:                          modIdempotencePositiveA                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:48:18:                         modIdempotencePositiveA                         precond. (call mod(mod(a, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:48:22:                         modIdempotencePositiveA                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:10:7:                             modIdentity                                     postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:12:5:                             modIdentity                                     precond. (call mod(a, a))                                               trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdentity.scala:12:28:                            modIdentity                                     precond. (call div(a, a))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:146:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:146:12:                         modLess                                         precond. (call modAdd(x, b, c))                                         trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:148:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:148:21:                         modLess                                         precond. (call div(x, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:148:33:                         modLess                                         precond. (call mod(x, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:149:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:149:21:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:149:33:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:150:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:150:21:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:150:33:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:152:5:                          modLess                                         precond. (call equality[BigInt](x, a - c, a - c, (b ... (require 1/8))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:152:5:                          modLess                                         precond. (call equality[BigInt](x, a - c, a - c, (b ... (require 2/8))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:152:5:                          modLess                                         precond. (call equality[BigInt](x, a - c, a - c, (b ... (require 3/8))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:152:5:                          modLess                                         precond. (call equality[BigInt](x, a - c, a - c, (b ... (require 4/8))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:152:5:                          modLess                                         precond. (call equality[BigInt](x, a - c, a - c, (b ... (require 5/8))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:152:5:                          modLess                                         precond. (call equality[BigInt](x, a - c, a - c, (b ... (require 6/8))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:152:5:                          modLess                                         precond. (call equality[BigInt](x, a - c, a - c, (b ... (require 7/8))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:152:5:                          modLess                                         precond. (call equality[BigInt](x, a - c, a - c, (b ... (require 8/8))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:156:12:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:156:24:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:156:42:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:156:54:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:157:11:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:157:23:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:157:39:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:157:51:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:158:11:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:158:27:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:158:39:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:158:51:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:159:12:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:159:24:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:159:37:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:159:49:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:160:11:                         modLess                                         precond. (call div(x, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:160:23:                         modLess                                         precond. (call mod(x, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:161:11:                         modLess                                         precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:161:27:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:165:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:165:21:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:165:33:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:166:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:166:21:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:166:33:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:167:5:                          modLess                                         precond. (call equality[BigInt](a - c, (b * div(a, b... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:167:5:                          modLess                                         precond. (call equality[BigInt](a - c, (b * div(a, b... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:167:5:                          modLess                                         precond. (call equality[BigInt](a - c, (b * div(a, b... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:169:11:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:169:23:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:169:40:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:169:52:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:170:11:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:170:23:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:170:39:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:170:51:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:171:11:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:171:27:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:171:39:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:171:51:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:173:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:173:12:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:173:29:                         modLess                                         precond. (call mod((b * (div(a, b) - div(c, b)) + mo...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:173:38:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:173:50:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:173:63:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:173:75:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:174:13:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:174:25:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:175:18:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:175:30:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:176:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:176:12:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:176:29:                         modLess                                         precond. (call mod(b * m + others, b))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:177:5:                          modLess                                         precond. (call ATimesBSameMod(others, b, m))                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:178:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:178:12:                         modLess                                         precond. (call mod(b * m + others, b))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:178:38:                         modLess                                         precond. (call mod(others, b))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:179:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:179:12:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:179:29:                         modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:179:33:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:179:45:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:181:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:181:12:                         modLess                                         precond. (call div(x + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:181:29:                         modLess                                         precond. (call div(x, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:181:41:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:181:53:                         modLess                                         precond. (call div(mod(x, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:181:57:                         modLess                                         precond. (call mod(x, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:181:69:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:182:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:182:12:                         modLess                                         precond. (call div((a - c) + c, b))                                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:182:33:                         modLess                                         precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:182:49:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:182:61:                         modLess                                         precond. (call div(mod(a - c, b) + mod(c, b), b))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:182:65:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:182:81:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:183:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:183:12:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:183:25:                         modLess                                         precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:183:41:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:183:53:                         modLess                                         precond. (call div(mod(a - c, b) + mod(c, b), b))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:183:57:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:183:73:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:184:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:184:12:                         modLess                                         precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:184:28:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:184:40:                         modLess                                         precond. (call div(mod(a - c, b) + mod(c, b), b))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:184:44:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:184:60:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:184:77:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:185:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:185:12:                         modLess                                         precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:185:28:                         modLess                                         precond. (call div(mod(a - c, b) + mod(c, b), b))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:185:32:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:185:48:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:185:65:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:185:77:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:186:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:186:12:                         modLess                                         precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:186:29:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:186:41:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:186:53:                         modLess                                         precond. (call div(mod(a - c, b) + mod(c, b), b))                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:186:57:                         modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:186:73:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:12:                         modLess                                         precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:29:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:41:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:53:                         modLess                                         precond. (call div(mod(mod(a, b) - mod(c, b), b) + m...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:57:                         modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:61:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:73:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:187:89:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:192:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:192:12:                         modLess                                         precond. (call modModMinus(a, b, c))                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:193:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:194:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:194:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:194:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:194:40:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:194:52:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:195:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:195:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:195:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:195:40:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:195:52:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:196:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:196:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:196:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:196:40:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:196:52:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:198:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:199:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:199:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:199:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:199:39:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:199:52:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:199:64:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:199:76:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:200:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:200:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:200:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:200:39:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:200:52:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:200:64:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:200:80:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:201:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:201:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:201:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:201:39:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:201:52:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:201:64:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:201:80:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:203:5:                          modLess                                         body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:204:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:204:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:204:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:204:39:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:204:52:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:205:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:205:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:205:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:205:39:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:205:52:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:206:7:                          modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:206:11:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:206:23:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:206:39:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:206:52:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:209:5:                          modLess                                         postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:209:5:                          modLess                                         precond. (call mod(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:209:22:                         modLess                                         precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:209:26:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:209:38:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:210:5:                          modLess                                         precond. (call div(a - c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:210:22:                         modLess                                         precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:210:34:                         modLess                                         precond. (call div(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:210:46:                         modLess                                         precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:210:50:                         modLess                                         precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:210:62:                         modLess                                         precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:171:19:                        modModMinus                                     class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:173:19:                        modModMinus                                     class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:176:20:                        modModMinus                                     class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:180:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:181:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:182:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:184:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:185:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:187:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:188:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:190:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:191:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:192:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:194:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:195:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:196:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:197:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:198:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:199:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:201:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:202:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:203:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:204:5:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:206:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:207:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:208:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:208:14:                        modModMinus                                     precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:208:18:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:208:30:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:208:47:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:208:59:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:209:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:210:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:211:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:211:14:                        modModMinus                                     precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:211:18:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:211:30:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:214:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:215:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:216:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:217:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:218:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:219:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:219:14:                        modModMinus                                     precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:219:18:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:219:30:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:219:47:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:219:59:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:220:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:220:14:                        modModMinus                                     precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:220:18:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:220:30:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:223:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:224:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:225:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:226:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:227:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:228:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:229:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:230:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:230:14:                        modModMinus                                     precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:230:18:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:230:30:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:230:47:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:230:59:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:231:7:                         modModMinus                                     body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:231:14:                        modModMinus                                     precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:231:18:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:231:30:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:5:                         modModMinus                                     postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:5:                         modModMinus                                     precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:9:                         modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:21:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:38:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:50:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:66:                        modModMinus                                     precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:70:                        modModMinus                                     precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:234:82:                        modModMinus                                     precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:98:19:                         modModPlus                                      class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:100:19:                        modModPlus                                      class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:103:20:                        modModPlus                                      class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:107:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:108:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:109:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:111:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:112:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:114:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:115:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:117:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:118:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:119:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:121:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:122:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:123:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:125:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:126:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:127:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:129:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:130:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:131:5:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:134:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:135:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:136:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:136:14:                        modModPlus                                      precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:136:18:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:136:30:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:136:47:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:136:59:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:137:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:138:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:138:14:                        modModPlus                                      precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:138:18:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:138:30:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:142:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:143:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:144:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:145:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:146:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:147:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:148:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:148:14:                        modModPlus                                      precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:148:18:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:148:30:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:148:47:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:148:59:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:149:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:149:14:                        modModPlus                                      precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:149:18:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:149:30:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:153:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:154:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:155:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:156:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:157:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:158:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:159:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:160:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:161:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:161:14:                        modModPlus                                      precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:161:18:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:161:30:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:161:47:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:161:59:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:162:7:                         modModPlus                                      body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:162:14:                        modModPlus                                      precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:162:18:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:162:30:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:5:                         modModPlus                                      postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:5:                         modModPlus                                      precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:9:                         modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:21:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:38:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:50:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:66:                        modModPlus                                      precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:70:                        modModPlus                                      precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:165:82:                        modModPlus                                      precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:15:13:                       modSmallDividend                                class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:16:5:                        modSmallDividend                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:17:5:                        modSmallDividend                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:18:5:                        modSmallDividend                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:19:5:                        modSmallDividend                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:20:5:                        modSmallDividend                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:20:12:                       modSmallDividend                                precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:21:5:                        modSmallDividend                                body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:21:12:                       modSmallDividend                                precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:22:5:                        modSmallDividend                                postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:22:5:                        modSmallDividend                                precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSmallDividend.scala:23:5:                        modSmallDividend                                precond. (call div(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:65:15:                         modUnique                                       non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:69:13:                         modUnique                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:70:13:                         modUnique                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:73:7:                          modUnique                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:74:7:                          modUnique                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:77:7:                          modUnique                                       precond. (call MoreDivLessMod(a, b, divx, modx) (require 1/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:77:7:                          modUnique                                       precond. (call MoreDivLessMod(a, b, divx, modx) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:78:19:                         modUnique                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:79:7:                          modUnique                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:80:7:                          modUnique                                       measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:80:7:                          modUnique                                       precond. (call modUnique(a, b, divx + BigInt("1"), m... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:80:7:                          modUnique                                       precond. (call modUnique(a, b, divx + BigInt("1"), m... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:80:7:                          modUnique                                       precond. (call modUnique(a, b, divx + BigInt("1"), m... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:81:7:                          modUnique                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:84:7:                          modUnique                                       precond. (call LessDivMoreMod(a, b, divx, modx) (require 1/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:84:7:                          modUnique                                       precond. (call LessDivMoreMod(a, b, divx, modx) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:85:19:                         modUnique                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:86:7:                          modUnique                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:87:7:                          modUnique                                       measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:87:7:                          modUnique                                       precond. (call modUnique(a, b, divx - BigInt("1"), m... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:87:7:                          modUnique                                       precond. (call modUnique(a, b, divx - BigInt("1"), m... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:87:7:                          modUnique                                       precond. (call modUnique(a, b, divx - BigInt("1"), m... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:88:7:                          modUnique                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:90:5:                          modUnique                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:92:5:                          modUnique                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:92:5:                          modUnique                                       postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:92:39:                         modUnique                                       class invariant                                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:57:5:                          modUniqueDiv                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:57:12:                         modUniqueDiv                                    precond. (call modUnique(x.a, x.b, x.div, x.mod, y.d... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:57:12:                         modUniqueDiv                                    precond. (call modUnique(x.a, x.b, x.div, x.mod, y.d... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:57:12:                         modUniqueDiv                                    precond. (call modUnique(x.a, x.b, x.div, x.mod, y.d... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModIdempotence.scala:58:5:                          modUniqueDiv                                    postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:118:13:                         modZeroPlusC                                    precond. (call mod(a, b))                                               trivial                     0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:120:5:                          modZeroPlusC                                    precond. (call modAdd(a, b, c))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:121:5:                          modZeroPlusC                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:121:12:                         modZeroPlusC                                    precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:121:29:                         modZeroPlusC                                    precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:121:33:                         modZeroPlusC                                    precond. (call mod(a, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:121:45:                         modZeroPlusC                                    precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:122:5:                          modZeroPlusC                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:122:12:                         modZeroPlusC                                    precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:122:29:                         modZeroPlusC                                    precond. (call mod(BigInt("0") + mod(c, b), b))                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:122:37:                         modZeroPlusC                                    precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:123:5:                          modZeroPlusC                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:123:12:                         modZeroPlusC                                    precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:123:29:                         modZeroPlusC                                    precond. (call mod(mod(c, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:123:33:                         modZeroPlusC                                    precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:125:5:                          modZeroPlusC                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:125:12:                         modZeroPlusC                                    precond. (call modIdempotence(c, b))                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:126:5:                          modZeroPlusC                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:126:12:                         modZeroPlusC                                    precond. (call mod(mod(c, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:126:16:                         modZeroPlusC                                    precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:126:33:                         modZeroPlusC                                    precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:127:5:                          modZeroPlusC                                    body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:127:12:                         modZeroPlusC                                    precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:127:29:                         modZeroPlusC                                    precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:129:5:                          modZeroPlusC                                    postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:129:5:                          modZeroPlusC                                    precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:129:22:                         modZeroPlusC                                    precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:130:5:                          modZeroPlusC                                    precond. (call mod(a + c, b))                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:130:22:                         modZeroPlusC                                    precond. (call mod(mod(c, b), b))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModOperations.scala:130:26:                         modZeroPlusC                                    precond. (call mod(c, b))                                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:29:5:                           nextValuesMatchLoop                             postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:29:5:                           nextValuesMatchLoop                             precond. (call apply(seq, pos + BigInt("1")))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:29:21:                          nextValuesMatchLoop                             precond. (call apply(seq, pos))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:29:32:                          nextValuesMatchLoop                             precond. (call apply(seq.loop, loopPosition))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:85:5:                                            noModValuesAreZero                              precond. (call countModZero(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:85:5:                                            noModValuesAreZero                              precond. (call countModZero(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:85:5:                                            noModValuesAreZero                              precond. (call countModZero(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:139:13:                       noModZeroPropagate                              precond. (call countModZero(cycle.values, dividendA) (require 1/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:139:13:                       noModZeroPropagate                              precond. (call countModZero(cycle.values, dividendA) (require 2/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:139:13:                       noModZeroPropagate                              precond. (call countModZero(cycle.values, dividendA) (require 3/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:140:13:                       noModZeroPropagate                              precond. (call countModZero(cycle.values, dividendB) (require 1/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:140:13:                       noModZeroPropagate                              precond. (call countModZero(cycle.values, dividendB) (require 2/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:140:13:                       noModZeroPropagate                              precond. (call countModZero(cycle.values, dividendB) (require 3/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:144:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:145:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:146:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:148:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:149:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:150:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:152:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:152:12:                       noModZeroPropagate                              precond. (call countModZero(cycle, dividendA) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:152:12:                       noModZeroPropagate                              precond. (call countModZero(cycle, dividendA) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:152:12:                       noModZeroPropagate                              precond. (call countModZero(cycle, dividendA) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:153:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:153:12:                       noModZeroPropagate                              precond. (call countModZero(cycle, dividendB) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:153:12:                       noModZeroPropagate                              precond. (call countModZero(cycle, dividendB) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:153:12:                       noModZeroPropagate                              precond. (call countModZero(cycle, dividendB) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:155:18:                       noModZeroPropagate                              precond. (call checkMod(cycle, dividendA))                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:156:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:157:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:157:12:                       noModZeroPropagate                              precond. (call noModValuesAreZero(cycleA, dividendA))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:158:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:158:12:                       noModZeroPropagate                              precond. (call noModValuesAreZero(cycleA, dividendB))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:159:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:160:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:161:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:162:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:164:18:                       noModZeroPropagate                              precond. (call checkMod(cycleA, dividendB))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:165:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:166:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:166:12:                       noModZeroPropagate                              precond. (call noModValuesAreZero(cycleB, dividendA))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:167:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:167:12:                       noModZeroPropagate                              precond. (call noModValuesAreZero(cycleB, dividendB))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:168:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:169:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:170:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:171:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:172:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:173:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:174:5:                        noModZeroPropagate                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:176:5:                        noModZeroPropagate                              postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:176:5:                        noModZeroPropagate                              precond. (call noModValuesAreZero(cycleB, dividendA))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:177:7:                        noModZeroPropagate                              precond. (call noModValuesAreZero(cycleB, dividendB))                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:15:7:                         notEvaluatedNotInTheList                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:39:21:                        oneListNotInOther                               precond. (call checkMod(cycle, dividend))                               valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:42:7:                         oneListNotInOther                               postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:45:7:                         oneListNotInOther                               postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:48:7:                         oneListNotInOther                               postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:50:7:                         oneListNotInOther                               postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:37:5:                           prevValuesMatchLoop                             postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:37:5:                           prevValuesMatchLoop                             precond. (call apply(seq, pos - BigInt("1")))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:37:21:                          prevValuesMatchLoop                             precond. (call apply(seq, pos))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:37:32:                          prevValuesMatchLoop                             precond. (call apply(seq.loop, loopPosition))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:106:22:                     propagateModFromValueToCycle                    precond. (call mod(key, size(cycle)))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:107:5:                      propagateModFromValueToCycle                    postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:107:5:                      propagateModFromValueToCycle                    precond. (call mod(apply(cycle, key), dividend))                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:107:14:                     propagateModFromValueToCycle                    precond. (call apply(cycle, key))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:107:38:                     propagateModFromValueToCycle                    precond. (call mod(apply[BigInt](cycle.values, modKe...)                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:107:47:                     propagateModFromValueToCycle                    precond. (call apply[BigInt](cycle.values, modKeySize))                 valid from cache            0.0 ║
[ Info  ] ║                                                                                        reduceMod                                       postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:27:15:                                            reduceMod                                       non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:31:20:                                            reduceMod                                       body assertion: match exhaustiveness                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:31:20:                                            reduceMod                                       postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:33:18:                                            reduceMod                                       measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:33:18:                                            reduceMod                                       precond. (call reduceMod(next))                                         valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:34:6:                                             reduceMod                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:35:6:                                             reduceMod                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:36:6:                                             reduceMod                                       body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:37:5:                                             reduceMod                                       postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:67:7:                           seqPosMatchSeqLoop                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:67:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 1/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:67:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 2/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:67:49:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 1/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:67:49:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:68:7:                           seqPosMatchSeqLoop                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:68:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 1/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:68:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 2/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:68:50:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 1/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:68:50:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:69:7:                           seqPosMatchSeqLoop                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:69:14:                          seqPosMatchSeqLoop                              precond. (call apply(seq, to))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:69:24:                          seqPosMatchSeqLoop                              precond. (call apply(seq, from))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:72:18:                          seqPosMatchSeqLoop                              precond. (call apply(seq.loop, loopPosition))                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:73:7:                           seqPosMatchSeqLoop                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:73:14:                          seqPosMatchSeqLoop                              measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:73:14:                          seqPosMatchSeqLoop                              precond. (call seqPosMatchSeqLoop(from, to - BigInt(... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:73:14:                          seqPosMatchSeqLoop                              precond. (call seqPosMatchSeqLoop(from, to - BigInt(... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:74:7:                           seqPosMatchSeqLoop                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:74:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to - BigInt(...   (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:74:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to - BigInt(...   (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:74:55:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to - BigInt(...  (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:74:55:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to - BigInt(...  (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:75:7:                           seqPosMatchSeqLoop                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:75:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 1/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:75:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 2/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:75:58:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to - BigInt(...   (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:75:58:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to - BigInt(...   (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:76:7:                           seqPosMatchSeqLoop                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:76:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 1/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:76:14:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:76:58:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to - BigInt(...  (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:76:58:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to - BigInt(...  (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:78:5:                           seqPosMatchSeqLoop                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:78:12:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 1/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:78:12:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 2/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:78:47:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 1/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:78:47:                          seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:80:5:                           seqPosMatchSeqLoop                              postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:80:5:                           seqPosMatchSeqLoop                              precond. (call equality[BigInt](compareTwoSeqPos(fro... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:80:5:                           seqPosMatchSeqLoop                              precond. (call equality[BigInt](compareTwoSeqPos(fro... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:80:5:                           seqPosMatchSeqLoop                              precond. (call equality[BigInt](compareTwoSeqPos(fro... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:81:7:                           seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 1/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:81:7:                           seqPosMatchSeqLoop                              precond. (call compareTwoSeqPos(from, to, seq) (require 2/2))           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:82:7:                           seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 1/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:82:7:                           seqPosMatchSeqLoop                              precond. (call compareTwoSeqLoop(from, to, seq) (require 2/2))          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:83:7:                           seqPosMatchSeqLoop                              precond. (call apply(seq, to))                                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:83:17:                          seqPosMatchSeqLoop                              precond. (call apply(seq, from))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:84:7:                           seqPosMatchSeqLoop                              precond. (call sumAllCycleValues(from - size[BigInt]... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:84:7:                           seqPosMatchSeqLoop                              precond. (call sumAllCycleValues(from - size[BigInt]... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:84:7:                           seqPosMatchSeqLoop                              precond. (call sumAllCycleValues(from - size[BigInt]... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:84:51:                          seqPosMatchSeqLoop                              non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:23:27:                                        slice                                           precond. (call apply[BigInt](list, to))                                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:27:18:                                        slice                                           measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:27:18:                                        slice                                           precond. (call slice(list, from, to - BigInt("1")) (require 1/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:27:18:                                        slice                                           precond. (call slice(list, from, to - BigInt("1")) (require 2/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:27:18:                                        slice                                           precond. (call slice(list, from, to - BigInt("1")) (require 3/3))       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:27:36:                                        slice                                           non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:37:7:                       smallValueInCycle                               postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:41:5:                       smallValueInCycle                               precond. (call apply(cycle, key))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:41:19:                      smallValueInCycle                               precond. (call apply[BigInt](cycle.values, key))                        valid from cache            0.0 ║
[ Info  ] ║                                                                                        solve                                           postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:19:22:                                            solve                                           body assertion: match exhaustiveness                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:19:22:                                            solve                                           postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:19:36:                                            solve                                           precond. (call reduceMod(thiss))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:19:51:                                            solve                                           precond. (call increaseMod(thiss))                                      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:20:6:                                             solve                                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:21:6:                                             solve                                           body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:22:5:                                             solve                                           postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:90:5:                                            someModValuesAreZero                            precond. (call countModZero(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:90:5:                                            someModValuesAreZero                            precond. (call countModZero(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:90:5:                                            someModValuesAreZero                            precond. (call countModZero(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:91:7:                                            someModValuesAreZero                            precond. (call countModZero(thiss, dividend) (require 1/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:91:7:                                            someModValuesAreZero                            precond. (call countModZero(thiss, dividend) (require 2/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/Cycle.scala:91:7:                                            someModValuesAreZero                            precond. (call countModZero(thiss, dividend) (require 3/3))             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:184:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendA) (require 1/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:184:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendA) (require 2/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:184:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendA) (require 3/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:185:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendB) (require 1/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:185:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendB) (require 2/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:185:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendB) (require 3/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:186:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendA) (require 1/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:186:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendA) (require 2/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:186:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendA) (require 3/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:187:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendB) (require 1/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:187:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendB) (require 2/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:187:13:                       someModZeroPropagate                            precond. (call countModZero(cycle.values, dividendB) (require 3/3))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:191:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:192:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:193:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:195:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:196:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:197:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:199:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:199:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendB) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:199:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendB) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:199:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendB) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:200:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:200:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendA) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:200:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendA) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:200:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendA) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:201:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:201:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendB) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:201:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendB) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:201:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendB) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:202:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:202:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendA) (require 1/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:202:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendA) (require 2/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:202:12:                       someModZeroPropagate                            precond. (call countModZero(cycle, dividendA) (require 3/3))            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:204:18:                       someModZeroPropagate                            precond. (call checkMod(cycle, dividendA))                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:205:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:206:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:206:12:                       someModZeroPropagate                            precond. (call someModValuesAreZero(cycleA, dividendA))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:207:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:207:12:                       someModZeroPropagate                            precond. (call someModValuesAreZero(cycleA, dividendB))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:208:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:209:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:210:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:211:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:213:18:                       someModZeroPropagate                            precond. (call checkMod(cycleA, dividendB))                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:214:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:215:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:215:12:                       someModZeroPropagate                            precond. (call someModValuesAreZero(cycleB, dividendA))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:216:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:216:12:                       someModZeroPropagate                            precond. (call someModValuesAreZero(cycleB, dividendB))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:217:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:218:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:219:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:220:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:221:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:222:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:223:5:                        someModZeroPropagate                            body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:225:5:                        someModZeroPropagate                            postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:225:5:                        someModZeroPropagate                            precond. (call someModValuesAreZero(cycleB, dividendA))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleCheckMod.scala:226:7:                        someModZeroPropagate                            precond. (call someModValuesAreZero(cycleB, dividendB))                 valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:9:7:                                          sum                                             non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:13:7:                                         sum                                             precond. (call head[BigInt](loopList))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:13:23:                                        sum                                             measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/ListUtils.scala:13:27:                                        sum                                             precond. (call tail[BigInt](loopList))                                  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:129:7:                          sumAllCycleValues                               precond. (call apply(cycle, to))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:129:19:                         sumAllCycleValues                               measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:129:19:                         sumAllCycleValues                               precond. (call sumAllCycleValues(from, to - BigInt(... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:129:19:                         sumAllCycleValues                               precond. (call sumAllCycleValues(from, to - BigInt( ... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:129:19:                         sumAllCycleValues                               precond. (call sumAllCycleValues(from, to - BigInt( ... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/seq/properties/SeqProperties.scala:129:43:                         sumAllCycleValues                               non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:53:7:                                  sumAllMods                                      precond. (call mod(to, b))                                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:55:7:                                  sumAllMods                                      precond. (call mod(to, b))                                              valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:55:24:                                 sumAllMods                                      measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:55:24:                                 sumAllMods                                      precond. (call sumAllMods(from, to - BigInt("1"), b) (require 1/4))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:55:24:                                 sumAllMods                                      precond. (call sumAllMods(from, to - BigInt("1"), b) (require 2/4))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:55:24:                                 sumAllMods                                      precond. (call sumAllMods(from, to - BigInt("1"), b) (require 3/4))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:55:24:                                 sumAllMods                                      precond. (call sumAllMods(from, to - BigInt("1"), b) (require 4/4))     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:55:41:                                 sumAllMods                                      non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:61:5:                                  sumAllModsEqualSumOfAllSmallValues              precond. (call checkAllPreviousValues(b - BigInt("1"... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:61:5:                                  sumAllModsEqualSumOfAllSmallValues              precond. (call checkAllPreviousValues(b - BigInt("1"... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:61:5:                                  sumAllModsEqualSumOfAllSmallValues              precond. (call checkAllPreviousValues(b - BigInt("1"... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:62:5:                                  sumAllModsEqualSumOfAllSmallValues              precond. (call sumAllMods(BigInt("0"), b - BigInt(...   (require 1/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:62:5:                                  sumAllModsEqualSumOfAllSmallValues              precond. (call sumAllMods(BigInt("0"), b - BigInt(...   (require 2/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:62:5:                                  sumAllModsEqualSumOfAllSmallValues              precond. (call sumAllMods(BigInt("0"), b - BigInt(...   (require 3/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:62:5:                                  sumAllModsEqualSumOfAllSmallValues              precond. (call sumAllMods(BigInt("0"), b - BigInt(...   (require 4/4))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:62:32:                                 sumAllModsEqualSumOfAllSmallValues              precond. (call sumAllValues(BigInt("0"), b - BigInt(... (require 1/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:62:32:                                 sumAllModsEqualSumOfAllSmallValues              precond. (call sumAllValues(BigInt("0"), b - BigInt(... (require 2/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:62:32:                                 sumAllModsEqualSumOfAllSmallValues              precond. (call sumAllValues(BigInt("0"), b - BigInt(... (require 3/3))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:42:13:                                 sumAllValues                                    measure decreases                                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:42:13:                                 sumAllValues                                    precond. (call sumAllValues(from, to - BigInt("1")) (require 1/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:42:13:                                 sumAllValues                                    precond. (call sumAllValues(from, to - BigInt("1")) (require 2/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:42:13:                                 sumAllValues                                    precond. (call sumAllValues(from, to - BigInt("1")) (require 3/3))      valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:42:32:                                 sumAllValues                                    non-negative measure                                                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:14:5:                                  sumSymmetricalMods                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:14:12:                                 sumSymmetricalMods                              precond. (call mod(step, b))                                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:15:5:                                  sumSymmetricalMods                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:15:12:                                 sumSymmetricalMods                              precond. (call mod(b - step, b))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:16:5:                                  sumSymmetricalMods                              body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:16:12:                                 sumSymmetricalMods                              precond. (call mod(step, b))                                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:16:32:                                 sumSymmetricalMods                              precond. (call mod(b - step, b))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:17:5:                                  sumSymmetricalMods                              postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:17:5:                                  sumSymmetricalMods                              precond. (call mod(step, b))                                            valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/div/properties/ModSum.scala:17:25:                                 sumSymmetricalMods                              precond. (call mod(b - step, b))                                        valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:43:14:                                tail                                            precond. (call tail[BigInt](thiss.list))                                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/list/integral/Integral.scala:43:25:                                tail                                            precond. (call head(thiss))                                             valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:58:5:                       valueMatchAfterManyLoops                        precond. (call ATimesBSameMod(key, size(cycle), m))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:59:5:                       valueMatchAfterManyLoops                        postcondition                                                           valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:59:5:                       valueMatchAfterManyLoops                        precond. (call apply(cycle, key))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:59:19:                      valueMatchAfterManyLoops                        precond. (call apply(cycle, key + size(cycle) * m))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:79:5:                       valueMatchAfterManyLoopsInBoth                  precond. (call ATimesBSameMod(key, size(cycle), m1))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:80:5:                       valueMatchAfterManyLoopsInBoth                  precond. (call ATimesBSameMod(key, size(cycle), m2))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:81:5:                       valueMatchAfterManyLoopsInBoth                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:81:12:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:81:26:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key + size(cycle) * m1))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:82:5:                       valueMatchAfterManyLoopsInBoth                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:82:12:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:82:26:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key + size(cycle) * m2))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:83:5:                       valueMatchAfterManyLoopsInBoth                  precond. (call APlusMultipleTimesBSameMod(key, size(... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:83:5:                       valueMatchAfterManyLoopsInBoth                  precond. (call APlusMultipleTimesBSameMod(key, size(... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:84:5:                       valueMatchAfterManyLoopsInBoth                  precond. (call APlusMultipleTimesBSameMod(key, size(... (require 1/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:84:5:                       valueMatchAfterManyLoopsInBoth                  precond. (call APlusMultipleTimesBSameMod(key, size(... (require 2/2))  valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:85:5:                       valueMatchAfterManyLoopsInBoth                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:85:12:                      valueMatchAfterManyLoopsInBoth                  precond. (call mod(key, size(cycle)))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:85:41:                      valueMatchAfterManyLoopsInBoth                  precond. (call mod(key + size(cycle) * m1, size(cycle)))                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:86:5:                       valueMatchAfterManyLoopsInBoth                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:86:12:                      valueMatchAfterManyLoopsInBoth                  precond. (call mod(key, size(cycle)))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:86:41:                      valueMatchAfterManyLoopsInBoth                  precond. (call mod(key + size(cycle) * m2, size(cycle)))                valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:87:5:                       valueMatchAfterManyLoopsInBoth                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:87:12:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key + size(cycle) * m1))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:87:44:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:88:5:                       valueMatchAfterManyLoopsInBoth                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:88:12:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key + size(cycle) * m2))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:88:44:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key))                                       valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:89:5:                       valueMatchAfterManyLoopsInBoth                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:89:12:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key + size(cycle) * m2))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:89:44:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, mod(key, size(cycle))))                     valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:89:50:                      valueMatchAfterManyLoopsInBoth                  precond. (call mod(key, size(cycle)))                                   valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:90:5:                       valueMatchAfterManyLoopsInBoth                  body assertion: Inlined precondition of assert                          valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:90:5:                       valueMatchAfterManyLoopsInBoth                  postcondition                                                           valid from cache            0.0 ║
```

</details>

```bash
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:90:12:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key + size(cycle) * m1))                    valid from cache            0.0 ║
[ Info  ] ║ ./src/main/scala/v1/cycle/properties/CycleProperties.scala:90:44:                      valueMatchAfterManyLoopsInBoth                  precond. (call apply(cycle, key + size(cycle) * m2))                    valid from cache            0.0 ║
[ Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
[ Info  ] ║ total: 2723 valid: 2723 (2690 from cache, 11 trivial) invalid: 0    unknown: 0    time:   10.71                                                                                                                                                ║
[ Info  ] ╚════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╝
[ Info  ] Verification pipeline summary:
[ Info  ]   @extern, cache, anti-aliasing, return transformation, 
[ Info  ]   imperative elimination, type encoding, choose injection, nativez3, 
[ Info  ]   non-batched
[ Info  ] Shutting down executor service.

```