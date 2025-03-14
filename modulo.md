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

```scala
case class DivMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt) {
  require(div * b + mod == a)
  require(b != 0)

  def absB: BigInt = if (b > 0) b else -b
  def isValid: Boolean = div * b + mod == a
  def isFinal: Boolean = if (b > 0) mod < b && mod >= 0 else mod < -b && mod >= 0

  def solve: DivMod = {
    if (this.isFinal) return this

    val result = if (mod > 0) then reduceMod else increaseMod
    check(result.isFinal && result.isValid)
    check(result.a == a && result.b == b)
    result
  }.ensuring(res => res.isFinal && res.isValid && res.a == a && res.b == b)

  def reduceMod: DivMod = {
    require(mod >= 0)
    decreases(mod)

    if (isFinal) return this

    val next = if (b > 0) then ModLessB else ModPlusB

    val result = next.reduceMod
    check(result.isFinal && result.isValid)
    check(result.mod < mod)
    check(result.a == a && result.b == b)
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def increaseMod: DivMod = {
    require(mod < 0) //                                               since mod is negative, it is not final
    decreases(-mod) //                                                mod should increase every iteration

    val next = if (b < 0) then ModLessB else ModPlusB //              increase the mod by abs(b)
    val result = if (next.isFinal) then next else next.increaseMod // repeat until mod is final
    check(result.isFinal && result.isValid) //                        result is final and valid
    check(result.a == a && result.b == b) //                          result has the same a and b as the original DivMod
    check(result.mod >= 0) //                                         result has a non-negative mod
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def ModPlusB: DivMod = {
    check(div * b + mod == a)
    check(div * b - b + mod + b == a)  //         adding +b and -b does not change the value
    check((div - 1) * b + (mod + b) == a) //      isolating div - 1 and mod + b
    val next = DivMod(a, b, div - 1, mod + b) //  is valid because next.div * next.b + next.mod == next.a as proved above
    check(next.a == a && next.b == b) //          next.a and next.b are the same as the original DivMod
    check(next.mod == mod + b) //                 next.mod is the same as the original DivMod plus b
    check(next.div == div - 1) //                 next.div is the same as the original DivMod minus 1
    check(next.isValid) //                        next is valid
    next
  }

  def ModLessB: DivMod = {
    check(div * b + mod == a)
    check(div * b + b + mod - b == a) //          adding -b and +b does not change the value
    check((div + 1) * b + (mod - b) == a) //      isolating div + 1 and mod - b
    val next = DivMod(a, b, div + 1, mod - b) //  is valid because next.div * next.b + next.mod == next.a as proved above
    check(next.a == a && next.b == b) //          next.a and next.b are the same as the original DivMod
    check(next.mod == mod - b) //                 next.mod is the same as the original DivMod minus b
    check(next.div == div + 1) //                 next.div is the same as the original DivMod plus 1
    check(next.isValid) //                        next is valid
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

### Creating the Division and Module Operations

As we can see in the class [Calc](
./src/main/scala/v1/Calc.scala
), we can define the division and module operations by extracting these properties from the solved $DivMod$ as follows:

```scala
  def div(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    check(a == 0 * b + a)
    val result = DivMod(a, b, 0, a)
    val solved = result.solve
    solved.div
  }

  def mod(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    check(a == 0 * b + a)
    val result = DivMod(a, b, 0, a)
    val solved = result.solve
    solved.mod
  }
```
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

```scala
def modSmallDividend(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(b > a)
    require(a >= 0)
    val x = DivMod(a, b, 0, a)
    check(x.isFinal)
    check(x == x.solve)
    check(x.mod == a)
    check(x.div == 0)
    check(Calc.mod(a, b) == x.mod)
    check(Calc.div(a, b) == 0)
    Calc.mod(a, b) == a &&
    Calc.div(a, b) == 0
  }.holds
```

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

```scala
  def longProof(n: BigInt): Boolean = {
   require(n != 0)
   check(!DivMod(a = n, b = n, div = 0, mod = n).isFinal)
  
   if (n > 0) {
    check(
     equality(
      DivMod(a=n, b=n, div=0, mod=n).solve,               // is equals to
      DivMod(a=n, b=n, div=0, mod=n).reduceMod.solve,     // is equals to
      DivMod(a=n, b=n, div=0, mod=n).ModLessB.reduceMod,  // is equals to
      DivMod(a=n, b=n, div=1, mod=0).reduceMod,           // is equals to
      DivMod(a=n, b=n, div=1, mod=0)
     )
    )
    // since
    check(DivMod(a=n, b=n, div=1, mod=0).isFinal)
   } else {
    check(equality(
     DivMod(a=n, b=n, div=0, mod=n).solve,                 // is equals to
     DivMod(a=n, b=n, div=0, mod=n).increaseMod.solve,     // is equals to
     DivMod(a=n, b=n, div=0, mod=n).ModPlusB.increaseMod,  // is equals to
     DivMod(a=n, b=n, div=1, mod=0)
    ))
    // since
    check(DivMod(a=n, b=n, div=1, mod=0).isFinal)
   }
   DivMod(a=n, b=n, div=0, mod=n).solve == DivMod(a=n, b=n, div=1, mod=0)
  }.holds
```

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
./src/main/scala/v1/div/properties/DivModAdditionAndMultiplication.scala#MoreDivLessMod
) and [LessDivMoreMod](
./src/main/scala/v1/div/properties/DivModAdditionAndMultiplication.scala#LessDivMoreMod
) and shown the code below, the division result is the same for the same dividend and divisor, regardless of the div and mod values, as long $a = b \cdot div + mod$.

```scala
  def MoreDivLessMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    val div1 = DivMod(a, b, div, mod)
    val div2 = DivMod(a, b, div + 1, mod - b)

    if (div1.isFinal) check(!div2.isFinal && div2.solve == div1.solve)
    if (div2.isFinal) check(!div1.isFinal && div1.solve == div2.solve)

    if (div1.mod < 0) {
      check(div1.solve == div1.increaseMod)
      if (b > 0) {
        check(
          equality(
            div2.solve, //       is equals to
            div2.increaseMod, // is equals to
            div1.increaseMod, // is equals to
            div1.solve
          )
        )
      } else {
        check(
          equality(
            div1.increaseMod, // is equals to
            div2.solve, //       is equals to
            div1.solve
          )
        )
      }
      check(div1.solve == div2.solve)
    }
    if (div1.mod > 0 && ! div1.isFinal && ! div2.isFinal) {
      if (b > 0 ) {
        check(div2.mod < div1.mod)
        check(
          equality(
            div1.solve, //       is equals to
            div1.reduceMod, //   is equals to
            div2.solve
          )
        )
      } else {
        check(div2.mod > div1.mod)
        check(
          equality(
            div2.solve, //     is equals to
            div2.reduceMod, // is equals to
            div2.solve
          )
        )
      }
    }
    check(div1.solve == div2.solve)
    DivMod(a,b, div + 1, mod - b).solve.mod == DivMod(a,b, div, mod).solve.mod
  }.holds

  def LessDivMoreMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)

    check(
      equality(
        a, //                     is equals to
        div * b + mod, //         is equals to
        (div - 1) * b + (mod + b)
      )
    )
    MoreDivLessMod(a, b, div - 1, mod + b)

    DivMod(a, b, div, mod).solve == DivMod(a, b, div - 1, mod + b).solve
  }.holds

```

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
./src/main/scala/v1/div/properties/ModIdempotence.scala#44
) as shown below:


```scala
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
      check(modx == mody)
      check(x == y)
    }
    if (divx < divy) {
      AdditionAndMultiplication.MoreDivLessMod(a, b, divx, modx) // calling the proof of the property MoreDivLessMod
      check(modx > mody)
      val next =  DivMod(a, b, divx + 1, modx - b)
      check(x.solve == next.solve)
      modUnique(a, b, divx + 1, modx - b, divy, mody)
      check(x.solve == y.solve)
    }
    if (divx > divy) {
      AdditionAndMultiplication.LessDivMoreMod(a, b, divx, modx) // calling the proof of the property LessDivMoreMod
      check(modx < mody)
      val next =  DivMod(a, b, divx - 1, modx + b)
      check(x.solve == next.solve)
      modUnique(a, b, divx - 1, modx + b, divy, mody)
      check(x.solve == y.solve)
    }
    check(x.solve == y.solve)

    DivMod(a, b, divx, modx).solve == DivMod(a, b, divy, mody).solve
  }.holds
```

### Modulo Idempotence

```math
\begin{aligned}
\forall \text{ } a,b & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b & = ( a \text{ mod } b ) \text{ mod } b \\
\end{aligned}
```

The proof of the modulo idempotence property is available in the [ModIdempotence](./src/main/scala/v1/div/properties/ModIdempotence.scala) as follows:

```scala
  def modIdempotence(a: BigInt, b: BigInt): Boolean = {
   require(b != 0)
   require(a >= 0)
  
   val div = DivMod(a, b, 0, a)
  
   val solved = div.solve
   check(solved.isFinal)
   check(solved.b == div.b)
   check(solved.a == div.a)
   check(div.absB > 0)
   check(solved.mod < div.absB)
   check(solved.mod >= 0)
  
   val result = solved.mod
   check(result <= a)
   check(result < div.absB)
   check(result == Calc.mod(a, b))
  
   check(Calc.mod(result, b) == result)
   check(Calc.mod(a, b) == Calc.mod(result, b))
   Calc.mod(a, b) == Calc.mod(Calc.mod(a, b), b)
  }.holds
```

### Distributivity over Addition and Subtraction

```math
\begin{aligned}
\forall \text{ } a,b,c & \in \mathbb{Z} : b \neq 0 \\
( a + c ) \text{ mod } b & = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b \\
( a - c ) \text{ mod } b & = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b \\
( a + c ) \text{ div } b & = a \text{ div } b + c \text{ div } b + ( a \text{ mod } b + c \text{ mod } b ) \text{ div } b \\
( a - c ) \text{ div } b & = a \text{ div } b - c \text{ div } b + ( a \text{ mod } b - c \text{ mod } b ) \text{ div } b \\
\end{aligned}
```

These properties are proved in the [ModOperations](
./src/main//scala/v1/div/properties/ModOperations.scala
), as shown as follows:

```scala
 def modAdd(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val absB = if (b < 0) -b else b

    val x = DivMod(a, b, 0, a)
    val solvedX = x.solve
    check(solvedX.mod < absB)
    check(solvedX.a == a && solvedX.b == b)
    check(solvedX.a == solvedX.b * solvedX.div + solvedX.mod) // by definition
    check(solvedX.a - solvedX.b * solvedX.div == solvedX.mod) // transposing solvedX.b * solvedX.div to the left side

    val y = DivMod(c, b, 0, c)
    val solvedY = y.solve
    check(solvedY.mod < absB)
    check(solvedY.a == c && solvedY.b == b)
    check(solvedY.a == solvedY.b * solvedY.div + solvedY.mod) // by definition
    check(solvedY.a - solvedY.b * solvedY.div == solvedY.mod) // transposing solvedY.b * solvedY.div to the left side

    val xy = DivMod(a + c, b, 0, a + c) // xy is the division of a + c by b
    val solvedXY = xy.solve
    check(solvedXY.mod < absB)
    check(solvedXY.a == a + c)
    check(solvedXY.b == b)
    check(solvedXY.a == solvedXY.b * solvedXY.div + solvedXY.mod)
    check(a + c == b * solvedXY.div + solvedXY.mod) // by definition

    val z = DivMod(solvedX.mod + solvedY.mod, b, 0, solvedX.mod + solvedY.mod)
    check(z.a == z.b * z.div + z.mod) // by definition
    check(z.mod == solvedX.mod + solvedY.mod)

    val solvedZ = z.solve
    check(solvedZ.mod < absB)
    check(modUniqueDivMod(z, solvedZ))
    check(z.solve.mod == solvedZ.mod)

    check(solvedX.mod + solvedY.mod == b * solvedZ.div + solvedZ.mod)
    check(solvedX.a - solvedX.b * solvedX.div + solvedY.a - solvedY.b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a - b * solvedX.div + c - b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a + c == b * solvedZ.div + b * solvedX.div + b * solvedY.div + solvedZ.mod) // transposing b * solvedX.div + b * solvedY.div to the left side

    val bigDiv = solvedZ.div + solvedX.div + solvedY.div
    check(a + c == b * bigDiv + solvedZ.mod)

    val w = DivMod(a + c, b, bigDiv, solvedZ.mod) // is valid since a + c = b * bigDiv + solvedZ.mod
    check(solvedZ.mod < absB)
    check(w.mod == solvedZ.mod)
    check(w.isFinal && w.solve == w)

    /* calling the proof of the property Module Plus Multiples of Divisor
     * mod(a + m * b, b) = mod(a, b)
     * described previously
     */
    DivModAdditionAndMultiplication.ATimesBSameMod(a + c, b, bigDiv)
    check(Calc.mod(a + c,b) == Calc.mod( a + c + b * bigDiv, b ))
    check(w.a == xy.a && w.b == xy.b)
    /* calling the proof of the property Unique Remainder
     * mod(a, b) = mod(a, b)
     * described previously
     */
    check(modUniqueDivMod(w, xy))
    check(w.solve == xy.solve)
    check(w.solve.mod == xy.solve.mod == Calc.mod(a+c,b) == solvedZ.mod)

    Calc.mod(a + c, b) == Calc.mod(Calc.mod(a, b) + Calc.mod(c, b), b) &&
    Calc.div(a + c, b) == Calc.div(a, b) + Calc.div(c, b) + Calc.div(Calc.mod(a, b) + Calc.mod(c, b), b)
  }.holds

  def modLess(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)
    modAdd(a - c, b, c)
    Calc.mod(a - c, b) == Calc.mod(Calc.mod(a, b) - Calc.mod(c, b), b) &&
    Calc.div(a - c, b) == Calc.div(a, b) - Calc.div(c, b) + Calc.div(Calc.mod(a, b) - Calc.mod(c, b), b)
  }.holds
```

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
```

Those properties could be verified by the Scala Stainless as we can see in the code bellow from the [Summary.scala](
 ./src/main/scala/v1/div/properties/Summary.scala
) file.   

```scala
  def PropertySummary(a: BigInt, b: BigInt, c: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)

    if (a >= 0 && b > a) {
      check(ModSmallDividend.modSmallDividend(a, b))
    }

    check(ModIdempotence.modIdempotence(a, b))
    check(ModIdentity.modIdentity(b))
    check(AdditionAndMultiplication.APlusBSameModPlusDiv(a, b))
    check(AdditionAndMultiplication.ALessBSameModDecreaseDiv(a, b))
    check(AdditionAndMultiplication.ATimesBSameMod(a, b, m))

    check(AdditionAndMultiplication.ALessMultipleTimesBSameMod(a, b, m))
    check(AdditionAndMultiplication.APlusMultipleTimesBSameMod(a, b, m))

    check(ModOperations.modAdd(a, b, c))
    check(ModOperations.modLess(a, b, c))

    check(ModIdempotence.modModPlus(a, b, c))
    check(ModIdempotence.modModMinus(a, b, c))

    check(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
    check(mod(a - c, b) == mod(mod(a, b) - mod(c, b), b))
    check(if a >= 0 && b > a then div(a,b) == 0 else true)
    check(if a >= 0 && b > a then mod(a,b) == a else true)
    check(if b > 0 then mod(mod(a, b), b) == mod(a, b) else true)
    check(mod(b, b)         == 0)
    check(div(b, b)         == 1)
    check(mod(a + b * m, b) == mod(a, b))
    check(mod(a - b * m, b) == mod(a, b))
    check(div(a + b, b)     == div(a, b) + 1)
    check(div(a - b, b)     == div(a, b) - 1)
    check(div(a + b * m, b) == div(a, b) + m)
    check(div(a - b * m, b) == div(a, b) - m)
    check(div(a + c, b)     == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b))
    check(div(a - c, b)     == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b))
    check(mod(a + c, b)     == mod(mod(a, b) + mod(c, b), b))
    check(mod(a - c, b)     == mod(mod(a, b) - mod(c, b), b))
    check(mod(a + c, b)     == mod(a, b) + mod(c, b) - b * div(mod(a, b) + mod(c, b), b))
    check(mod(a - c, b)     == mod(a, b) - mod(c, b) - b * div(mod(a, b) - mod(c, b), b))

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
    mod(a - c, b)     == mod(a, b) - mod(c, b) - b * div(mod(a, b) - mod(c, b), b)
  }.holds
```

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
$ just verify
jenv local 21
stainless $(find ./src/main/scala -name '*.scala' | tr '\n' ' ')
[  Info  ] Finished compiling                                       
[  Info  ] Preprocessing finished                                   
[  Info  ] Finished lowering the symbols                            
[  Info  ] Finished generating VCs                                  
[  Info  ] Starting verification...
[  Info  ] Verified: 0 / 540
[Warning ] The Z3 native interface is not available. Falling back onto smt-z3.
[  Info  ] Verified: 540 / 540
[  Info  ] Done in 12.14s
[  Info  ] Verified: 1016 / 1016
[  Info  ] Done in 23.49s
[  Info  ]   ┌───────────────────┐
[  Info  ] ╔═╡ stainless summary ╞═════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗
[  Info  ] ║ └───────────────────┘                                                                                                                                                                                     ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:82:17:    ALessBSameModDecreaseDiv    class invariant                                                         valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:85:5:     ALessBSameModDecreaseDiv    body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:86:5:     ALessBSameModDecreaseDiv    body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:87:5:     ALessBSameModDecreaseDiv    body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:88:5:     ALessBSameModDecreaseDiv    body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:89:5:     ALessBSameModDecreaseDiv    body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:90:5:     ALessBSameModDecreaseDiv    body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:91:5:     ALessBSameModDecreaseDiv    body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala:92:5:     ALessBSameModDecreaseDiv    body assertion: Inlined precondition of check                           valid from cache     0.0 ║
...
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:15:7:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:15:13:                      PropertySummary             precond. (call modSmallDividend(a, b) (require 1/3))                    trivial              0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:15:13:                      PropertySummary             precond. (call modSmallDividend(a, b) (require 2/3))                    valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:15:13:                      PropertySummary             precond. (call modSmallDividend(a, b) (require 3/3))                    valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:16:7:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:16:13:                      PropertySummary             precond. (call modIdempotence(a, b) (require 1/2))                      valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:16:13:                      PropertySummary             precond. (call modIdempotence(a, b) (require 2/2))                      valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:19:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:19:11:                      PropertySummary             precond. (call modIdentity(b))                                          valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:20:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:20:11:                      PropertySummary             precond. (call APlusBSameModPlusDiv(a, b))                              valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:21:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:21:11:                      PropertySummary             precond. (call ALessBSameModDecreaseDiv(a, b))                          valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:22:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:22:11:                      PropertySummary             precond. (call ATimesBSameMod(a, b, m))                                 valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:11:                      PropertySummary             precond. (call ALessMultipleTimesBSameMod(a, b, m) (require 1/2))       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:11:                      PropertySummary             precond. (call ALessMultipleTimesBSameMod(a, b, m) (require 2/2))       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:25:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:25:11:                      PropertySummary             precond. (call APlusMultipleTimesBSameMod(a, b, m) (require 1/2))       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:25:11:                      PropertySummary             precond. (call APlusMultipleTimesBSameMod(a, b, m) (require 2/2))       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:27:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:27:11:                      PropertySummary             precond. (call modAdd(a, b, c))                                         valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:28:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:28:11:                      PropertySummary             precond. (call modLess(a, b, c))                                        valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:30:5:                       PropertySummary             postcondition                                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:30:30:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:31:30:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:32:5:                       PropertySummary             precond. (call mod(b, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:5:                       PropertySummary             precond. (call div(b, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:5:                       PropertySummary             precond. (call mod(a + b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:26:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:35:5:                       PropertySummary             precond. (call mod(a - b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:35:26:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:5:                       PropertySummary             precond. (call mod(mod(a, b), b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:9:                       PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:26:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:37:5:                       PropertySummary             precond. (call div(a + b, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:37:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:38:5:                       PropertySummary             precond. (call div(a - b, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:38:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:39:5:                       PropertySummary             precond. (call div(a + b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:39:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:40:5:                       PropertySummary             precond. (call div(a - b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:40:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:5:                       PropertySummary             precond. (call mod(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:26:                      PropertySummary             precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:30:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:42:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:5:                       PropertySummary             precond. (call mod(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:26:                      PropertySummary             precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:30:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:42:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:5:                       PropertySummary             precond. (call div(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:38:                      PropertySummary             precond. (call div(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:50:                      PropertySummary             precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:54:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:66:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:5:                       PropertySummary             precond. (call div(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:38:                      PropertySummary             precond. (call div(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:50:                      PropertySummary             precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:54:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:66:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
...
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:15:7:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:15:13:                      PropertySummary             precond. (call modSmallDividend(a, b) (require 1/3))                    trivial              0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:15:13:                      PropertySummary             precond. (call modSmallDividend(a, b) (require 2/3))                    valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:15:13:                      PropertySummary             precond. (call modSmallDividend(a, b) (require 3/3))                    valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:18:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:18:11:                      PropertySummary             precond. (call modIdempotence(a, b))                                    valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:19:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:19:11:                      PropertySummary             precond. (call modIdentity(b))                                          valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:20:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:20:11:                      PropertySummary             precond. (call APlusBSameModPlusDiv(a, b))                              valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:21:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:21:11:                      PropertySummary             precond. (call ALessBSameModDecreaseDiv(a, b))                          valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:22:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:22:11:                      PropertySummary             precond. (call ATimesBSameMod(a, b, m))                                 valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:11:                      PropertySummary             precond. (call ALessMultipleTimesBSameMod(a, b, m) (require 1/2))       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:24:11:                      PropertySummary             precond. (call ALessMultipleTimesBSameMod(a, b, m) (require 2/2))       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:25:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:25:11:                      PropertySummary             precond. (call APlusMultipleTimesBSameMod(a, b, m) (require 1/2))       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:25:11:                      PropertySummary             precond. (call APlusMultipleTimesBSameMod(a, b, m) (require 2/2))       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:27:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:27:11:                      PropertySummary             precond. (call modAdd(a, b, c))                                         valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:28:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:28:11:                      PropertySummary             precond. (call modLess(a, b, c))                                        valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:30:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:30:11:                      PropertySummary             precond. (call modModPlus(a, b, c))                                     valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:31:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:31:11:                      PropertySummary             precond. (call modModMinus(a, b, c))                                    valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:11:                      PropertySummary             precond. (call mod(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:28:                      PropertySummary             precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:32:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:33:44:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:11:                      PropertySummary             precond. (call mod(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:28:                      PropertySummary             precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:32:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:34:44:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:35:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:35:35:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:36:35:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:37:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:37:25:                      PropertySummary             precond. (call mod(mod(a, b), b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:37:29:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:37:46:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:38:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:38:11:                      PropertySummary             precond. (call mod(b, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:39:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:39:11:                      PropertySummary             precond. (call div(b, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:40:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:40:11:                      PropertySummary             precond. (call mod(a + b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:40:32:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:11:                      PropertySummary             precond. (call mod(a - b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:41:32:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:11:                      PropertySummary             precond. (call div(a + b, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:42:32:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:11:                      PropertySummary             precond. (call div(a - b, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:43:32:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:11:                      PropertySummary             precond. (call div(a + b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:44:32:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:11:                      PropertySummary             precond. (call div(a - b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:45:32:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:11:                      PropertySummary             precond. (call div(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:32:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:44:                      PropertySummary             precond. (call div(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:56:                      PropertySummary             precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:60:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:46:72:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:11:                      PropertySummary             precond. (call div(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:32:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:44:                      PropertySummary             precond. (call div(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:56:                      PropertySummary             precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:60:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:47:72:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:11:                      PropertySummary             precond. (call mod(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:32:                      PropertySummary             precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:36:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:48:48:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:11:                      PropertySummary             precond. (call mod(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:32:                      PropertySummary             precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:36:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:49:48:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:11:                      PropertySummary             precond. (call mod(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:32:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:44:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:60:                      PropertySummary             precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:64:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:50:76:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:51:5:                       PropertySummary             body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:51:11:                      PropertySummary             precond. (call mod(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:51:32:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:51:44:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:51:60:                      PropertySummary             precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:51:64:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:51:76:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:53:5:                       PropertySummary             postcondition                                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:53:30:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:54:30:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:55:5:                       PropertySummary             precond. (call mod(b, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:56:5:                       PropertySummary             precond. (call div(b, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:57:5:                       PropertySummary             precond. (call mod(a + b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:57:26:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:58:5:                       PropertySummary             precond. (call mod(a - b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:58:26:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:59:5:                       PropertySummary             precond. (call mod(mod(a, b), b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:59:9:                       PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:59:26:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:60:5:                       PropertySummary             precond. (call div(a + b, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:60:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:61:5:                       PropertySummary             precond. (call div(a - b, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:61:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:62:5:                       PropertySummary             precond. (call div(a + b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:62:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:63:5:                       PropertySummary             precond. (call div(a - b * m, b))                                       valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:63:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:5:                       PropertySummary             precond. (call div(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:38:                      PropertySummary             precond. (call div(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:50:                      PropertySummary             precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:54:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:64:66:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:5:                       PropertySummary             precond. (call div(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:26:                      PropertySummary             precond. (call div(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:38:                      PropertySummary             precond. (call div(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:50:                      PropertySummary             precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:54:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:65:66:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:66:5:                       PropertySummary             precond. (call mod(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:66:26:                      PropertySummary             precond. (call mod(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:66:30:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:66:42:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:5:                       PropertySummary             precond. (call mod(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:26:                      PropertySummary             precond. (call mod(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:30:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:67:42:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:5:                       PropertySummary             precond. (call mod(a + c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:26:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:38:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:54:                      PropertySummary             precond. (call div(mod(a, b) + mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:58:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:68:70:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:69:5:                       PropertySummary             precond. (call mod(a - c, b))                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:69:26:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:69:38:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:69:54:                      PropertySummary             precond. (call div(mod(a, b) - mod(c, b), b))                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:69:58:                      PropertySummary             precond. (call mod(a, b))                                               valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/properties/Summary.scala:69:70:                      PropertySummary             precond. (call mod(c, b))                                               valid from cache     0.0 ║
...
[  Info  ] ║                                                                              solve                       postcondition                                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:18:22:                                  solve                       body assertion: match exhaustiveness                                    valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:18:22:                                  solve                       postcondition                                                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:18:36:                                  solve                       precond. (call reduceMod(thiss))                                        valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:18:51:                                  solve                       precond. (call increaseMod(thiss))                                      valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:19:5:                                   solve                       body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:20:5:                                   solve                       body assertion: Inlined precondition of check                           valid from cache     0.0 ║
[  Info  ] ║ ./src/main/scala/v1/div/DivMod.scala:21:5:                                   solve                       postcondition                                                           valid from cache     0.0 ║
[  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
[  Info  ] ║ total: 1016 valid: 1016 (1007 from cache, 9 trivial) invalid: 0    unknown: 0    time:    1.80                                                                                                            ║
[  Info  ] ╚═══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╝
[  Info  ] Verification pipeline summary:
[  Info  ]   @extern, cache, anti-aliasing, return transformation, 
[  Info  ]   imperative elimination, type encoding, choose injection, nativez3, 
[  Info  ]   non-batched
[  Info  ] Shutting down executor service.
```