# Proving Properties of Division and Modulo using Formal Verification

## Abstract

The division and modulo operations are fundamental elements in the study of programming and mathematics.
Prime numbers, modular arithmetic, and cryptography are some of the areas where these operations are used.
In this article, we show how to prove some properties of these operations using the recursive definition
of the division and modulo operations, such as the unique remainder, modulo idempotence, and distributivity
over addition and subtraction. We used Scala Stainless to verify these properties. Since these proofs are
available in the source code, we can use them as a base to prove other properties related to the division
and modulo operations.

## Introduction

Given integers $dividend$ and $divisor$ where $divisor \neq 0$, the division algorithm determines integers $quotient$ 
and $remainder$ such that:

```math
\displaylines{ \\
\forall \text{ } dividend, divisor \in \mathbb{N}, \text{ where } divisor\neq 0  \\
\exists ! \\
\text{quotient} = \left\lfloor \frac{\text{dividend}}{\text{divisor}} \right\rfloor \implies   \\
dividend = divisor \cdot quotient + \text{remainder}, \text { where } 0 \leq \text{remainder} < |b|, \\
dividend \text{ mod } divisor = remainder, \\
dividend \text{ div } divisor = quotient. \\
} \\
```

## Recursive Definition

Some properties of the division and modulo can be proved using the 
recursive definition of the division and modulo operations.

The recursive definition of the division and modulo operations are:

```math
\displaylines{ \\
\forall a, b, div \text{ and } mod \in \mathbb{Z}, \\
\text{where } b \neq 0 \\
}
```

We define $Div(a, b, div, mod)$ such that:

```math
a = \text{div} \cdot b + \text{mod}
```

The solved $Div$ are those where the remainder $mod$ satisfies:

```math
\begin{cases}
0 \leq \text{mod} < b & \text{if } b > 0, \\
0 \leq \text{mod} < -b & \text{if } b < 0.
\end{cases}
```

### Recursive Formula

```math
\displaylines{ \\
\text{Div.solve}(a, b, \text{div}, \text{mod}) =
\begin{cases}
\text{Div}(a, b, \text{div}, \text{mod}) & \text{if } 0 \leq \text{mod} < |b|, \\
\text{Div.solve}(a, b, \text{div} + \text{sign}(b), \text{mod} - |b|) & \text{if } \text{mod} \geq |b|, \\
\text{Div.solve}(a, b, \text{div} - \text{sign}(b), \text{mod} + |b|) & \text{if } \text{mod} < 0. \\
\end{cases} \\
}
```

We can see the described [recursive definition on Scala](
./src/main/scala/v1/div/Div.scala
), simplified as follows:

```scala
case class Div(a: BigInt, b: BigInt, div: BigInt, mod: BigInt ) {
  require(div * b + mod == a)
  require(b != 0)

  def isValid: Boolean = div * b + mod == a
  def isFinal: Boolean = if (b > 0) mod < b && mod >= 0 else mod < -b && mod >= 0
  def solve: Div = if (this.isFinal) this else ( if (mod > 0) reduceMod else increaseMod )

  def reduceMod: Div = {
    require(mod >= 0)
    decreases(mod)

    if isFinal then this else (if (b > 0) ModLessB else ModPlusB).reduceMod
  }.ensuring(res => res.isFinal && res.isValid)

  def increaseMod: Div = {
    val absB = if (b > 0) b else -b
    require(mod < 0)
    decreases(-mod)

    if isFinal this else (if (b > 0) ModPlusB else ModLessB).increaseMod
  }.ensuring(res => res.isFinal && res.isValid)

  def ModPlusB: Div = Div(a, b, div - 1, mod + b)
  def ModLessB: Div = Div(a, b, div + 1, mod - b)

  override def equals(obj: Any): Boolean = {
    obj match {
      case that: Div =>
        ( that.a == this.a &&
          that.b == this.b &&
          that.div == this.div &&
          that.mod == this.mod ) ||
          ( that.solve == this.solve )
      case _ => false
    }
  }
}
```

### Creating the Division and Module Operations

As we can see in the class [Calc](./src/main/scala/v1/Calc.scala),
we can define the division and module operations by extracting
these properties from the solved $Div$ as follows:

https://github.com/thiagomata/prime-numbers/blob/restart/src/main/scala/v1/Calc.scala#L7-L24

```scala
  def div(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    check(a == 0 * b + a)
    val result = Div(a, b, 0, a)
    val solved = result.solve
    solved.div
  }

  def mod(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    check(a == 0 * b + a)
    val result = Div(a, b, 0, a)
    val solved = result.solve
    solved.mod
  }
```
## Some Important Properties of Modulo and Division

### Trivial Case

If the dividend is smaller than the divisor, the result of the modulos operation should be the dividend value and the division result should be zero.

```math
\displaylines{ \\
\forall a,b \in \mathbb{N}, \text{ and } b \neq 0 \\
a < b \implies \\
a \text{ mod } b = a \text{ and } \\
a \text{ div } b = 0 \\
}
```

We can check that since $Div(a, b, 0, a)$ is the final solution for the division operation.
That verification is available in [ModSmallDividend](./src/main/scala/v1/div/properties/ModSmallDividend.scala) and simplified below:

```scala
def modSmallDividend(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(b > a)
    require(a >= 0)
    val x = Div(a, b, 0, a)
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
\displaylines{ \\
\forall n \in \mathbb{N}, \\
\text{ where } n \neq 0 \\
n \text{ mod } n = 0 \text{ and } \\
n \text{ div } n = 1 \\
}
```


We can prove this property using the recursive definition of the division and module operations. 
As the following simplified version of the 
[long proof](./src/main/scala/v1/div/properties/ModIdentity.scala#longProof) code example:

```scala
  def longProof(n: BigInt): Boolean = {
    require(n != 0)
    check(!Div(a = n, b = n, div = 0, mod = n).isFinal)

    if (n > 0) {
      check(
        Div(a=n, b=n, div=0, mod=n).solve ==
        Div(a=n, b=n, div=0, mod=n).reduceMod.solve ==
        Div(a=n, b=n, div=0, mod=n).ModLessB.reduceMod ==
        Div(a=n, b=n, div=1, mod=0).reduceMod ==
        Div(a=n, b=n, div=1, mod=0)
      )
      // since
      check(Div(a=n, b=n, div=1, mod=0).isFinal)
    } else {
      check(
        Div(a=n, b=n, div=0, mod=n).solve ==
        Div(a=n, b=n, div=0, mod=n).increaseMod.solve ==
        Div(a=n, b=n, div=0, mod=n).ModPlusB.increaseMod ==
        Div(a=n, b=n, div=1, mod=0)
      )
      // since
      check(Div(a=n, b=n, div=1, mod=0).isFinal)
    }
    Div(a=n, b=n, div=0, mod=n).solve == Div(a=n, b=n, div=1, mod=0)
  }.holds
```

But we don't need to manually do all these transformations.
Scala Stainless can verify that property holds in 
[ModIdentity](./src/main/scala/v1/div/properties/ModIdentity.scala) 
with no issues as follows:

```scala
  def modIdentity(a: BigInt): Boolean = {
    require(a != 0)
    Calc.mod(a, a) == 0
  }.holds
```

Similary, in the next sections, 
we will prove other properties of the division and module operations 
using only the amount of evidences required to Scala Stainless to verify 
that they hold.

### Addition

```math
\displaylines{ \\
\forall a,b,div,mod \in \mathbb{Z}, \\
\text{ where } a = \text{div} \cdot b + \text{mod}, \quad b \neq 0 \\ 
Div(a,b, div + 1, mod - b).solve = Div(a,b, div, mod).solve \\
Div(a,b, div - 1, mod + b).solve = Div(a,b, div, mod).solve \\
\therefore \\
a \text{ mod } b = (a + b) \text{ mod } b = (a - b) \text{ mod } b \\
1 + (a \text{ div } b) = (a + b) \text{ div } b \\
1 - (a \text{ div } b) = (a - b) \text{ div } b \\
}
```

As proved in [MoreDivLessMod](./src/main/scala/v1/div/properties/DivModAdditionAndMultiplication.scala#MoreDivLessMod) 
and [LessDivMoreMod](./src/main/scala/v1/div/properties/DivModAdditionAndMultiplication.scala#LessDivMoreMod) 
and shown in a simplified version in the code below, the division result is the same for the same dividend and divisor, 
regardless of the div and mod values, as long $a = b \cdot div + mod$.

```scala
  def MoreDivLessMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    val div1 = Div(a, b, div, mod)
    val div2 = Div(a, b, div + 1, mod - b)

    if (div1.isFinal) check(!div2.isFinal && div2.solve == div1.solve)
    if (div2.isFinal) check(!div1.isFinal && div1.solve == div2.solve)

    if (div1.mod < 0) {
      check(div1.solve == div1.increaseMod)
      if (b > 0) check(div2.solve == div2.increaseMod == div1.increaseMod == div1.solve)
      else check(div1.solve == div1.increaseMod == div2.solve)
    }
    if (div1.mod > 0 && ! div1.isFinal && ! div2.isFinal) {
      if (b > 0 ) {
        check(div2.mod < div1.mod)
        check(div1.solve == div1.reduceMod == div2.solve)
      } else {
        check(div2.mod > div1.mod)
        check(div2.solve == div2.reduceMod == div1.solve)
      }
    }
    check(div1.solve == div2.solve)
    Div(a,b, div + 1, mod - b).solve.mod == Div(a,b, div, mod).solve.mod
  }.holds

  def LessDivMoreMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)

    check(a == div * b + mod)
    check(a == (div - 1) * b + (mod + b))
    MoreDivLessMod(a, b, div - 1, mod + b)

    Div(a, b, div, mod).solve == Div(a, b, div - 1, mod + b).solve
  }.holds

```

### Adding or Removing Multiples of Divisor

As a directly consequence of these properties, we can extend the Div with the following properties:

```math
\displaylines{ \\
\forall \text{ } m \in \mathbb{N}, \text{ where }  \\
a = b \cdot div + mod \\
\therefore \\
Div(a,b, div + m, mod - m * b).solve = Div(a,b, div, mod).solve \\
Div(a,b, div - m, mod + m * b).solve = Div(a,b, div, mod).solve \\
\therefore \\
mod(a + m \cdot b, b) = mod(a, b) \\
div(a + m \cdot b, b) = div(a, b) + m \\
mod(a - m \cdot b, b) = mod(a, b) \\
div(a - m \cdot b, b) = div(a, b) - m \\
}
```

### Unique Remainder

There is only one single remainder value for every $a, b$ pair.

```math
\displaylines{ \\
\forall a, b \in \mathbb{Z}, \\
\exists ! \text{ remainder } r \\
\text{ such that } \\
0 \leq r < |b|  \\
\text{ and }  \\
a = \left\lfloor \frac{a}{b} \right\rfloor \cdot b + r \\
}
```

in other words, two $Div$ instances with the same dividend $a$ and divisor $b$ will have the same solution.

```math
\displaylines{ \\
\forall a, b,divX, modX, divY, modY \in \mathbb{N}, \\ 
\text{where } b \neq 0 \text{, } \\
a = b \cdot divX + modX \text{ and } \\
a = b \cdot divX + modY \text{ then } \\
Div(a, b, divX, modX).solve = Div(a, b, divY, modY).solve \\
}
```

For every $a, b$ pair, with any $divX, modX, divY, modY$, there is always the same and single solution for the division operation.
That is proved in the [unique remainder property](./src/main/scala/v1/div/properties/ModIdempotence.scala#44) as simplified below:


```scala
def modUnique(a: BigInt, b: BigInt, divx: BigInt, modx: BigInt, divy: BigInt, mody: BigInt): Boolean = {
    require(divx * b + modx == a)
    require(divy * b + mody == a)

    val x = Div(a, b, divx, modx)
    val y = Div(a, b, divy, mody)

    if (divx == divy) {
      check(modx == mody)
      check(x == y)
    }
    if (divx < divy) {
      check(modx > mody)
      val next =  Div(a, b, divx + 1, modx - b)
      check(x.solve == next.solve)
      modUnique(a, b, divx + 1, modx - b, divy, mody)
    }
    if (divx > divy) {
      check(modx < mody)
      val next =  Div(a, b, divx - 1, modx + b)
      check(x.solve == next.solve)
      modUnique(a, b, divx - 1, modx + b, divy, mody)
    }
   check(x.solve == y.solve)
   Div(a, b, divx, modx).solve == Div(a, b, divy, mody).solve
}.holds
```

### Modulo Idempotence

```math
\displaylines{ \\
\forall a,b \in \mathbb{Z}, \\
\text{ where } b \neq 0 \\
a \text{ mod } b = ( a \text{ mod } b ) \text{ mod } b \\
}
```

The proof of the modulo idempotence property is available in the [ModIdempotence](./src/main/scala/v1/div/properties/ModIdempotence.scala) as follows:
```scala
  def modIdempotence(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(a >= 0)

    val div = Div(a, b, 0, a)
    val absB = if (b < 0) -b else b

    val solved = div.solve
    check(solved.isFinal)
    check(solved.b == div.b)
    check(solved.a == div.a)
    check(absB > 0)
    check(solved.mod < absB)
    check(solved.mod >= 0)

    val result = solved.mod
    check(result <= a)
    check(result < absB)
    check(result == Calc.mod(a, b))

    check(Calc.mod(result, b) == result)
    check(Calc.mod(a, b) == Calc.mod(result, b))
    Calc.mod(a, b) == Calc.mod(Calc.mod(a, b), b)
  }.holds
```

### Distributivity over Addition and Subtraction

```math
\displaylines{ \\
\forall a,b,c \in \mathbb{Z}, \\
\text{ where } b \neq 0 \\
( a + c ) \text{ mod } b = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b \\
( a + c ) \text{ div } b = a \text{ div } b + c \text{ div } b + ( a \text{ mod } b + c \text{ mod } b ) \text{ div } b \\
( a - c ) \text{ mod } b = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b \\
( a - c ) \text{ div } b = a \text{ div } b - c \text{ div } b + ( a \text{ mod } b - c \text{ mod } b ) \text{ div } b \\
}
```

These properties are proved in the [ModOperations](./src/main//scala/v1/div/properties/ModOperations.scala),
as simplified as follows:

```scala
 def modAdd(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val absB = if (b < 0) -b else b

    val x = Div(a, b, 0, a)
    val solvedX = x.solve
    check(solvedX.mod < absB)
    check(solvedX.a == a && solvedX.b == b)
    check(solvedX.a == solvedX.b * solvedX.div + solvedX.mod) // by definition
    check(solvedX.a - solvedX.b * solvedX.div == solvedX.mod) // transposing solvedX.b * solvedX.div to the left side

    val y = Div(c, b, 0, c)
    val solvedY = y.solve
    check(solvedY.mod < absB)
    check(solvedY.a == c && solvedY.b == b)
    check(solvedY.a == solvedY.b * solvedY.div + solvedY.mod) // by definition
    check(solvedY.a - solvedY.b * solvedY.div == solvedY.mod) // transposing solvedY.b * solvedY.div to the left side

    val xy = Div(a + c, b, 0, a + c) // xy is the division of a + c by b
    val solvedXY = xy.solve
    check(solvedXY.mod < absB)
    check(solvedXY.a == a + c)
    check(solvedXY.b == b)
    check(solvedXY.a == solvedXY.b * solvedXY.div + solvedXY.mod)
    check(a + c == b * solvedXY.div + solvedXY.mod) // by definition

    val z = Div(solvedX.mod + solvedY.mod, b, 0, solvedX.mod + solvedY.mod)
    check(z.a == z.b * z.div + z.mod) // by definition
    check(z.mod == solvedX.mod + solvedY.mod)

    val solvedZ = z.solve
    check(solvedZ.mod < absB)
    check(modUniqueDiv(z, solvedZ))
    check(z.solve.mod == solvedZ.mod)

    check(solvedX.mod + solvedY.mod == b * solvedZ.div + solvedZ.mod)
    check(solvedX.a - solvedX.b * solvedX.div + solvedY.a - solvedY.b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a - b * solvedX.div + c - b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a + c == b * solvedZ.div + b * solvedX.div + b * solvedY.div + solvedZ.mod) // transposing b * solvedX.div + b * solvedY.div to the left side

    val bigDiv = solvedZ.div + solvedX.div + solvedY.div
    check(a + c == b * bigDiv + solvedZ.mod)

    val w = Div(a + c, b, bigDiv, solvedZ.mod) // is valid since a + c = b * bigDiv + solvedZ.mod
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
    check(modUniqueDiv(w, xy))
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
using the recursive definition of the division and modulo operations.
We used the Scala Stainless tool to verify these properties.
The properties proved in this article, with available proofs in the source code, are:

```math
\displaylines{ \\
\forall a, b, div \text{ and } mod \in \mathbb{Z}, \\
\text{where } b \neq 0 \\
}
```
```math
\begin{align*}
a < b \implies a \text{ mod } b & = a \\
a < b \implies a \text{ div } b &= 0 \\
b \text{ mod } b & = 0 \\
b \text{ div } b & = 1 \\
a \text{ mod } b & = ( a \text{ mod } b ) \text{ mod } b \\
( a + c ) \text{ mod } b & = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b \\
( a + c ) \text{ div } b & = a \text{ div } b + c \text{ div } b + ( a \text{ mod } b + c \text{ mod } b ) \text{ div } b \\
( a - c ) \text{ mod } b & = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b \\
( a - c ) \text{ div } b & = a \text{ div } b - c \text{ div } b + ( a \text{ mod } b - c \text{ mod } b ) \text{ div } b \\
\end{align*}
```
