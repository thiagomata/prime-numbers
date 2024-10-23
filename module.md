# Division and Module

Given integers $dividend$ and $divisor$ where $divisor \neq 0$, the division algorithm determines integers $quotient$ and $remainder$ such that:

$$
\forall \text{ } dividend, divisor \in \mathbb{N}, \text{ where } divisor\neq 0 
$$

$$
\exists ! \
\text{quotient} = \left\lfloor \frac{\text{dividend}}{\text{divisor}} \right\rfloor \implies  
$$

$$
dividend = divisor \cdot quotient + \text{remainder}, \text { where } 0 \leq \text{remainder} < |b|, 
$$

$$
dividend \text{ mod } divisor = remainder, 
$$

$$
dividend \text{ div } divisor = quotient. 
$$

## Recursive Definition

Some properties of the division and module can be proved using the 
recursive definition of the division and module operations.

The recursive definition of the division and module operations are:

We define $Div(a, b, div, mod)$ such that:
$$
a = \text{div} \cdot b + \text{mod}, \quad b \neq 0
$$
and the remainder $mod$ satisfies:
$$
\begin{cases}
0 \leq \text{mod} < b & \text{if } b > 0, \\
0 \leq \text{mod} < -b & \text{if } b < 0.
\end{cases}
$$

### Base Case:
If $0 \leq \text{mod} < |b|$, then the solution is:
$$
\text{Div}(a, b, \text{div}, \text{mod}) = (a, b, \text{div}, \text{mod}).
$$


### Recursive Formula:
$$
\text{Div}(a, b, \text{div}, \text{mod}) =
\begin{cases}
\text{Div}(a, b, \text{div}, \text{mod}) & \text{if } 0 \leq \text{mod} < |b|, \\
\text{Div}(a, b, \text{div} + \text{sign}(b), \text{mod} - |b|) & \text{if } \text{mod} \geq |b|, \\
\text{Div}(a, b, \text{div} - \text{sign}(b), \text{mod} + |b|) & \text{if } \text{mod} < 0.
\end{cases}
$$


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

As we can see in the class [Calc](./src/main/scala/v1/Calc.scala), we can define the division and module operations as follows:

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
## Some Important Properties

### Modulo and Div Identity

The modulo of every number by itself is zero and the division of every number by itself is one.

$$
\forall n \in \mathbb{N}, \\
\text{ where } n \neq 0 \\
n \text{ mod } n = 0 \text{ and } \\
n \text{ div } n = 1
$$


We can prove this property using the recursive definition of the division and module operations. As the following simplified version of the [long proof](./src/main/scala/v1/div/properties/ModIdentity.scala#longProof) code example:

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
Scala Stainless can verify that property holds in [ModIdentity](./src/main/scala/v1/div/properties/ModIdentity.scala) with no issues as follows:

```scala
  def modIdentity(a: BigInt): Boolean = {
    require(a != 0)
    Calc.mod(a, a) == 0
  }.holds
```

Similary, in the next sections, we will prove other properties of the division and module operations using only the amount of evidences required to Scala Stainless to verify that they hold.

### Modulo Addition

$$
Div(a,b, div + 1, mod - b) = Div(a,b, div, mod) \\
Div(a,b, div - 1, mod + b) = Div(a,b, div, mod)
$$

As proved in [MoreDivLessMod](./src/main/scala/v1/div/properties/DivModAdditionAndMultiplication.scala#MoreDivLessMod) and [LessDivMoreMod](./src/main/scala/v1/div/properties/DivModAdditionAndMultiplication.scala#LessDivMoreMod), we can see that the division operation is the same for the same dividend and divisor, regardless of the div and mod values, as long $a = b \cdot div + mod$.

### Module Multiplication

As a directly consequence of these properties, we can extend the Div with the following properties:

$$
\forall \text{ } m \in \mathbb{N}, \text{ where }  \\
a = b \cdot div + mod \therefore \\
Div(a,b, div + m, mod - m * b) = Div(a,b, div, mod) \\
Div(a,b, div - m, mod + m * b) = Div(a,b, div, mod)
$$

### Unique Remainder Property in Integer Division

There is only one single remainder value for every $a, b$ pair.

$$
\forall a, b \in \mathbb{N}, \exists ! \text{ remainder } r \text{ such that } 0 \leq r < |b| \text{ and } a = \left\lfloor \frac{a}{b} \right\rfloor \cdot b + r 
$$

in other words:

$$
\forall a, b,divX, modX, divY, modY \in \mathbb{N}, \\ 
\text{where } b \neq 0 \text{, } \\
a = b \cdot divX + modX \text{ and } \\
a = b \cdot divX + modY \text{ then } \\
Div(a, b, divX, modX) = Div(a, b, divY, modY)
$$

For every $a, b$ pair, with any $divX, modX, divY, modY$, there is always the same and single solution for the division operation. That is proved in the [unique remainder property](./src/main/scala/v1/div/properties/ModIdempotence.scala#44) as simplified below:


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

### Modulo Addition

Adding the divisor to the dividend do not change the mod result.

$$
\forall a,b \in \mathbb{N}, (a + b) \text{ mod } b = a \text{ mod } b
$$

### Modulo Multiplication

Recursively applying the Modulo Addition Property, we can prove that:

$$
\forall a,b,m \in \mathbb{N}, (a + m \cdot b) \text{ mod } b = a \text{ mod } b
$$

### Div Addition Propert

Adding the divisor to the dividend increase the div result by one.

$$
\forall a,b \in \mathbb{N}, (a + b) \text{ div } b = (a \text{ div } b ) + 1
$$


Therefore:

$$
\forall a,b,m \in \mathbb{N}, (a + m \cdot b) \text{ div } b = (a \text{ div } b ) \cdot m
$$


### Modulo Result for Small Dividend

If the dividend is smaller than the divisor, the result of the modulos operation should be the dividend value.

$$
\forall a,b \in \mathbb{N}, \text{ where } a < b \implies a \text{ mod } b = a
$$

### Modulo Idempotence

$$
\forall a,b \in \mathbb{N}, a \text{ mod } b = ( a \text{ mod } b ) \text{ mod } b
$$

