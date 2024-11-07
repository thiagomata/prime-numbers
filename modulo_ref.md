# Proving Properties of Division and Modulo using Formal Verification

<div align="justify">

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
\displaylines{ \\
\forall \text{ } dividend, divisor \in \mathbb{N}, \text{ where } divisor\neq 0  \\
\exists ! \\
\text{quotient} = \left\lfloor \frac{\text{dividend}}{\text{divisor}} \right\rfloor \implies   \\
dividend = divisor \cdot quotient + \text{remainder}, \text { where } 0 \leq \text{remainder} < |b|, \\
dividend \text{ mod } divisor = remainder, \\
dividend \text{ div } divisor = quotient. \\
}
```

## Recursive Definition

Some properties of the division and modulo can be proved using the recursive definition of the division and modulo operations.
The recursive definition of the division and modulo operations are:

```math
\displaylines{ \\
\forall a, b, div \text{ and } mod \in \mathbb{Z}, \\
\text{where } b \neq 0 \\
}
```

We define $DivMod(a, b, div, mod)$ such that:

```math
a = \text{div} \cdot b + \text{mod}
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
\displaylines{ \\
\text{DivMod.solve}(a, b, \text{div}, \text{mod}) =
\begin{cases}
\text{DivMod}(a, b, \text{div}, \text{mod}) & \text{if } 0 \leq \text{mod} < |b|, \\
\text{DivMod.solve}(a, b, \text{div} + \text{sign}(b), \text{mod} - |b|) & \text{if } \text{mod} \geq |b|, \\
\text{DivMod.solve}(a, b, \text{div} - \text{sign}(b), \text{mod} + |b|) & \text{if } \text{mod} < 0. \\
\end{cases} \\
}
```

We can see the described [recursive definition on Scala](
./src/main/scala/v1/div/DivMod.scala
), as follows:

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/DivMod.scala?plain=1#L7-L86

### Creating the Division and Module Operations

As we can see in the class [Calc](
./src/main/scala/v1/Calc.scala
), we can define the division and module operations by extracting these properties from the solved $DivMod$ as follows:

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/Calc.scala#L5-L26

## Some Important Properties of Modulo and Division

### Trivial Case

If the dividend is smaller than the divisor, the result of the modulos operation should be the dividend value and the division result should be zero.

```math
\displaylines{ \\
\forall a,b \in \mathbb{N}, \text{ and } b \neq 0 \\
a < b \implies \\
a \text{ mod } b = a \\
a \text{ div } b = 0 \\
}
```

We can check that since $DivMod(a, b, 0, a)$ is the final solution for the division operation.
That verification is available in [ModSmallDividend](./src/main/scala/v1/div/properties/ModSmallDividend.scala) and described below:

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/ModSmallDividend.scala#L9-L24

### Identity

The modulo of every number by itself is zero and the division of every number by itself is one.

```math
\displaylines{ \\
\forall n \in \mathbb{N}, \\
\text{ where } n \neq 0 \\
n \text{ mod } n = 0 \\
n \text{ div } n = 1 \\
}
```


We can prove this property using the recursive definition of the division and module operations.
As the following [long proof](
./src/main/scala/v1/div/properties/ModIdentity.scala#longProof
) code example:

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/ModIdentity.scala#L15-L42

But we don't need to manually do all these transformations.
Scala Stainless can verify that property holds in
[ModIdentity](
./src/main/scala/v1/div/properties/ModIdentity.scala
) with no issues as follows:

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/ModIdentity.scala#L10-L13

Similary, in the next sections, we will prove other properties of the division and module operations using only the amount of evidences required to Scala Stainless to verify that they hold.

### Addition

```math
\displaylines{ \\
\forall a,b,div,mod \in \mathbb{Z}, \\
\text{ where } a = \text{div} \cdot b + \text{mod}, \quad b \neq 0 \\ 
DivMod(a,b, div + 1, mod - b).solve = DivMod(a,b, div, mod).solve \\
DivMod(a,b, div - 1, mod + b).solve = DivMod(a,b, div, mod).solve \\
\therefore \\
a \text{ mod } b = (a + b) \text{ mod } b = (a - b) \text{ mod } b \\
1 + (a \text{ div } b) = (a + b) \text{ div } b \\
1 - (a \text{ div } b) = (a - b) \text{ div } b \\
}
```

As proved in [MoreDivLessMod](
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#MoreDivLessMod
) and [LessDivMoreMod](
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#LessDivMoreMod
) and shown the code below, the division result is the same for the same dividend and divisor, regardless of the div and mod values, as long $a = b \cdot div + mod$.

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#L184-L238

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#L240-L251

### Adding or Removing Multiples of Divisor

As a directly consequence of these properties, we can extend the $DivMod$ with the following properties:

```math
\displaylines{ \\
\forall \text{ } m \in \mathbb{N}, \text{ where }  \\
a = b \cdot div + mod \\
\therefore \\
DivMod(a,b, div + m, mod - m * b).solve = DivMod(a,b, div, mod).solve \\
DivMod(a,b, div - m, mod + m * b).solve = DivMod(a,b, div, mod).solve \\
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

in other words, two $DivMod$ instances with the same dividend $a$ and divisor $b$ will have the same solution.

```math
\displaylines{ \\
\forall a, b,divX, modX, divY, modY \in \mathbb{N}, \\ 
\text{where } b \neq 0 \text{, } \\
a = b \cdot divX + modX \text{ and } \\
a = b \cdot divX + modY \text{ then } \\
DivMod(a, b, divX, modX).solve = DivMod(a, b, divY, modY).solve \\
}
```

For every $a, b$ pair, with any $divX, modX, divY, modY$, there is always the same and single solution for the division operation.
That is proved in the [unique remainder property](
./src/main/scala/v1/div/properties/ModIdempotence.scala#44
) as shown below:

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/ModIdempotence.scala#L43-L75

### Modulo Idempotence

```math
\displaylines{ \\
\forall a,b \in \mathbb{Z}, \\
\text{ where } b \neq 0 \\
a \text{ mod } b = ( a \text{ mod } b ) \text{ mod } b \\
}
```

The proof of the modulo idempotence property is available in the [ModIdempotence](./src/main/scala/v1/div/properties/ModIdempotence.scala) as follows:

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/ModIdempotence.scala#L9-L31

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

These properties are proved in the [ModOperations](
./src/main//scala/v1/div/properties/ModOperations.scala
), as shown as follows:

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/ModOperations.scala#L13-L91

https://github.com/thiagomata/prime-numbers/blob/064187f9c3ac3ff226c14518b823bfe47ad473d1/src/main/scala/v1/div/properties/ModOperations.scala#L100-L105

## Conclusion

The division and module operations are fundamental in computer science and mathematics.
In this article, we have shown how to prove some properties of these operations
using the recursive definition of the division and modulo operations and formal verification on Scala Stainless,
with available proofs in the source code.

These properties are:

```math
\forall a, b, div \text{ and } mod \in \mathbb{Z}, \\
\text{where } b \neq 0 \\
```

```math
\begin{align*} \\
a >= 0 \text{ and } b > a \implies a \text{ div } b & = 0 \\
a >= 0 \text{ and } b > a \implies a \text{ mod }  b & = a \\
b \text{ mod } b               & = 0 \\
b \text{ div } b               & = 1 \\
( a + b \cdot m ) \text{ mod } b       & = a \text{ mod } b \\
( a - b \cdot m ) \text{ mod } b       & = a \text{ mod } b \\
(a \text{ mod } b) \text{ mod } b       & = a \text{ mod } b \\
(a + b) \text{ div } b         & = (a \text{ div } b) + 1 \\
(a - b) \text{ div } b         & = (a \text{ div } b) - 1 \\
(a + b \cdot m ) \text{ div } b    & = (a \text{ div } b) + m \\
(a - b \cdot m ) \text{ div } b    & = (a \text{ div } b) - m \\
(a + c) \text{ div } b         & = (a \text{ div } b) + (c \text{ div } b) + (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } b) \\
(a - c) \text{ div } b         & = (a \text{ div } b) - (c \text{ div } b) + (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } b) \\
(a + c) \text{ mod } b         & = ((a \text{ mod } b) + (c \text{ mod } b)) \text{ mod } b \\
(a - c) \text{ mod } b         & = ((a \text{ mod } b) - (c \text{ mod } b)) \text{ mod } b \\
(a + c) \text{ mod } b         & = (a \text{ mod } b) + (c \text{ mod } b) - b \cdot (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } c) \\
(a - c) \text{ mod } b         & = (a \text{ mod } b) - (c \text{ mod } b) - b \cdot (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } c) \\
\end{align*} \\
```

Those properties could be verified by the Scala Stainless as we can see in the code bellow from the [Summary.scala](
./src/main/scala/v1/div/properties/Summary.scala
) file.

https://github.com/thiagomata/prime-numbers/blob/6207ca8c867bc9ddc939939bb157cbe068f00f7a/src/main/scala/v1/div/properties/Summary.scala#L10-L70


## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
[Formal Verification - Wikipedia, 2024](https://en.wikipedia.org/wiki/Formal_verification)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Sanghavi, Alok (May 21, 2010). "What is formal verification?". EE Times Asia.

<a name="ref3" id="ref3" href="#ref3">[3]</a>
[Stainless - Program Verification, 2024](https://epfl-lara.github.io/stainless/intro.html)

</div>
