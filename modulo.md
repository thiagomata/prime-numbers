# Proving Properties of Division and Modulo using Formal Verification

## Abstract

<p style="text-align: justify">
The division and modulo operations are fundamental in mathematics and computer science,
 especially in areas such as number theory, cryptography, and algorithm design. 
In this article, we define these operations from scratch using a recursive formulation,
 without relying on built-in semantics or standard library behavior — a zero-prior-knowledge approach. 
We formally verify key properties such as unique remainder, modulo idempotence, and distributivity
 using the Stainless verification system. 
All properties are expressed and proved within a minimal framework using only elementary arithmetic,
 recursion, and pure Scala code.
This work bridges mathematical foundations and executable verification, offering a self-contained, verifiable
 treatment of modular arithmetic.
 </p>

## Introduction

Integer division and modulo operations are central tools in discrete mathematics, number theory, and algorithms. 
While their properties are well known, rigorous formalization and verification—particularly via recursive definitions—
offer an interesting alternative to the traditional axiomatic model.

This work formalizes these operations recursively, demonstrates fundamental properties, and uses the Scala Stainless 
tool to ensure that these properties are formally verifiable.

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
It goals is to make available a set of lemmas and proofs that can be verified and used as a base to prove other 
properties related to the division and modulo operations.>
Therefore, the implementation is optimized to correctness and not to performance.

The use of BigInt in the implementation focused on unbounded integers, without the need to worry about overflow or 
underflow issues. 
But, they are still constrained by the memory available in the system. 
Similarly, some lemmas and proofs are using the recursive definition of the division and modulo operations, which could 
trigger a stack overflow for large numbers. Those issues do not invalidate the mathematical properties proved in this 
article, which are the main focus of this article.

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

The Recursive definition on Scala is available in the [DivMod.scala](
./src/main/scala/v1/div/DivMod.scala
).


## DivMod Solution Invariance Under Linear Shift

```math
\begin{aligned}
\forall a, b, div, mod \in \mathbb{Z} : a & = \text{div} \cdot b + \text{mod}, b \neq 0 \\ 
a = div * b + mod & = (div + 1) * b + ( mod − b ) = (div - 1 ) * b + ( mod + b ) \\
DivMod(a, b, div + 1, mod - b).solve & = DivMod(a, b, div, mod).solve \\
DivMod(a, b, div - 1, mod + b).solve & = DivMod(a, b, div, mod).solve \\
\end{aligned}
```

As proved in the [proof for positive shift](
  ./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#assertDivModWithMoreDivAndLessModeSameSolution
) and [proof for negative shift](./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#assertDivModWithLessDivAndMoreModSameSolution).


### Creating the Division and Module Operations

Using the DivMod class we defined, in the class [Calc](
./src/main/scala/v1/Calc.scala
), the division and module operations by extracting these properties from the solved $DivMod$.

## Some Important Properties of Modulo and Division

### Trivial Case

If the dividend is smaller than the divisor, the result of the modulos operation should be the dividend value and the division result should be zero.

```math
\begin{aligned}
& \forall \text{ } a, b \in \mathbb{N} : b \neq 0 \\
& a < b \implies a \text{ mod } b & = a \\
& a < b \implies a \text{ div } b & = 0 \\
\end{aligned}
```

We can check that since $DivMod(a, b, 0, a)$ is the final solution for the division operation.
That verification is available in [mod small dvidend proof](./src/main/scala/v1/div/properties/ModSmallDividend.scala).

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

But we don't need to manually do all these transformations.
Scala Stainless is capable of verifying that property holds in 
[ModIdentity](./src/main/scala/v1/div/properties/ModIdentity.scala) 
with no issues as follows:

```scala
  def modIdentity(a: BigInt): Boolean = {
    require(a != 0)
    Calc.mod(a, a) == 0
  }.holds
```

Similary, in the next sections, we will prove other properties of the division and module operations using only the amount of evidences required to Scala Stainless to verify that they hold.

### Quotient Invariance Under Linear Shift

```math
\begin{aligned}
\forall \text{ } a, b, div, mod \in \mathbb{Z} & : b \neq 0, a = b \cdot div + mod \\
mod(a + b, b) & = mod(a, b) \\
div(a + b, b) & = div(a, b) + 1 \\
mod(a - b, b) & = mod(a, b) \\
div(a - b, b) & = div(a, b) - 1 \\
\end{aligned}
```

Quotient Invariance Under Linear Shift proof is available for the [positive case](
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#APlusBSameModPlusDiv
) and [negative case](
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#ALessBSameModDecreaseDiv
).

### Quotient Invariance Under Linear Shift by Multipler

As a directly consequence of these properties, we can also prove that:

```math
\begin{aligned}
\forall \text{ } a, b, div, mod, m \in \mathbb{Z} & : b \neq 0, a = b \cdot div + mod \\
mod(a + m \cdot b, b) & = mod(a, b) \\
div(a + m \cdot b, b) & = div(a, b) + m \\
mod(a - m \cdot b, b) & = mod(a, b) \\
div(a - m \cdot b, b) & = div(a, b) - m \\
\end{aligned}
```

Quotient Invariance Under Linear Shift by Multiplier proof is available for the [positive case](
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#APlusMultipleTimesBSameMod
) and [negative case](
./src/main/scala/v1/div/properties/AdditionAndMultiplication.scala#ALessMultipleTimesBSameMod
).

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
That is proved in the [proof of unique remainder property](
./src/main/scala/v1/div/properties/ModIdempotence.scala#modUnique
).

### Modulo Idempotence

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b & = ( a \text{ mod } b ) \text{ mod } b \\
\end{aligned}
```

The proof of the modulo idempotence property is available in the [mod idempotence proof](./src/main/scala/v1/div/properties/ModIdempotence.scala#modIdempotence).

### Distributivity over Addition

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a + c ) \text{ mod } b & = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b \\
( a + c ) \text{ div } b & = a \text{ div } b + c \text{ div } b + ( a \text{ mod } b + c \text{ mod } b ) \text{ div } b \\
( a +  c) \text{ mod } b & = (a \text{ mod } b) + (c \text{ mod } b) - b \cdot (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } c) \\
\end{aligned}
```

As the scala [distribution over addition proof](
./src/main//scala/v1/div/properties/ModOperations.scala#modAdd
) can be verified.

### Distribution over Subtraction

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a - c ) \text{ mod } b & = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b \\
( a - c ) \text{ div } b & = a \text{ div } b - c \text{ div } b + ( a \text{ mod } b - c \text{ mod } b ) \text{ div } b \\
( a - c ) \text{ mod } b & = (a \text{ mod } b) - (c \text{ mod } b) - b \cdot (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } c) \\
\end{aligned}
```

As the scala [distribution over subtraction proof](
./src/main//scala/v1/div/properties/ModOperations.scala#modAdd
) can be verified.

### Modular Shift Invariance under Divisible Base

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b = 0 & \implies ( a + c ) \text{ mod } b = c \text{ mod } b \\
a \text{ mod } b = 0 & \implies ( a - c ) \text{ mod } b = c \text{ mod } b \\
\end{aligned}
```

As scala [proof of invariance](
./src/main//scala/v1/div/properties/ModOperations.scala#modZeroPlusC
) can be verified.

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

As the scala [proof for the unit-step increment law](
./src/main//scala/v1/div/properties/ModOperations.scala#addOne
) can be verified.

## Conclusion

In this article, we constructed the division and modulo operations from first principles,
 using a recursive definition that avoids reliance on any built-in semantics or library
 implementations — a zero-prior-knowledge approach.
Within this minimal foundation, we proved the following set of fundamental properties and
 identities using formal verification with Scala Stainless:

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
Those properties can be verified using Scala Stainless, as available in the [Summary.scala](
 ./src/main/scala/v1/div/properties/Summary.scala
) file. The recursive formulation, combined with machine-checked proofs, ensures both correctness and
 transparency.
 
This work demonstrates how modular arithmetic can be derived, reasoned about, 
 and verified from the ground up, providing a reusable and trustworthy basis for further
 mathematical or computational development.

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