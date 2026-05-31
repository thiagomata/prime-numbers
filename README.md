# Prime Numbers

This project uses formal verification to prove properties related to integers,
division, modulo, lists, cycles, and integrals using recursive, from-scratch 
constructions grounded in a zero-prior-knowledge methodology.
The project is written in Scala and uses the Stainless library to prove theorems.

## Note

This project was initially created using Dafny,
but we decided to switch to Stainless because of the better support for Scala.

This rewriting process is still ongoing.

## Proved Properties

### Division and Modulo Properties

The article [Proving Properties of Division and Modulo using Formal Verification](./articles/modulo.md) describes how the current code verifies the following theorems:

```math
\begin{aligned}
\forall \text{ } a, b, c, m & \in ℤ : b \neq 0 \\
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
```math
\begin{aligned}
\forall \text{ } a \in ℕ_0,\ b & \in ℕ \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ mod } b = 0 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ mod } b = (a \text{ mod } b) + 1 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ div } b = (a \text{ div } b) + 1 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ div } b = a \text{ div } b \\
\end{aligned}
```

### List Properties

The article [Using Formal Verification to Prove Properties of Lists Recursively Defined](./articles/list.md)
defines and constructs immutable finite lists of <code>BigInt</code> values
from scratch, relying only on recursion and core type constructs. 

```math
\begin{aligned}
L_{e} & \in 𝕃 \\
L_{e} & = [] \\
\end{aligned}
```

```math
\begin{aligned}
&\text{ head } &\in 𝕊 \\
&\text{ tail } &\in 𝕃 \\
&L_{node}(\text{head}, \text{tail}) \in 𝕃_{node} \\
\end{aligned}
```
```math
\begin{aligned}
&𝕃 &= \{ L_e \}  \cup \{ L_{node}(\text{head}, \text{tail}) &\mid \text{head} \in 𝕊,\ \text{tail} \in 𝕃 \} \\
\end{aligned}
```

```math
\begin{aligned}
L = [x_0, x_1, \dots, x_{n-1}] \in 𝕊^n \\
\end{aligned}
```

```math
\begin{aligned}
& &\text{size}(L) &:= \begin{cases}
0 & \text{ if } L = L_{e} \\\
1 + \text{size}(tail(L)) & \text{otherwise} \\
\end{cases} \\
& &sum(L) &:= \begin{cases}
0 & \text{if } L = L_e \\
head(L) + sum(tail(L)) & \text{otherwise} \\
\end{cases} \\
|L| > 0 &\implies &\text{last}(L) &:= \begin{cases}
\text{head}(L) & \text{if } |L| = 1 \\
\text{last}(\text{tail}(L)) & \text{otherwise} \\
\end{cases} \\
|L| > 0 &\implies &\text{slice}(L, f, t) &:=  \begin{cases}
[ L_j ] & \text{if } f = t \\
\text{slice}(L, f, t - 1) ⧺ [ L_t ] & \text{if } f < t \\
\end{cases}
\forall \ f, t \in ℕ_0 \text{ where } 0 \leq f \leq t \\
& &A ⧺ B &:= \begin{cases}
B & \text{if } A = L_e \\
L_{node}(head(A), tail(A) ⧺ B) & \text{otherwise} \\
\end{cases}
\forall \ L, A, B \in  𝕃 \\
\end{aligned}
```

From these definitions, it mathematically proves and formally verifies the following properties of lists:

```math
\begin{aligned}
&\forall\, L, A, B \in  𝕃,\quad &\forall\, v \in 𝕊,\quad &\forall\, i, f, t \in ℕ_0 \\
\end{aligned}
```
```math
\begin{aligned}
f \leq t, \quad 0 \leq i < |L|\\
\\
\end{aligned}
```
```math
\begin{aligned}
&|L| &> 0 &\implies \text{tail}(L) &= &L[x_1, x_2, \dots, x_{n-1}] \quad &\text{[Tail Identity]} \\
&|L| &> 0 &\implies L_{0} &= &\text{ }\text{head}(L) \quad &\text{[Head Identity]} \\
&|L| &> 0 &\implies L_{|L|-1} &= &\text{ }\text{last}(L) \quad &\text{[Last Element Identity]} \\
&|L| - 1 &> i > 0 &\implies L_i &= &\text{ }\text{tail}(L)_{i-1} \quad &\text{[Access Tail Shift Left]} \\
&|L| - 2 &> i > 1 \text{ } &\implies \text{tail}(L)_i &= &L_{i+1} \quad &\text{[Access Tail Shift Right]} \\
\end{aligned}
```
```math
\begin{aligned}
&|L| &= &\text{size}(L)                        \quad &\text{[Size Identity]} \\
&\sum L &= &\text{sum}(L)                      \quad &\text{[Sum matches Summation]} \\
&\sum ([v] ⧺ L) &= &v + \sum L                 \quad &\text{[Left Append Preserves Sum]} \\
&\sum (A ⧺ B) &= &\sum A + \sum B              \quad &\text{[Sum over Concatenation]} \\
&\sum (A ⧺ B) &= &\sum (B ⧺ A)                 \quad &\text{[Commutativity of Sum over Concatenation]} \\
&L[f \dots t] &= &L[f \dots {(t - 1)}] ⧺ [L_t] \quad &\text{[Slice Append Consistency]} \\
\end{aligned}
```

### Integral Properties

Similarly, the article [Formal Verification of Discrete Integration Properties from First Principles](./articles/integral.md)
defines and constructs bounded discrete integrals of <code>BigInt</code> values
from scratch, relying only on recursion and core type constructs. 

$$
\begin{aligned}
I &= [v_0, v_1, \dots, v_{n-1}] = \text{Integral}(L, init) \\
n &= |L| \\
k &\in [0, n - 1]
\end{aligned}
$$

```math
\begin{aligned}
&I_k &:= &\begin{cases}
L_0 + init & \text{if } k = 0 \\
\text{Integral}(\text{tail}(L),\ \text{head}(L) + init)_{(k - 1)} & \text{if } k > 0 \\
\end{cases} \\
&acc &:= &\begin{cases}
L_e & \text{if } L = L_e \\
\text{acc}(\text{Integral}(\text{tail}(L),\ \text{head}(L) + init)) & \text{otherwise} \\
\end{cases} \\
\end{aligned}
```

From these definitions, it mathematically proves and formally verifies the following properties related to discrete integrals:

```math
\begin{aligned}
 I_0 &= x_0 + init & \text{[Head Value Matches Definition]} \\
 I_k &= init + \sum_{i=0}^k x_i & \text{[Integral Equals Sum Until Position]} \\
 I_{n-1} &= init + \sum_{i=0}^{n-1} x_i & \text{[Final Element Equals Full Sum]} \\
 I_{p+1} - I_p &= x_{p+1} & \text{[Incremental Change Matches List]} \\
 I_k &= acc_k & \text{[Element Consistency]} \\
  \text{last}(I) &= acc_{n-1} = I_{n-1} & \text{[Integral-Accumulation Last Agreement]} \\
 acc_{p+1} - acc_p &= x_{p+1} & \text{[Integral-Accumulation Delta Consistency]} \\
 |acc| &= |L| & \text{[Integral-Accumulation Size Agreement]} \\
\end{aligned}
```

### Cycle Properties

The article [Using Formal Verification to Prove Properties of Unbound Lists](./articles/cycle.md)
defines cycles as unbounded lists generated by repeating a finite non-empty list.
It proves the equivalence between recursive and modulo-based definitions of the same cycle.

```math
\begin{aligned}
L &= [v_0, v_1, \dots, v_{n-1}] \in \mathbb{N}_0^n,\quad n = |L|,\quad n > 0 \\
\text{Cycle}(L) &= [v_0, v_1, \dots, v_{n-1}, v_0, v_1, \dots] \\
\text{ModCycle}_i &= L_{i \text{ mod } n} \\
\end{aligned}
```

From these definitions, it mathematically proves and formally verifies the following properties:

```math
\begin{aligned}
\text{ModCycle}_i &= \text{RecCycle}_i = \text{Cycle}_i
\quad &\text{[Cycle Equivalence]} \\
\text{Cycle}_{i + n \cdot m} &= \text{Cycle}_i
\quad &\text{[Value Match After Many Loops]} \\
\text{Cycle}_{i + n \cdot m_1} &= \text{Cycle}_{i + n \cdot m_2}
\quad &\text{[Two Multiples of Cycle Size]} \\
\text{Cycle}_i &= L_{i \text{ mod } n}
\quad &\text{[Propagate Modulo from Value to Cycle]} \\
\end{aligned}
```

### Cycle Integral Properties

The article [Formal Verification of Cycle Integral Properties from First Principles](./articles/integral-cycle.md)
extends the list, modulo, integral, and cycle foundations to define integrals over repeating cycles.
A cycle integral accumulates values from a finite list as if the list repeated forever.

```math
\begin{aligned}
L &= [v_0, v_1, \dots, v_{n-1}],\quad n = |L|,\quad n > 0 \\
T &= \sum_{j=0}^{n-1} v_j \\
I &= \text{Integral}(L, 0) \\
\text{CycleIntegral}(L, init)_i
&= (i \text{ div } n) \cdot T + I_{i \text{ mod } n} + init \\
\end{aligned}
```

From these definitions, it mathematically proves and formally verifies the following properties:

```math
\begin{aligned}
\text{ClassicCycleIntegral}(L, init)_i
&= \text{RecursiveCycleIntegral}(L, init)_i
= \text{ModuloCycleIntegral}(L, init)_i
\quad &\text{[Equivalence of Definitions]} \\
\text{CycleIntegral}(L^{(x)}, init)_i
&= \text{CycleIntegral}(L, init)_i
\quad &\text{[Invariance by Concatenation]} \\
\text{CycleIntegral}(L, init)_{i+1}
&= \text{CycleIntegral}(L', init')_i
\quad &\text{[Right Index Shift]} \\
\text{CycleIntegral}(L, init)_{i+1}
&= \text{CycleIntegral}(L'', init'')_i
\quad &\text{[Left Index Shift]} \\
\end{aligned}
```

## Running the Formal Verification

### Running Locally

- Scala 3.4.0
- Just 1.16.0
- JEnv 0.5.7
- Java 21
- Stainless 0.9.8

```bash
just verify
```
### Running on Docker

- Just 0.5.7
- docker 20.10.16

```bash
just verify-docker
```
