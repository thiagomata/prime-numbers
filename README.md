# Prime Numbers

This project uses formal verification to prove properties related to integers,
division, modulo, lists, cycles, and integrals using recursive, from-scratch 
constructions grounded in a zero-prior-knowledge methodology.
The project is written in Scala and uses the Stainless library to prove theorems.

## Research Vocabulary

Use the [Research Vocabulary](VOCABULARY.md) for the canonical meanings of
sieve objects, proof scope, quantifiers, empirical status, and mathematical
proof status across candidates, properties, articles, and research notes.

## Note

This project was initially created using Dafny,
but we decided to switch to Stainless because of the better support for Scala.

This rewriting process is still ongoing.

## Proved Properties

### Division and Modulo Properties

The article [Division and Modulo from Recursive Normalization](./articles/chapter2/modulo.md) describes how the current code verifies the following theorems:

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

The article [Using Formal Verification to Prove Properties of Lists Recursively Defined](./articles/chapter3/list.md)
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
0 \leq f \leq t < |L| &\implies &\text{slice}(L, f, t) &:=  \begin{cases}
[ L_j ] & \text{if } f = t \\
\text{slice}(L, f, t - 1) \mathbin{\texttt{++}} [ L_t ] & \text{if } f < t \\
\end{cases}
\forall \ f, t \in ℕ_0 \\
& &A \mathbin{\texttt{++}} B &:= \begin{cases}
B & \text{if } A = L_e \\
L_{node}(head(A), tail(A) \mathbin{\texttt{++}} B) & \text{otherwise} \\
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
0 \leq f \leq t < |L|, \quad 0 \leq i < |L|\\
\\
\end{aligned}
```
```math
\begin{aligned}
&|L| &> 0 &\implies \text{tail}(L) &= &L[x_1, x_2, \dots, x_{n-1}] \quad &\text{[Tail Identity]} \\
&|L| &> 0 &\implies L_{0} &= &\text{ }\text{head}(L) \quad &\text{[Head Identity]} \\
&|L| &> 0 &\implies L_{|L|-1} &= &\text{ }\text{last}(L) \quad &\text{[Last Element Identity]} \\
&0 &< i < |L| &\implies L_i &= &\text{ }\text{tail}(L)_{i-1} \quad &\text{[Access Tail Shift Left]} \\
&0 &\leq i < |\text{tail}(L)| &\implies \text{tail}(L)_i &= &L_{i+1} \quad &\text{[Access Tail Shift Right]} \\
\end{aligned}
```
```math
\begin{aligned}
&|L| &= &\text{size}(L)                        \quad &\text{[Size Identity]} \\
&\sum L &= &\text{sum}(L)                      \quad &\text{[Sum matches Summation]} \\
&\sum (v :: L) &= &v + \sum L                 \quad &\text{[Left Append Preserves Sum]} \\
&\sum (A \mathbin{\texttt{++}} B) &= &\sum A + \sum B              \quad &\text{[Sum over Concatenation]} \\
&\sum (A \mathbin{\texttt{++}} B) &= &\sum (B \mathbin{\texttt{++}} A)                 \quad &\text{[Commutativity of Sum over Concatenation]} \\
&L[f \dots t] &= &L[f \dots {(t - 1)}] \mathbin{\texttt{++}} [L_t] \quad &\text{[Slice Append Consistency]} \\
\end{aligned}
```

### Integral Properties

Similarly, the article [Formal Verification of Discrete Integration Properties from First Principles](./articles/chapter4/integral.md)
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

The article [Using Formal Verification to Prove Properties of Unbound Lists](./articles/chapter4/cycle.md)
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

The article [Formal Verification of Cycle Integral Properties from First Principles](./articles/chapter4/integral-cycle.md)
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
\text{CycleIntegral}(L, init)_i
&= \text{ModuloCycleIntegral}(L, init)_i
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

### Euclid's Theorem (Infinitude of Primes)

The article [Formal Verification of Euclid's Theorem on the Infinitude of Primes](./articles/chapter5/euclid-theorem.md)
proves that there are infinitely many primes using Euclid's classic construction:
given any finite list of primes, compute their primorial plus one, and show that
this number has a prime divisor not in the original list.

```math
\begin{aligned}
\text{primorial}(L) &= \prod_{i=1}^{k} p_i \\
n &= \text{primorial}(L) + 1
\end{aligned}
```

From these definitions, it mathematically proves and formally verifies the following theorem:

```math
\begin{aligned}
\forall\ \text{primes} \in \text{List[Prime]},\ \text{primes.nonEmpty} &\implies
\exists\ p \notin \text{primes} : \text{isPrime}(p)
\quad &\text{[Euclid's Theorem]} \\
\end{aligned}
```

The same chapter also verifies two downstream families that are important for
the later sieve construction: the Euclid-constructed prime is strictly greater
than the current complete prime-prefix head, and the smallest divisor of a
composite number is a prime divisor at most the square root of that number.

```math
\begin{aligned}
\text{allPrimesSoFar}(P) &\implies
\text{newPrimeFromEuclid}(P) > \text{head}(P)
\quad &\text{[Euclid Prime Exceeds Head]} \\
\neg\text{isPrime}(n) &\implies
d = \text{findSmallestDivisor}(n, 2)
\land d^2 \leq n
\quad &\text{[Smallest Divisor Sqrt Bound]} \\
\neg\text{isPrime}(n) &\implies
\text{isPrime}(d) \land d \mid n
\quad &\text{[Composite Smallest Prime Divisor]} \\
\end{aligned}
```

### Sieve Foundation Properties

The codebase verifies foundational lemmas for the sieve sequence algorithm:
CycleIntegral with a unit cycle produces natural numbers, and filtering out
multiples of a prime preserves every other prime. These properties are source
backed, but they do not currently have an active standalone article.

```math
\begin{aligned}
L &= [1],\quad \text{MemCycle}(L) \text{ is the unit cycle} \\
\text{CycleIntegral}(L, init)_i &= \sum_{j=0}^{i} L_{(j \text{ mod } 1)} + init
\end{aligned}
```

From these definitions, it mathematically proves and formally verifies the following properties:

```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_i &= init + i + 1
\quad &\text{[Unit Cycle Generates Natural Numbers]} \\
b > a &\implies \text{CycleIntegral}(\text{MemCycle}([1]), init)_b > \text{CycleIntegral}(\text{MemCycle}([1]), init)_a
\quad &\text{[Strict Monotonicity]} \\
\text{isPrime}(q) \land \text{isPrime}(p) \land q \neq p &\implies q \bmod p \neq 0
\quad &\text{[Distinct Primes Coprime]} \\
\text{isPrime}(q) \land q \neq \text{filterPrime} &\implies q \bmod \text{filterPrime} \neq 0
\quad &\text{[Filter Preserves Primes]} \\
q \in \text{originalPrimes} \land \text{isPrime}(q) \land q \neq \text{filterPrime} &\implies q \in \text{filteredPrimes}
\quad &\text{[Filtered Contains All Primes]} \\
\end{aligned}
```

### Sieve Sequence Stage Properties

The article [Formal Verification of Sieve Sequence Stages and Their Transitions](./articles/chapter6/sieve-sequence.md)
defines a sieve stage as the increasing sequence of integers accepted by a
finite prefix of prime filters. It verifies that one finite period of gaps
reconstructs the infinite accepted-value sequence, and it verifies the main
transition facts used when installing the next prime filter.

```math
\begin{aligned}
A_S(v) &\implies \exists i \geq 0,\ \ell_i = v
\quad &\text{[Accepted-Value Completeness]} \\
\ell_{k+1} &> \ell_k
\quad &\text{[Strict Increase]} \\
\ell_{k+nT} &= \ell_k + nM
\quad &\text{[Block-Period Shift]} \\
I_G(k-1) &= \ell_k
\quad &\text{[Gap-Cycle Reconstruction]} \\
I_{G^{\langle h\rangle}}(k) &= I_G(k)
\quad &\text{[Repeated-Cycle Invariance]} \\
N_{\mathrm{survive}} &= T(h-1)
\quad &\text{[Exact Expanded Filtering]} \\
g'_m &= g_k
\quad\text{or}\quad
g'_m = \sum_{i=k}^{j-1} g_i
\quad &\text{[Copy Or Merge]} \\
p^+ < h^2 &\implies \ell_1 = p^+
\quad &\text{[Conditional Next Head]} \\
\end{aligned}
```

The result is a finite-stage specification and transition semantics. It does
not claim a faster sieve algorithm, and it does not by itself prove persistence
of any particular prime gap in local windows.

### Gap Dynamics And 2-Gap Properties

The article [Structural Properties and Open Boundaries of 2-Gaps in Sieve Sequences](./articles/chapter6/gap-dynamics.md)
uses the verified sieve-stage foundation to study the special case of 2-gaps.
It separates complete-period facts, which are global and structural, from the
local square-window placement problem needed to certify infinitely many twin
prime pairs.

```math
\begin{aligned}
\#\{2\text{-gaps in one complete period}\}
&=
\prod_{\substack{3 \leq r < p\\r\text{ prime}}}(r-2)
\quad &\text{[Exact Full-Period 2-Gap Count]} \\
\text{No old 2-gap} &\implies \text{no new 2-gap}
\quad &\text{[Stable Absence]} \\
\text{one new odd filter } r
&\text{ forbids exactly two copy-index classes}
\quad &\text{[Two Forbidden Classes]} \\
\#\text{surviving copies over a finite batch}
&=
\prod_{r \in \mathcal R}(r-2)
\quad &\text{[Finite-Batch Survival]} \\
x,x+2 \in [q,q^2)
\land \gcd(x(x+2), P_q)=1
&\implies x,x+2\text{ are prime}
\quad &\text{[Square-Safe Twin Certificate]} \\
\end{aligned}
```

These properties prove that 2-gaps are forced in complete periods and evolve
by exact copy/merge arithmetic. The remaining open boundary is local placement:
showing that sufficiently many of those surviving 2-gaps land inside
square-safe windows.

## Running the Formal Verification

### Running Locally

- Scala 3.4.0
- Just 1.16.0
- JEnv 0.5.7
- Java 21
- Stainless 0.9.8

The recommended project-wide verification workflow is chapter-by-chapter:

```bash
just verify-ch 1
just verify-ch 2
just verify-ch 3
just verify-ch 4
just verify-ch 5
just verify-ch 6
```

`just verify-ch N` loads source files up to chapter `N`, then verifies only
the highest requested chapter with `--functions=v1.chapterN._`. This keeps each
Stainless batch small enough to finish while still compiling the chapter's
dependencies.

The older all-at-once command is still available, but it is not the preferred
regression command because the combined VC set can time out even when each
chapter verifies successfully on its own:

```bash
just verify
```

### Running on Docker

- Just 0.5.7
- docker 20.10.16

```bash
just verify-docker
```
