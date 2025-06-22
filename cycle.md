# Using Formal Verification to Prove Properties of Unbound Lists and Integrals

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<div align="justify">
<p style="text-align: justify">
In previous articles, we defined bounded Lists and Integrals of <code>BigInt</code>
from scratch, relying only on core type constructs and recursion, 
with no prior knowledge of Scala's collections required.
From that, we proved and formally verify some properties related to them as size, append, concat,
slice and sum.
This article use that as foundation to define Cycles - unbounded List of Integers
created from a bounded List, where the values of the Cycle are the values of the
List in repetition using recursion - and Cycle Integral that is the discrete integral of the Cycles.
Then, we formally defined and verify key properties such as ... using the Stainless verification system. 
All properties are expressed and proved within a minimal framework using only elementary arithmetic,
 recursion, and pure Scala code.
This work bridges mathematical foundations and executable verification, offering a self-contained, verifiable
 treatment of modular arithmetic.
 </p>
</div>

# Introduction

Unbounded lists in cycles, are a fundamental concept in computer science and mathematics, often used to model
repetitive structures or processes. They can be thought of as infinite lists that repeat a finite sequence of elements.

```math
L = [x_0, x_1, x_2, \ldots, x_{n-1}]  \mid x_n \in 𝕊, L \in 𝕃\\
\text{Cycle}(L) = [x_0, x_1, x_2, \ldots, x_{n-1}, x_0, x_1, \ldots] \\
```
In this article, we present a discrete definition of Cycle and Cycle Integral 
operations over finite integer lists, defined recursively and verified some of 
its properties using the Stainless system.
Our approach follows a zero-prior-knowledge philosophy, building on a previously 
verified foundation for recursive list and integral structures and summation.
The result is a verified, from-scratch implementation of cycle and cycle integral 
suitable as a foundation for higher-level numeric reasoning over unbounded lists.

## 2. Preliminaries and Notation

We reuse several basic list and integral operations and their verified properties from the companion articles [Using Formal Verification to Prove Properties of Lists Recursively Defined](
https://github.com/thiagomata/prime-numbers/blob/master/list.md
) [[1]](#ref1) and [Formal Verification of Discrete Integration Properties from First Principles](integral.md)[[2]](#ef2).
These include the following functions:

- $\text{sum}(L)$: recursively computes the total sum of elements in a list.
- $\text{head}(L)$: returns the first element of a non-empty list.
- $\text{tail}(L)$: returns the list without its first element.
- $A$ &#x29FA; $B$: concatenates two lists $A$ and $B$.

These operations were defined and verified using the same zero-prior-knowledge methodology,
and are treated here as foundational primitives.

Proofs in this article are written in Scala and verified using the Stainless system with `BigInt` used to represent
unbounded integers.

