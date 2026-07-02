# Proof Guide

This document describes how to write mathematical proofs with Stainless verification in this repository.

## The Three Representations

Every property should be presented three times:

### 1. English Description (Above the Math)

Place the English description ABOVE the formal proof as an overview.
It should answer these questions naturally in prose — without explicit labels:

- **What** the property states
- **Why** it matters (motivation)
- **Intuition** to help readers before seeing symbols

Example:
> The first property establishes that a cycle integral with unit cycle produces
> consecutive integers. Each step adds exactly 1, so we get consecutive integers
> starting from `init + 1`. This is how the sieve generates all natural numbers
> from 2 onward.

### 2. Mathematical Proof

Articles use Formal statement and step-by-step derivation with `\`\`\`math` blocks with LaTeX notation. 
Javadoc in `.scala` files uses plain ASCII math (see AGENTS.md rule `javadoc-math`).


```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_0 &= \text{cycle}(0) + init \\
&= 1 + init \\
&= init + 0 + 1 \quad \text{[Q.E.D.]}
\end{aligned}
```

### 3. Stainless Verification (Code)

Formal verification code with reference to source file:

```scala
def assertCycleIntegralOfOnes(init: BigInt, pos: BigInt): Boolean = {
  require(pos >= 0)
  require(init >= 0)
  // ... proof logic ...
}.holds
```

This property is verified in the [
  ObjectName::functionName
](
  ../src/main/scala/path/to/file.scala
).

### Placement Guidelines

- Place English description ABOVE the math as an overview
- Weave motivation and intuition into natural prose
- The math proof stands on its own
- Stainless verification follows the math

### When to Skip English

Simpler properties (e.g., `sum(A ⧺ B) = sum(A) + sum(B)`) may skip
the English layer if the formula is self-explanatory.

## Mathematical Proofs

### Format

Use LaTeX notation in `\`\`\`math` blocks:

```math
\begin{aligned}
\text{Statement} &= \text{Value} \quad \text{[Label]}
\end{aligned}
```

### Structure

1. **State the theorem/lemma** formally
2. **Explain the intuition** in natural prose (no label required)
3. **Show the proof** with step-by-step derivations
4. **Reference the Stainless verification**

### Labels

Label key steps with:
- `[Q.E.D.]` for proof completion
- `[By Lemma X]` for referencing other lemmas
- `[By Definition]` for definitional expansions
- `[By Induction Hypothesis]` for induction steps

### Example

```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_0 &= \text{cycle}(0) + init \\
&= 1 + init \\
&= init + 0 + 1 \quad \text{[Q.E.D.]}
\end{aligned}
```

## Stainless Verification

### Code Placement

Show formal verification code alongside the math:

```markdown
#### Mathematical Proof

[LaTeX proof here]

#### Stainless Verification

```scala
def lemma(...): Boolean = {
  // Stainless code here
}.holds
```

This property is verified in the [
  ObjectName::functionName
](
  ../src/main/scala/path/to/file.scala
).
```

### .holds Mechanism

Functions annotated with `.holds` are verified to return `true` for all valid inputs.

```scala
def myLemma(x: BigInt): Boolean = {
  require(x >= 0)
  // ... proof logic ...
}.holds
```

**Key insight:** Internal assertions inside `.holds` functions are cached by Stainless and become available at call sites. This eliminates the need to enrich postconditions explicitly.

### Helper Lemmas

When the SMT solver can't connect abstract properties to concrete relationships, create helper lemmas:

1. **Identify the gap**: What can't the solver connect?
2. **Create a helper lemma**: Bridge the gap with explicit induction
3. **Use the helper**: Reference it from the main lemma

**Example:**
The solver couldn't connect `noDivisorInRange(q, 2, q)` (abstract) to `mod(q, p) ≠ 0` (concrete). The helper lemma `noDivisorInRangeImpliesModNonZero` makes this connection explicit.

### Assertion Patterns

Use `assert()` to invoke cached lemmas:

```scala
def mainLemma(...): Boolean = {
  // Invoke cached lemma
  assert(helperLemma(...))
  
  // Now the solver knows the result of helperLemma
  result
}.holds
```

**Rule:** One assertion per change for verification. If you need `a && b && c`, split into 3 changes.

### Verification Workflow

1. Write the mathematical proof first
2. Implement in Stainless with `require()` for preconditions
3. Add `decreases()` for recursive functions
4. Add `assert()` to invoke cached lemmas
5. Run `just verify`
6. If it fails, read the error and fix (don't retry blindly)
7. If stuck after 3 attempts, stop and ask for help
8. Update README with new properties

### Common Patterns

**Base Case:**
```scala
if (pos == 0) {
  // Base case logic
  result
}
```

**Inductive Step:**
```scala
else {
  assert(lemma(pos - 1))  // Invoke induction hypothesis
  result
}
```

**Case Analysis:**
```scala
if (condition1) {
  assert(helperForCase1(...))
  result
} else {
  assert(helperForCase2(...))
  result
}
```

## Getting Started

When writing a new article or adding new proofs:

1. **Always look to existing finished articles** (not drafts) to copy the similar structure and style
2. Reference articles: `integral.md`, `cycle.md`, `list.md`, `modulo.md`, `integral-cycle.md`
3. Match the formatting patterns you see in those articles
4. Avoid referencing draft articles (`draft-*.md`) as they may not follow final conventions

## Stainless Rules

### Do

- Use `BigInt` for all integers
- Use `stainless.collection.List` not `scala.collection.List`
- Import `BooleanDecorations` for `.holds`
- Use `decreases()` for recursive functions
- Use `Calc.div()` and `Calc.mod()` not `%` operator

### Don't

- Use `%` operator (not supported by Stainless)
- Use `@extern` without explicit instruction
- Modify `MemCycle`, `ModCycle`, or `CycleIntegral`
- Add multiple assertions per verify cycle
- Delete files to fix compile errors

### Debugging

- Read error messages carefully
- Check which verification condition failed
- Add `assert()` to help the solver
- Use `stainless.lang BooleanDecorations` for `.holds`
- Run `just verify` after each change
