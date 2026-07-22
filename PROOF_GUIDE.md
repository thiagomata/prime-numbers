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

The snippet should match the source shape. A `.holds` lemma is common, but it
is not the only acceptable verification form: verified `assert` chains,
`ensuring` postconditions, constructor invariants, and Boolean helper
predicates consumed by verified callers can also support an article claim. The
article standard is source-backed verification code, not "must end in `.holds`".

For article readability, use `articles/chapter4/cycle.md` as the preferred
embedding pattern. Main property sections should carry the English explanation,
the mathematical proof, and a source link. Small inline Scala blocks are fine
when they show the core idea with a good signal/noise ratio. Put longer proof
bodies in an appendix only when they are worth keeping close to the article;
otherwise, link to the source module directly. Any Scala excerpt kept in an
appendix must have a nearby Markdown source link to the repository file that
owns the maintained proof. Source excerpts kept in the main body need the same
treatment: put a source link before or immediately after the block. When prose
points to an appendix item, check that the appendix number still matches the
current document.

The mathematical property must lead the section. Do not organize article prose
around source method names or code-name inventories. When a helper matters,
give it a property name, state and prove the math, then cite the source method
as the verification reference.

Theorem articles should be math-first rather than source walkthroughs. Keep
solver tactics, cache behavior, verification workflow, and postcondition
strategy notes in `LEARNINGS.md` or tickets, not article bodies.
It is fine to include a concise verification-log appendix that confirms the
described properties verify and links to the log; do not make run-log mechanics
part of the proof narrative.
Do not let this become understatement: formal verification is a meaningful
achievement and should remain visible in abstracts, introductions, conclusions,
and property references when the code has been verified. The distinction is
between proudly reporting formal verification and teaching low-level verifier
mechanics.

Conclusion and future-work sections should be prose, not simple task lists.
Use the conclusion to synthesize the theorem, proof strategy, verified support,
and scope of the result. The conclusion must also bring back the core proved
properties and proof structure in mathematical form: include a compact math
recap of the main theorem, definitions, and supporting properties that the
article established, following the `integral.md` and `cycle.md` pattern. Use
future work to explain the next mathematical directions and why they extend
the article, rather than listing project names as bullets.
Avoid future-facing framing outside Future Work: abstracts, introductions, and
conclusions should not justify the result by saying it will be used later,
needed downstream, or useful for future chapters. They should state what the
article proves and verifies now.

Use `$...$` for inline mathematical expressions such as
$d \cdot d \le d \cdot q = n$ and $\text{mod}(n,d)=0$; reserve
backticks for source identifiers and literal code.
Do not use unsupported LaTeX macros such as `\operatorname`; use `\text{...}`
or established infix notation instead.
For strict comparisons, avoid compact raw forms such as `a<b` or `x<N` in
article math because `<b` or `<N` can be read as HTML-like markup by GitHub or
VS Code. Write spaced raw comparisons such as `a < b`, or use `\lt` and `\gt`
when spacing would make the expression awkward.

Use `:=` only for definitions, local aliases, and notation conventions. Use
`=` for mathematical equalities, theorem statements, and proof derivation
steps. For example, $S := \text{DivMod}(a,b,0,a).\text{solve}$ introduces
$S$, while $a = bq + r$ states an equality.

### Verification References

Article prose should state what was verified, not teach the mechanics of
Stainless annotations. Prefer wording like "This property is verified in
`ObjectName::functionName`" or "The source proof establishes the implication
above." Avoid phrases that make `.holds`, assertions, or solver caching the
topic of the article.

```scala
def myLemma(x: BigInt): Boolean = {
  require(x >= 0)
  // ... proof logic ...
}.holds
```

Use code blocks only when the snippet helps the reader see the proof shape.
Otherwise, link to the source. Internal proof-engine observations belong in
`LEARNINGS.md`, where they can guide future verification work without pulling
the article away from the mathematics.

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

## Formatting Conventions

### List Concatenation

Use `::` for cons: an element on the left and a list on the right. Use
`\mathbin{\texttt{++}}` for list concatenation: a list on the left and a list on
the right. Do not write singleton-list prepends such as `[x] ++ L` in article
math when `x :: L` expresses the same structure more directly. Likewise, avoid
singleton-list construction such as `[x]`, `[e]`, or `[L_t]` when expressing
cons, suffix append, or insertion in article math; prefer `x :: L_e`,
`e :: suffix`, or `A \mathbin{\texttt{++}} (e :: B)`. Display lists such as
`[v_0,\dots,v_{n-1}]` and set-builder/range lists remain fine.

```math
\begin{aligned}
x :: L \\
A \mathbin{\texttt{++}} B
\end{aligned}
```

The `\mathbin` wrapper gives `++` binary-operator spacing, while `\texttt`
renders the two plus signs as a cohesive operator in GitHub and VS Code math
previews.

In prose, code blocks, and bullet-summary lines, plain `++` is acceptable
because it renders as monospace text or source code, not LaTeX math.

```scala
sum(A ++ B) == sum(A) + sum(B)
```

For suffix and insertion cases, keep `++` only between lists and express the
inserted singleton with cons:

```math
\begin{aligned}
\text{slice}(L, f, t - 1) \mathbin{\texttt{++}} (L_t :: L_e) \\
prefix \mathbin{\texttt{++}} (e :: suffix)
\end{aligned}
```
