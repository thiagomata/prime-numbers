# Proof Guide

This document describes how to write mathematical proofs with Stainless verification in this repository.

## Print-Only Self-Containment

Every article must stand on its own as a printed document given to a reader who
has no access to this repository. The article itself must communicate four
things:

1. **Context:** define the mathematical objects and notation, and state the
   indispensable prior facts on which the article relies.
2. **Challenge:** identify the precise question being addressed and explain why
   it is not already settled by the context.
3. **Work:** present the construction or method, its assumptions, the argument,
   and the status of the mathematical, formal, and empirical evidence.
4. **Conclusion:** state what was established, what remains conditional or open,
   and why the result matters.

Repository links and citations may provide provenance, verification sources,
data, and reproducibility. They must not carry a definition, premise, proof
step, limitation, or conclusion that the reader needs in order to understand
the article. When a prior theorem is cited, restate its mathematical statement
and its role in the present argument; the earlier theorem's full proof may
remain in the cited source.

A final editorial review should therefore include a print-only test: ignore
every repository link and ask whether the remaining title, abstract,
introduction, body, and conclusion still explain the context, challenge, work,
and result as one coherent document.

## The Three Representations

Every property must be presented three times:

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

### Keep Simple English Simple

Every property needs the English layer, including a formula that appears
self-explanatory. For a simple identity such as
`sum(A ⧺ B) = sum(A) + sum(B)`, one sentence can be enough. State what the
identity says and why it is useful, then continue to the mathematical proof.

### Anti-Pattern: Labeled Blocks Are Not Prose

Do not replace the English description with a stack of bolded labels. This
has happened in practice and is exactly what "without explicit labels" (above)
rules out:

```markdown
**Population:** Cyclic 2-gap starts in one complete period of a prime stage.
**Scope and quantifier:** Complete-period; every prime stage after filter 2.
**Status:** Mathematically proved. Not Stainless-verified.
```

Write the same content as prose instead:

```markdown
This property counts every 2-gap in one complete sieve period directly from
the installed prime filters, for any prime stage once filter 2 is installed.
It is an exact finite product, not a recurrence or an asymptotic estimate.
```

The labels are a checklist for the author while drafting (does the prose
state the population? the scope? the status?), not headings meant to survive
into the published text. If a note's population or scope genuinely needs to
be pinned down precisely (see `VOCABULARY.md`), say so in a sentence, not a
label.

## Mathematical Proofs

### Format

Use LaTeX notation in `\`\`\`math` blocks:

```math
\begin{aligned}
\text{Statement} &= \text{Value} \quad \text{[Label]}
\end{aligned}
```

### Structure

1. **Explain the property and its intuition** in natural prose
2. **State the theorem/lemma** formally
3. **Show the proof** with step-by-step derivations
4. **Reference the Stainless verification**

### Labels

Label key steps with:
- `[Q.E.D.]` for proof completion
- `[By Lemma X]` for referencing other lemmas
- `[By Definition]` for definitional expansions
- `[By Induction Hypothesis]` for induction steps

The same `\quad \text{[Label]}` syntax has a second, distinct use: naming a
property in a conclusion's math recap rather than justifying a derivation
step. There the label is the property's short name (e.g.
`&&\text{[Modulo Idempotence]}`, using a double ampersand since the recap
row already has its own `&` before the `=`), one per row, not a proof-step
justification — see CONTRIBUTING.md rule 19 for the conclusion-recap
convention and formatting/width guidance.

### Example

```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_0 &= \text{cycle}(0) + init \\
&= 1 + init \\
&= init + 0 + 1 \quad \text{[Q.E.D.]}
\end{aligned}
```

## Common Rigor Failures (Review Checklist)

These five patterns were found, live, while auditing chapter 4's articles
(`cycle.md`, `integral.md`, `integral-cycle.md`) against their own cited
Scala source. Each one *looked* rigorous on a fast read — proper
headings, a `[Q.E.D.]` tag, a working link to source — and only broke
down once someone actually opened the cited lemma or traced a reference
to where it pointed. Check for all five before calling a property
section done, and re-check them whenever a section is restructured,
since reordering can silently turn a citation into a forward reference.

### Anti-Pattern: A Q.E.D. Label Is Not a Proof

Restating the theorem statement and appending `[Q.E.D.]` is a label, not
a derivation:

```markdown
​```math
\begin{aligned}
\text{rotate}(L, k)_i = L_{(i+k) \bmod n} \quad \text{[Q.E.D.]}
\end{aligned}
​```
```

Every such claim needs a real `**Proof.**` paragraph: explicit
substitution steps, an induction with a stated base case and inductive
step, or an explicit case split — not a sentence or two that only names
the Scala lemma verifying it, and not a bare restatement of the claim
with a label tacked on. A cheap, reliable tell: if a `\blacksquare` mark
is missing from a Q.E.D. block that every other proved claim in the
article carries, that block's derivation was probably never actually
written down.

### Anti-Pattern: A Named Citation Is Not a Different Fact

Before citing a Scala lemma, open it and read the function body — not
just its docstring or its name. A repeated failure mode: two sections
each cite a differently-named lemma —

```markdown
This property is verified in `Module.assertShiftAtBoundary`.
...
This property is verified in `Module.assertWrapsAfterPeriod`.
```

— and both names turn out, on inspection, to be thin wrappers that
immediately delegate to the same third lemma, with no independent proof
content of their own (a `require`/one-line-body pattern is the tell —
check for it explicitly). If two claims are backed by citations that
resolve to the same underlying call, the article has manufactured a
distinction that does not exist. Merge the two claims into one, or state
plainly that the second is the same identity applied at a different call
site; do not write two proofs for one fact.

### Anti-Pattern: Borrowing a Scala Name as Math Notation Without Defining It

Do not introduce math notation by mirroring a Scala field or method name
— e.g. writing `\text{total}(x)` in a math block because the Scala class
has a `.total` field — without a formal definition earlier in the
article. This matters doubly when the borrowed name could mislead about
the finiteness of what it names: a name like "total" or "sum" attached
to an object that is itself unbounded (an infinite, strictly-increasing
stream, not the finite structure underneath it) reads as if it sums
infinitely many terms. Ask: does this name still make sense if a
skimming reader takes it to mean the English word, applied to the thing
it's attached to? If not, pick a name that survives that reading — e.g.
`periodTotal(x)` instead of bare `total(x)` when `x` is unbounded but
the quantity itself is really a total over one finite period — and
define it explicitly before first use.

### Anti-Pattern: A Vague Backward Reference

"The property cited above," or a proof-step tag like `[X, above]`, sends
the reader searching an unspecified distance backward. Every
cross-section reference should be a `[§N](#anchor)` link. A
same-subsection reference is fine as bare prose only when it is
genuinely local — a few lines away, inside the same math block or the
immediately preceding paragraph. If resolving "above" requires the
reader to scroll past an intervening subsection, it should be a real
`§N` link instead.

### Anti-Pattern: Proof Order That Doesn't Match Dependency Order

When section B's proof uses a fact that section A establishes, A must
come before B in reading order — not just be citable from B.
Restructuring an article (splitting a chapter, promoting a subsection)
can silently turn a valid citation into a forward reference if the
dependency wasn't checked first. Before reordering, trace which
sections' proofs actually use which other sections' conclusions (read
the derivations, not just the section titles), and order accordingly. A
vague backward reference (previous anti-pattern) is often the symptom
that lets a forward dependency go unnoticed in the first place: a proof
step justified only by a descriptive bracket label, with no `§N`
pointer at all, gives no way to check whether the fact it leans on is
actually established yet.

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

**State verification status as a fact, not an apology.** A note whose scope
never claims full Stainless verification does not owe the reader a "pending"
disclaimer after every property. Use the `VOCABULARY.md` statuses precisely:
say **Stainless verified** when a theorem passed, **Not Stainless-verified**
as the plain, neutral default when it hasn't (and nothing says it's about
to), and reserve **Stainless verification pending** for a result with an
actual tracked next step. Do not write "No `.holds` theorem currently
encodes this... Stainless verification is pending" as a stock closer on
dozens of unrelated properties — that repetition reads as an apology for
something the note never promised. State it once, plainly, and move on.

#### Mathematical Drafts Without Stainless Verification

A draft may contain a complete mathematical proof before its Scala
verification exists. State once that the mathematical results are not
Stainless-verified, and do not present the draft as publication-ready under the
three-representation standard. The mathematical proof must appear in the
article body, an appendix, or another published article. Mark any included
Scala block as `DRAFT — not yet verified through Stainless`. Use “verification
pending” only when there is an actual tracked verification step. The final
article still needs English, mathematics, and maintained verification evidence
for every property.

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

### Mathematical Authority and Article Boundaries

An official article may cite only the following locations as the authority for
a mathematical definition, lemma, proof, or derivation:

1. an earlier section of the same article;
2. an appendix in the same article; or
3. another published article under `articles/chapter*/`.

Do not send the reader to `properties/`, `companions/`, `candidates/`,
`articles/learnings/`, tickets, or other internal working notes for the
mathematics. If a required proof exists only in one of those locations, either
include the proof in an appendix or promote it into an article before citing
it. An article's reference list should likewise omit internal working notes as
mathematical authorities.

Repository-file links remain appropriate when they point to the artifact that
implements, verifies, calculates, generates, or reproduces a result. Examples
include a Scala verification function, a calculation script, a verification
log, a data file, or a figure generator. Introduce such a link by stating its
evidentiary role; do not present it as a substitute for the mathematical proof
in the article or appendix.

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

1. Write the mathematical proof first.
2. Search the full source tree and `LEARNINGS.md` for an existing lemma before
   writing a new one; read the lemma body, not only its name.
3. Establish a green baseline with the Scala tests and applicable
   `just verify-ch N` checks. Inspect the existing logs before rerunning a
   completed check, and do not begin the proof change from a failed or timed-out
   gate.
4. Implement in Stainless with `require()` for preconditions and `decreases()`
   for recursive functions.
5. Add one assertion or lemma invocation per change.
6. Use `just verify functionName` for focused proof iteration when useful.
7. Repeat the Scala tests and applicable `just verify-ch N` commands for
   regression; the combined `just verify` timeout is not the canonical project
   result.
8. If a check fails, read the error and correct or revert that one change. Do
   not add unrelated changes while the selected gate is red.
9. If the same micro-goal fails three times, stop and ask for help.
10. Update `OBJECTS.md`, relevant articles, and durable `LEARNINGS.md` entries
   after verification succeeds.

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

## Voice and Style

These conventions were implicit in the earliest articles (`integral.md`,
`modulo.md`, `list.md`, `cycle.md`, `integral-cycle.md`) but were never
written down, and later articles drifted from them. They are now explicit.

### Match the Publication Series, Not Only Its Outline

An article can have the expected title, abstract, numbered sections, equations,
and references and still sound unrelated to the rest of the series. Structural
compliance is necessary, but the prose must also follow the same teaching
rhythm: introduce the construction, make it concrete, explain the property,
derive it, and then point to its verification evidence.

- **Lead with the contribution.** Use a direct, accurate title. Keep the
  abstract compact and centered on the construction, main result, and
  significance. Include assumptions needed for accuracy, but do not turn the
  abstract into a catalog of caveats, secondary models, or future work.
- **Build from a concrete case.** When a construction is unfamiliar, give one
  small example before introducing the general notation or asymptotic law. The
  example should reveal the invariant or distinction used by the proof, not
  merely decorate the section.
- **Teach one mathematical idea at a time.** A subsection should normally
  introduce one definition, property, or comparison. Explain why it matters
  before presenting its symbols. Use a summary table when several regimes must
  be compared, but do not repeat the same conclusion in multiple inventories.
- **Keep research protocols outside the proof narrative.** Seed grids,
  per-transition logging checklists, solver tactics, and execution plans belong
  in companion model documents, `LEARNINGS.md`, or tickets. If an empirical
  comparison matters to the article, state the mechanisms, essential
  observables, and mathematical purpose in concise prose or a small table.
- **Prefer direct language.** Say “the companion model defined above,” “the
  cumulative criterion,” or “the mixed process” instead of research-ledger
  phrases such as “the stipulated model,” “the authoritative quantity,” or
  “the projection,” unless the technical distinction genuinely requires that
  term.
- **Preserve depth without preserving drafting history.** A detailed article
  may be long. Remove duplicated status notes, abandoned alternatives,
  protocol inventories, and repeated summaries rather than removing premises,
  derivations, boundary cases, or evidence.

- **Write in first person plural.** "We prove...", "we define...", not "This
  article proves..." or "The article defines...". The author is present in
  the prose, doing the work, not narrating a document that does the work.
- **Close a derivation with `\blacksquare` and/or `[Q.E.D.]`**, matching every
  existing article. Do not introduce `\boxed{...}` around conclusions; it is
  not the established convention and mixing the two within one project reads
  as two different authors.
- **Bold is for defining a term once**, not for labeling every claim. Do not
  bold entire status or label phrases ("**Mathematically proved, Stainless
  verification pending.**") as a matter of routine — see the labeled-block
  anti-pattern above. If most sentences in a section start with a bolded
  phrase, that is a sign the prose has collapsed into a checklist.
- **Use sentence case for inline concept names in flowing prose.** Write "the
  divisor local factor property," not "the Divisor Local Factor property."
  Capitalize only genuine proper nouns (a person's name, a named theorem from
  the literature). This does not apply to section/subsection headers, which
  keep Title Case per existing convention (e.g. "Core Integral Properties"),
  nor to a property's short name used as a citation label — link text, table
  cells, and "properties from X through Y" range references keep the
  registry's Title Case, matching how the short-name registry itself presents
  them.
- **Vary contrastive phrasing.** "This does not X; it does Y" is a useful
  sentence once. Repeated as the default way to state every scope boundary,
  it becomes a tic. Prefer stating what something establishes first, and
  reach for a contrastive construction only when the reader would otherwise
  guess wrong.
- **One explanatory sentence before the first display equation.** Do not
  jump from a header straight into `math` blocks; give the reader the idea in
  words first, the way `integral.md` and `cycle.md` do.

## Getting Started

When writing a new article or adding new proofs:

1. **Read the finished articles**, not drafts, before choosing the structure and
   voice.
2. Use `articles/chapter2/modulo.md`, `articles/chapter3/list.md`,
   `articles/chapter4/integral.md`, `articles/chapter4/cycle.md`, and
   `articles/chapter4/integral-cycle.md` as the principal references.
3. Follow this guide when an older article contains a legacy inconsistency; use
   the finished articles for their teaching rhythm, not as permission to copy
   every historical formatting choice.
4. Do not use `draft-*.md` articles as style authorities because they may not
   follow the final conventions.

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
- Use focused verification while iterating, then run the applicable
  chapter-by-chapter regression before treating the change as complete

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
