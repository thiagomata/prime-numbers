# Research Vocabulary

This document defines the shared language for research notes in this
repository. Its main purpose is to keep a claim's **population**, **scope**,
**quantifier**, and **status** visible. Those four coordinates are part of the
claim, not editorial decoration.

This is a canonical vocabulary, not a universal symbol table. A specialized
document may introduce local notation, but it should map that notation to the
terms here and must not silently change their meanings. The mathematical
definition in the property or candidate being discussed remains authoritative.

## The Minimum Complete Statement

A research statement should answer four questions:

1. **Population:** What values, gaps, anchors, copies, or residue classes are
   being counted?
2. **Scope:** Is the statement about a complete period, a local window, one
   filter, or a complete conditioned chain?
3. **Quantifier:** Was it seen once, checked finitely, proved for every layer of
   one chain, proved infinitely often, or proved eventually always?
4. **Status:** Is it an exact definition, a mathematical theorem, a
   Stainless-verified theorem, a conditional implication, an empirical
   observation, or an open hypothesis?

For example, “the 2-gaps are balanced” is incomplete. A usable version is:

> In every complete period before filter `r`, the 2-gap starts are exactly
> uniform across the copy-index classes modulo `r` [mathematically proved].

That statement does not claim uniformity inside a square window or after the
filter.

## Core Sieve Objects

### Sieve stage

A **sieve stage** is the state after a specified finite set of prime filters
has been installed. The stage determines the accepted values, its cyclic gap
pattern, its period, and the next transition.

### Head

The **head** is the prime that identifies the current sieve-sequence stage.
When a proof fixes a future certification stage, use **future head** `Q`.

### Incoming or filter prime

An **incoming prime** or **filter prime** is the prime installed by one
transition. Use `r` when discussing one generic filter and `r_i` for filter
`i` in a chain.

Some older candidate notes use `p` for the installed transition prime and `q`
for the next head. That notation remains valid when defined locally. New
cross-candidate arguments should prefer `r` for a filter and `Q` for the fixed
future head, because their mathematical roles are then visible.

### Installed and missing primes

Relative to a stage:

- an **installed prime** already participates in its acceptance condition;
- a **missing prime** is a later prime whose filter must still be applied
  before the chosen future stage is reached.

A **complete conditioned chain to `Q`** installs all missing primes required
to reach the future head `Q`, in their actual order.

### Accepted value

An **accepted value** survives every prime filter installed at the stage under
discussion. Acceptance is always stage-relative.

### Gap and gap start

If consecutive accepted values are `x<y`, their **gap** is `y-x` and its
**gap start** is `x`.

A **2-gap** has endpoints `x` and `x+2`; its **2-gap start** is `x`. A
statement about 2-gap starts is not automatically a statement about all
accepted values or all numerical prime candidates.

### Candidate

The word **candidate** is overloaded and should be qualified:

- a **research candidate** is a numbered open hypothesis under `candidates/`;
- a **prime candidate** is a numerical value not yet certified prime;
- a **twin-prime candidate** is a pair with difference two that has not yet
  passed the required certification argument.

Do not use “candidate” alone where more than one meaning is possible.

## Windows, Periods, and Populations

### Complete period

A **complete period** contains one full cycle of the current periodic sieve
pattern. CRT and copy-count identities are often exact on complete periods.

Complete-period uniformity does not imply uniformity in a short interval cut
from that period.

### Local window

A **local window** is a bounded interval selected from the unbounded or cyclic
pattern. Its boundary may cut through complete blocks, so complete-period
cancellation can disappear.

### Ambient square interval

For a fixed future head `Q`, `[Q,Q^2)` is the common **ambient square
interval** for gap starts. A note must still check the right endpoint of the
gap before calling every start in this interval square-safe.

### Eligible square-safe window

The **eligible square-safe 2-gap-start window** is

```math
W_Q=\{x:Q\le x\text{ and }x+2<Q^2\}.
```

The strict upper inequality belongs to the definition. If every missing prime
below `Q` has been installed, a surviving 2-gap start in `W_Q` is a
**square-safe certificate** for the twin-prime pair `(x,x+2)`.

### Population

A **population** is a set or count attached to a stated stage and region. Never
write only “the population” when it could mean:

- all accepted values;
- all 2-gap starts;
- starts before the incoming filter;
- starts after that filter;
- a complete-period population;
- a local-window population.

For a conditioned chain, the recommended notation is:

```math
S_i=\{\text{2-gap starts in the stated window before filter }r_i\},
\qquad
N_i=|S_i|.
```

Use `S_{i+1}` and `N_{i+1}` for the actual survivors after filter `r_i`.
Some one-layer notes use `G` for a generic local 2-gap population. Such a file
should state explicitly whether `G=N_i` or `G=N_{i+1}`.

## Filter Dynamics

### Expansion

**Expansion** repeats the old period or gap cycle into the copies needed for a
new transition. “Each old object has the same number of copies before
filtering” is an expansion statement. It says nothing by itself about the
distribution of surviving copies inside a local window.

### Shot or strike

A **shot** or **strike** is a value removed by the incoming filter. In algebraic
arguments, prefer:

- **accepted strike** when the removed multiple had survived all earlier
  filters;
- **harmful strike** when it hits an endpoint of a 2-gap in the stated
  population.

Counting raw multiples is not the same as counting accepted strikes, and
counting strikes is not the same as counting destroyed 2-gaps.

### Struck and intact copies

When one expansion step produces `r` copies of an old object and one
incoming filter strikes some of them, name the two resulting counts
`N_struck` and `N_intact` (with `N_intact = r - N_struck`), each with a
one-line description of what is being counted (e.g. "the number of expanded
copies of one cluster struck by filter `r`"). Do not fall back to an inline
cardinality expression such as `#{struck copies}` for a quantity that is
used more than once — introduce the name first, then use it.

### Harmful and harmless residue classes

For 2-gap starts modulo an incoming prime `r`, the **harmful classes** are `0`
and `-2`: a start in either class has one endpoint removed. The other `r-2`
classes are **harmless classes** for that filter.

“Harmless” is one-layer language. A start in a harmless class for `r_i` may be
harmful for a later prime.

### Deletion, destruction, survival, and merge

- A value is **deleted** when the filter removes it.
- A 2-gap is **destroyed at a layer** when at least one endpoint is deleted.
- A 2-gap **survives a layer** when both endpoints remain after that filter.
- A 2-gap **survives the conditioned chain** when it survives every remaining
  filter in that chain.
- Adjacent gaps **merge** when the accepted value between them is deleted.

Filtering copies or merges existing gaps; it does not recreate a missing
2-gap. Nevertheless, “some copy survives this filter” is weaker than “one
descendant survives every future filter.”

### Descendant and lineage

A **descendant** is a later copy of an earlier gap or pattern traced through
expansion and filtering. Its **lineage** is that history across layers.

Existence of a survivor at each layer does not automatically produce one
common surviving lineage unless the choices are shown to be compatible or a
finite nested-set argument supplies that compatibility.

## Scope Vocabulary

Use the narrowest applicable scope qualifier.

| Term | Meaning | Does not imply |
|------|---------|----------------|
| **One-layer** | One incoming filter applied to one stated pre-filter population | Survival through later filters |
| **Complete-period** or **cyclic** | One full period, with wrap-around when stated | Any short-window placement |
| **Local** or **windowed** | Restricted to a stated bounded interval | Complete-period uniformity |
| **Conditioned-chain** | The actual nested populations under an ordered list of future filters | The same estimate for every possible chain |
| **Weighted aggregate** | A sum across layers with explicitly defined survival weights | The corresponding pointwise estimate at each layer |
| **Global** | The entire object named by the statement | Permission to omit what that object is |
| **Square-safe** | Below the strict square threshold after all required smaller-prime filters | Survival at an earlier incomplete stage |
| **Hereditary** | Preserved along every required later transition or along a specified common lineage | Mere repetition of unrelated one-layer witnesses |

Avoid “global” by itself. Say **complete-period global**, **global over the
conditioned chain**, or another precise variant.

## Quantifier Vocabulary

These statements have different strength:

1. **One example:** the claim holds for one specified input.
2. **Finite sweep:** the claim holds for every input in a stated finite sample.
3. **Every layer of one chain:** the claim holds at all layers for one fixed
   future head.
4. **Infinitely many heads:** there is an unbounded family of successful
   heads; this does not mean every sufficiently large head succeeds.
5. **Eventually always:** there is a threshold beyond which every head
   succeeds.
6. **Universal:** the claim holds for every input satisfying its stated
   preconditions.

Words such as “always,” “eventually,” and “infinitely often” must not be used
interchangeably.

## Collision and Capacity Language

### Residue histogram

For the pre-filter population `S_i`, the **residue histogram** modulo `r_i` is

```math
c_{i,a}
=
\#\{x\in S_i:x\equiv a\pmod{r_i}\}.
```

### Full residue collision energy

The **full residue collision energy** is

```math
V_i
=
\sum_{a\bmod r_i}
\left(c_{i,a}-\frac{N_i}{r_i}\right)^2.
```

It measures deviation from uniformity over all residue classes. It is not a
probabilistic variance claim unless a probability space is separately defined.

### Harmful excess and imbalance

Let

```math
K_i=c_{i,0}+c_{i,-2}.
```

The **total harmful excess** and **harmful-class imbalance** are

```math
b_i=K_i-\frac{2N_i}{r_i},
\qquad
\Delta_i=c_{i,0}-c_{i,-2}.
```

Their **harmful scalar energy** is

```math
Q_i
=
\frac{r_i}{2(r_i-2)}b_i^2
+
\frac12\Delta_i^2.
```

### Harmless-class energy

With actual survivor count `N_{i+1}`, the **harmless-class energy** is

```math
U_i
=
\sum_{a\notin\{0,-2\}}
\left(c_{i,a}-\frac{N_{i+1}}{r_i-2}\right)^2.
```

The exact orthogonal decomposition is

```math
V_i=U_i+Q_i.
```

This identity separates three effects; it does not bound any of them.

### Capacity

A **capacity** is a deterministic upper bound on how many relevant objects can
occupy a class, interval, block, or other container. A population exceeding
the total harmful capacity forces survival by pigeonhole.

Capacity is not equidistribution, random sampling, or a density theorem.

### Density

A **density** is always a ratio with an explicitly named numerator and
denominator. For example, some one-layer capacity notes use

```math
\rho=\frac{G}{B},
```

where `G` is the stated local population and `B` is a one-class harmful
capacity. The critical value `rho_*(r)` belongs to that one-layer collision
ellipse. It is not a global chain threshold.

### One-layer allowance versus global weighted budget

For one filter, set

```math
a_i=1-\frac2{r_i}.
```

The multiplicative main term is `a_iN_i`. The sharp one-layer harmful ellipse
compares

```math
Q_i
<
\frac{(a_iN_i)^2}{2}.
```

For a chain of `m` filters, define

```math
A_{u,v}=\prod_{j=u}^{v-1}a_j,
\qquad
w_i=A_{i+1,m},
\qquad
W_{\mathrm{chain}}=\sum_{i=0}^{m-1}w_i,
```

and name the final multiplicative main term

```math
T_{\mathrm{chain}}=N_0A_{0,m}.
```

The corresponding weighted second-moment budget compares

```math
\sum_iw_iV_i
<
\frac{T_{\mathrm{chain}}^2}{2W_{\mathrm{chain}}}.
```

Passing every one-layer ellipse does not imply this aggregate inequality.
The local allowances and the global weighted budget have different scaling.

## Symbol Registry

This table collects every symbol defined in prose elsewhere in this document,
plus the local-but-registered symbols introduced to resolve a collision (see
Notation Discipline below). It is not a universal symbol table for every
one-off variable in every derivation — see the Maintenance Rule at the end of
this document for when a symbol belongs here.

| Symbol | Concept | Notes |
|--------|---------|-------|
| `Q` | Fixed future prime head used for square-safe certification | |
| `r` | One generic incoming or filter prime | |
| `r_i` | Filter `i` in an ordered chain | |
| `p`, `q` | Legacy roles: `p` the installed transition prime, `q` the next head | Valid only when defined locally; new cross-cutting work should prefer `r` and `Q` instead |
| `x` | A gap start or accepted value under discussion | |
| `W_Q` | Eligible square-safe 2-gap-start window, `{x : Q<=x and x+2<Q^2}` | |
| `S_i` | 2-gap starts in the stated window before filter `r_i` | |
| `N_i` | `\|S_i\|`, the population size before filter `r_i` | |
| `S_{i+1}`, `N_{i+1}` | The actual survivors, and their count, after filter `r_i` | |
| `G` | Generic local 2-gap population in a one-layer note | Collision-prone across notes; state explicitly whether `G=N_i` or `G=N_{i+1}` |
| `N_struck`, `N_intact` | Copies struck by, versus left intact by, one incoming filter during expansion | `N_intact = r - N_struck` |
| `c_{i,a}` | Residue histogram: count of `S_i` in residue class `a mod r_i` | |
| `V_i` | Full residue collision energy at layer `i` | Deviation from uniformity across all residue classes |
| `K_i` | `c_{i,0}+c_{i,-2}`, the harmful-class total at layer `i` | |
| `b_i` | Total harmful excess, `K_i - 2N_i/r_i` | |
| `Delta_i` | Harmful-class imbalance, `c_{i,0}-c_{i,-2}` | |
| `Q_i` | Harmful scalar energy, combining `b_i` and `Delta_i` | |
| `U_i` | Harmless-class energy: deviation from uniformity over the harmless classes | |
| `B` | A one-class harmful capacity bound (e.g. in `rho=G/B`) | Collision-prone; see Notation Discipline |
| `rho` | A density: always a ratio with an explicitly named numerator and denominator | |
| `a_i` | One-layer multiplicative allowance factor, `1-2/r_i` | |
| `A_{u,v}` | Product of `a_j` for `j=u,...,v-1` | Do not confuse with `A_i` below |
| `w_i` | `A_{i+1,m}`, the weight of layer `i` in a chain of `m` filters | |
| `W_chain` | Sum of `w_i` over a chain | |
| `T_chain` | `N_0 * A_{0,m}`, the chain's final multiplicative main term | Prefer this name over bare `T` in cross-cutting summaries |
| `M_i` | Collision-prone: actual harmless survivor population in some notes, one-step multiplicative main term in others | Define locally; prefer `N_{i+1}` or `a_iN_i` in new shared work |
| `A_i` | Accepted-anchor population in some notes | Do not confuse with product notation `A_{u,v}` above |
| `T` | Chain main term in candidate #21/#22; period-like quantities elsewhere | Prefer `T_chain` in cross-cutting summaries |
| `K` | Largest accepted multiplier below a future head's square in `gap-dynamics-v3.md` §4.3 | Reserved for that meaning in this document; do not reintroduce bare `K` for a new count |
| `I` | An arbitrary integer interval throughout `gap-dynamics-v3.md` from §5.1 onward | Do not reuse bare `I` for a count |
| `N_harm` | `c_0+c_{-2}`, harmful-class count in `gap-dynamics-v3.md` Appendix C.1 | Renamed from a bare `K` that collided with §4.3's `K` above |
| `R` | Product of a batch of incoming primes in `gap-dynamics-v3.md` §3.3 | Renamed from a bare `B` that collided with the capacity `B` above |
| `N_destroyed`, `N_removed` | Destroyed 2-gaps, and removed accepted values, in `gap-dynamics-v3.md` §4.2 | |
| `G_destroyed(r,Q)` | Destroyed eligible 2-gaps in `gap-dynamics-v3.md` §4.4 | Parallel to `G_local(r,Q)` and `G_surviving(r,Q)` in the same section |

## Notation Discipline

Definitions local to a file remain valid, but every symbol must be defined
before use. For new cross-cutting work, prefer role-revealing names such as
`T_chain`, `W_chain`, `N_before`, and `N_after` when collisions are likely.
Add a new symbol to the Symbol Registry above when it resolves a collision or
is meant to be reused across documents.

Prefer a named, introduced quantity over an inline cardinality expression
such as `#{struck copies}` or `|{...}|`, even for a count used only once.
State what is being counted in a short lead-in sentence ("let `N_struck` be
the number of..."), then use the name in the display. This keeps the same
name attached to the same thing everywhere it recurs, instead of each
derivation re-describing the same count in slightly different words. See
"Struck and intact copies" above for a worked example.

## Evidence and Proof Status

Use one of these explicit statuses:

- **Definition:** fixes meaning; it is not a theorem.
- **Exact identity:** an equality derived without an approximation or
  inequality. Also state whether it is proved.
- **Mathematically proved:** a complete mathematical proof is present or
  linked. This status is complete on its own. A note or article whose scope
  never claims Stainless verification does not need a verification qualifier
  attached to every occurrence of this status — say so once, if at all, and
  move on.
- **Stainless verified:** a named Scala theorem has passed Stainless. This
  status is stronger about the encoded program, but only within its stated
  preconditions and specification.
- **Not Stainless-verified:** a plain factual statement that no passing
  Stainless theorem exists for this result yet, with no claim about whether
  or when one will. This is the default way to note the absence of
  verification for exploratory notes, candidates, and drafts that never
  promised full verification in the first place. State it once per document
  or once per property, not as a refrain repeated after every claim.
- **Stainless verification pending:** reserve this specifically for a result
  with an actual tracked plan to verify it soon (e.g. linked to an open
  ticket targeting that exact proof). "Pending" says a next step is already
  underway or committed to; do not use it as a synonym for "not verified" —
  that overstates the situation and, repeated across dozens of properties,
  reads as an apology for something that was never promised. Ask "has
  Stainless verified this?" — the answer is either yes, no, or not yet but
  actively in progress; write whichever is true.
- **Proved conditional implication:** `H => C` is proved, while the antecedent
  `H` remains a separate obligation.
- **Candidate hypothesis** or **open:** the statement is proposed but not
  proved.
- **Problem boundary:** proved reductions identify a missing theorem without
  claiming that theorem.
- **Empirically checked on a finite sample:** exact inputs and range are stated;
  no universal conclusion is claimed.
- **Empirically reinforced:** finite observations support prioritizing the
  hypothesis but do not prove it.
- **Empirically inconclusive:** the test was indirect, too small, or otherwise
  unable to distinguish the hypothesis.
- **Refuted:** a valid counterexample falsifies the exact universal statement.
- **Failed proof route:** an attempted method did not prove the statement. This
  does not refute the statement.

Avoid unqualified **proved** and **verified**. Say what was proved, by which
kind of argument, and at what scope. “Test sample checked” is empirical, not a
proof for all inputs.

## Exact, Bounded, Conditional, and Heuristic Claims

- An **exact formula** is an equality, not merely an upper or lower bound.
- An **upper bound** and a **lower bound** must preserve their direction when
  substituted into later inequalities.
- A **sufficient condition** proves an outcome if its antecedent holds; it does
  not prove that the antecedent holds.
- A **necessary condition** is required by an outcome; satisfying it need not
  force the outcome.
- A **heuristic** or **random-model benchmark** guides expectation but is not a
  deterministic theorem about the sieve.
- An **asymptotic** statement does not automatically settle finitely many
  exceptional inputs or provide an effective threshold.

## Common Non-Equivalences

Do not substitute either side of these distinctions for the other:

| Established statement | Stronger statement still needing its own argument |
|-----------------------|---------------------------------------------------|
| Every old object is copied equally during expansion | Survivors are evenly distributed in a local window |
| Exact complete-period CRT uniformity | Short-window residue uniformity |
| A 2-gap survives one filter | The same lineage survives every future filter |
| Some survivor exists at each layer | One compatible survivor exists at the end |
| A strike occurs | A 2-gap is destroyed |
| Capacity leaves room for a survivor | Residues sample their classes evenly |
| A local harmful ellipse holds at every layer | The weighted global collision budget holds |
| A finite sweep has no counterexample | The universal statement is proved |
| A conditional implication is proved | Its candidate antecedent is proved |
| A proof route fails | The candidate is refuted |
| A start lies in `[Q,Q^2)` | Its full 2-gap lies strictly below `Q^2` |
| A square-safe pair survives all smaller filters | An earlier, incompletely filtered pair is already certified |

## Writing Checklist

Before adding or revising a research claim, check:

1. Is the population named precisely?
2. Are the interval and endpoint conventions explicit?
3. Is the statement one-layer, complete-period, local, conditioned-chain, or
   weighted-global?
4. Is its quantifier explicit?
5. Is its evidence or proof status explicit?
6. Are exact identities separated from inequalities and heuristics?
7. If it is conditional, is the unresolved antecedent named?
8. If symbols overlap established uses, are they defined locally?
9. Does “survival” say how many filters are survived?
10. Does a source link point to the proof, verification code, or empirical
    report that supports the stated status?

## Related Guides

- [Proof Guide](PROOF_GUIDE.md) — how article properties are presented in
  English, mathematics, and Stainless code.
- [Candidate Catalog](candidates/README.md) — open sufficient conditions and
  their empirical or algebraic assessment.
- [Sieve-Sequence Property Catalog](properties/sieve-sequence/README.md) —
  established mathematical results and problem boundaries.
- [Object Catalog](OBJECTS.md) — verified Scala objects and lemmas.
- [Verification Learnings](LEARNINGS.md) — durable Stainless techniques and
  failed implementation patterns.

## Maintenance Rule

Add a term here when its meaning crosses document families or when ambiguity
has caused a scope or proof-status error. Keep specialized notation in the
document that uses it, and add a mapping here only when readers must compare
that notation across multiple candidates or properties.
