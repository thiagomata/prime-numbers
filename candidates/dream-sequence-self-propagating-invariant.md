# The Dream Sieve Sequence: A Self-Propagating Two-Gap Invariant

**Candidate hypothesis:** Unproved and potentially false. **Nonemptiness is
deliberately not claimed**: no real or constructed sieve sequence is
asserted to satisfy the invariant. The object under study is the invariant
itself.

**Conditional implications:** Mathematically proved where marked. The
perpetuity theorem is proved unconditionally as an implication; the global
component of the invariant is provably conserved; the local component's
preservation is open and stated as the remaining lemma.

**Empirical status:** ALGEBRA-FIRST — built from the proved exact
transition laws; the next actions are the two named preservation lemmas,
not measurement.

## The Inversion

**The formal object (definable now).** Let `C(seq)` denote "this stage's
safe window contains a 2-gap". The family of self-propagating
certificate-properties is closed under disjunction, so it has a greatest
element — the dream sequence itself, defined coinductively:

```math
\mathcal P^{*}=\nu X.\bigl(C\wedge\mathrm{next}^{-1}(X)\bigr)
=\text{“every descendant certifies”},
```

together with its weak twin

```math
\mathcal P^{\infty}(\mathrm{seq})
=\text{“always eventually some descendant certifies”}
=\forall k\,\exists j\ge k:\ C(\mathrm{seq}_j).
```

Both are hereditary by construction; both deliver infinitely many
distinct certificates from a single seed; and `P^infinity` at any real
stage is *equivalent* to infinitely many twin primes. The dream is
therefore fully stated. What does not exist yet is its **interface**: a
structural, finitely checkable property `P` with `P subset P*` and proved
closure — in verification language, an **invariant strengthening** for a
coinductively defined greatest fixed point. The components below are the
first fragments of that strengthening; Lemma A is the missing local
fragment.

Candidate #2 asks, at each transition, whether the parent's window surplus
covers the next filter's strikes — a per-step hypothesis that must be
re-established at every layer. This candidate inverts the direction:
**exhibit a structural property set `P` over sieve sequences that (a)
guarantees a square-safe 2-gap, and (b) reproduces itself under the sieve
transition.** If any stage of any sequence ever satisfies `P`, then every
descendant does, and every subsequent head carries a twin-prime
certificate.

The structure of the argument is then a single existential plus a closed
induction:

```math
\bigl(\exists k_0:\ \mathcal P(\mathrm{seq}_{k_0})\bigr)
\ \wedge\
\bigl(\mathcal P\Rightarrow\mathcal P\circ\mathrm{next}\bigr)
\ \wedge\
\bigl(\mathcal P\Rightarrow\text{safe-window 2-gap}\bigr)
\;\Longrightarrow\;
\text{infinitely many distinct twin primes}.
\qquad[\text{Perpetuity Theorem; Q.E.D.}]
```

The proof is induction on layers; distinctness of certificates follows from
the bounded-coverage argument (a fixed pair certifies only finitely many
heads). Everything hard is isolated into the two conjuncts on the right:
one closure lemma and one seed existential.

### The Recurrent Generalization

Direct heredity is the special case `J={1}` of the weaker **recurrence**
requirement

```math
\mathcal P(\mathrm{seq})
\ \Longrightarrow\
\exists j\ge1:\ \mathcal P(\mathrm{seq}_j),
```

and the perpetuity theorem survives verbatim: a seed plus guaranteed
return generates an infinite strictly increasing sequence of `P`-stages,
each certifying, hence infinitely many distinct twin pairs. The
recurrent form matches how the per-step candidates are actually stated
(#2 asks for surplus at *infinitely many* transitions, not all) and how
the article's head-recurrence machinery works (Borel–Cantelli is an
"infinitely often" structure).

Two consequences for the open lemmas:

- **Worst-case-per-layer becomes integrated.** The obstruction that kills
  naive Lemma A is the per-layer degradation product `prod(1+2S/r)`,
  which diverges. Under recurrence the requirement weakens to: integrated
  degradation over a dormancy window is below the growth of the scale
  threshold over the same window — an *averaged* statement of exactly the
  shape the mean-square machinery of
  [window innovation orthogonality](window-innovation-orthogonality.md)
  produces. Bad layers become absorbable (Lemma A′).
- **Recovery runs through the threshold, never the spacing.** 2-gaps are
  only destroyed, never created, so the absolute spacing between
  consecutive 2-gap starts is monotone non-decreasing across all layers —
  absolute recovery is structurally impossible. `P2` can re-qualify only
  because the scale threshold `S(Q) ~ C log^2 Q` grows faster than the
  integrated degradation and catches up. Together with the decay
  constraint, this completes the design rule: **every component must be
  scale-relative; no component may be monotone-absolute.**

## The Mirror

[Absence of 2-gaps is stable](../properties/sieve-sequence/absence-of-two-gaps-is-stable.md)
proves that the **nightmare invariant** — "no 2-gaps at all" — is
hereditary: a 2-gap-free stage has only 2-gap-free descendants, forever.
The dream invariant is its mirror, and the asymmetry between them is the
whole difficulty: destruction is one-way, so absence preserves itself for
free; presence must survive the exact two harmful copy classes at every
layer, which requires surplus and distribution, not just existence.

### The Space Of Dreams

The definition is canonical; the implementations are plural.

- **Canonical targets: exactly two.** `P*` and `P^infinity` are greatest
  fixed points determined by `C` and the transition — not design choices.
- **Interfaces: a lattice.** Valid strengthening invariants are closed
  under both disjunction (each disjunct guarantees its own recurrence and
  certificate) and conjunction, so they form a lattice between falsity
  and `P^infinity`. The components of this file are one member; a
  #27-style Gram-typicality interface or a #24-style energy interface
  would be others. Lemma A′ failing does not sink the program — only
  this lattice element.
- **Witness sequences: a constructible class.** Nonemptiness in the
  abstract is trivial — a protective-placement policy always sparing a
  window target explicitly builds a `P*` sequence (the §5.2 companion at
  full protection). The open question is membership of the **real
  chain**: `P^infinity` holds at one real stage iff it holds at every
  real stage iff there are infinitely many twin primes.

## Component 0 (Proved): Perpetual Presence In Compressed Coordinates

By the [2-focused compression alternation law](
../properties/sieve-sequence/two-focused-alternation-law.md), every
post-3 stage's 2-focused compression has cells strictly alternating
2-cell / run-cell, so **exactly half the compressed cells are 2-gaps at
every stage** — a perpetual, scale-free presence structure requiring no
lemma. In these coordinates the decay constraint relocates entirely into
the run values (average run `= 1/density - 2 ~ (1/C) log^2 Q`), and the
open local content becomes pure run-value control: a window fails
exactly when a run sum exceeds it, so Lemma A′ is equivalently a
max-run-value law at the Mertens scale.

## Component 1 (Proved): The Conserved Mertens Ratio

Let `N` be a sequence's complete-period 2-gap count and `Pi` its period.
Two proved exact laws — every parent leaves exactly `r-2` copies, and the
period scales by `r` — give, for **every** transition and **every**
placement policy:

```math
\frac{N_{\mathrm{child}}/\Pi_{\mathrm{child}}}
{\prod_{r\ \mathrm{installed}}(1-2/r)}
=
\frac{N_{\mathrm{parent}}/\Pi_{\mathrm{parent}}}
{\prod_{r\ \mathrm{installed}}(1-2/r)}.
```

The global 2-gap density relative to the Mertens benchmark is an exact
**conserved quantity** of the dynamics (validated stage-by-stage on the
post-3 chain: ratio `1/6` at every layer). Therefore the band property

```text
P1:  kappa = N / (Pi * Mertens)  in  [kappa_min, kappa_max]
```

is hereditary for free — this component of the dream invariant closes
today. Note what this does and does not say: it pins the global count at
every descendant stage; by the [Past-Span Saturation property](
../properties/sieve-sequence/past-span-saturation-does-not-determine-placement.md),
no global property can determine window content — which is exactly why the
invariant needs a second, local component. The design is forced: a dream
invariant built only from complete-period quantities cannot certify
anything.

## Decay Compatibility (Hard Design Constraint)

The absolute count increases at every layer, but the 2-gap **density
provably decreases at every layer, forever**, by the exact factor
`(r-2)/r`. Any strengthening invariant `P` submitted for Lemma A or
Component 3 must therefore be compatible with perpetual decay:

1. **No absolute-density floors.** A property requiring density `>= c > 0`
   is refuted in finitely many layers by the exact recurrence — this is a
   zero-cost falsifier to run on every proposed invariant: it must survive
   the exact map `(N, Pi) -> ((r-2)N, rPi)`.
2. **All quantities are scale-relative.** `P1` pins only the conserved
   ratio `kappa` (the benchmark itself decays); `S(Q)` must *grow* on the
   Mertens scale (`~ C log^2 Q`) precisely because the density decays on
   that scale — spacing and density are the same scale read from opposite
   sides.
3. **The certificate engine is growth of the window, not of the density.**
   What forces `|W_q ~ q^2|` to contain a 2-gap despite falling density is
   that the window length outruns the spacing scale:
   `q^2 >> C log^2 q`. The dream survives *because* both the count and the
   window grow while the density falls; it must never ask the density to
   stop falling.

## Component 2 (Open): Local Spacing With Slack

```text
P2:  consecutive 2-gap starts over the whole cycle are spaced at most
     S(head) apart, with slack calibrated to the Mertens scale.
```

P2 with `S << r/2` is what forces window occupancy (any window of length
`>> S` contains a 2-gap) and what the certificate consumes. Its
preservation analysis: the next filter kills exactly the starts at
`v = 0, -2 (mod r)` — deterministic arithmetic, `<= 2*length/r + 2` kills
in any stretch — so parent spacing `S` degrades to child spacing at most
`~ 2Sr/(r-2S)`, a factor `1+2S/r` per layer. The product of these factors
over prime layers **diverges** (`sum S/r` over primes diverges for any
non-shrinking `S`), so naive slack does not close: `S` must be calibrated
to grow with the Mertens scale, and the preservation lemma becomes:

> **Open Lemma A (spacing self-preservation).** There is an explicit
> scale function `S(Q)` (heuristically `~ C log^2 Q`) such that `P2` at
> scale `S` implies `P2` at scale `S` again at the child.

Two facts make Lemma A plausible rather than hopeless. First, the
per-layer kill fraction is `2/r`, exactly the rate the Mertens scale
already absorbs — the destruction and the density decay are the same
arithmetic, so the scale is self-consistent. Second, by the
[2-Gap Placement Saturation property](
../properties/sieve-sequence/two-gap-placement-saturation.md), the real
filter's surviving pair counts are *rigidly elevated* at separations
`h = 0, +-2 (mod r)` (the exclusion-intersection wastes strikes in the
child's favor) — the kill geometry is maximally spread, never clumped on
neighbors; an adversarial placement need not be granted in Lemma A
because the transition is the real one.

Lemma A is the open core of the existing hereditary program: candidate
#14's exact spacing certificates hold at every defined layer measured,
and its open part — universal close-pair existence and population
control — is precisely the seed-free fragment of Lemma A.

## Component 3 (Open, minor): Certificate Bridge

```text
P3:  every sub-window of length H(q) contains at least one 2-gap start
     with both endpoints coprime to the next incoming prime.
```

P3 converts spacing into a certificate that survives one filter. Its
preservation follows from P2 plus counting (`2H/r+2` bad starts per
stretch) whenever `H` is calibrated between `S` and `r/2` — the
calibration exists at large heads; the lemma to close is routine once
Lemma A's scale is explicit. Marked open only because it depends on
Lemma A's constants.

## Lemma A' Calibration (Deep-Dive, 2026-08-18)

Three facts pin the lemma's exact strength and location.

**Fact 1 (identity of the run object).** Post-2, a value `v+1` between
`v` and `v+2` is even and dead, so "consecutive" is automatic: the set of
2-gap starts is *exactly* the dimension-2 sifted set
`{v : v, v+2 both coprime to every installed prime}` (validated on
complete periods). Runs are literally the gaps of that set, and its
complete-period pair statistics are already exact via the
[Pair Local Factor property](
../properties/sieve-sequence/two-gap-pair-local-factor-by-separation.md).

**Fact 2 (exact equivalence class).** Within the safe window
`[Q, Q^2)`, a sifted pair is a twin-prime pair (any composite below
`Q^2` has a factor below `Q`). Therefore:

```text
weak run law:   infinitely many windows contain a start
                 <=>  infinitely many twin primes   (exactly equivalent)

strong run law:  eventually every window contains a start
                 =>   infinitely many twin primes   (strictly stronger;
                      infinite twins do not preclude an occasional
                      empty window)
```

The dream interface at the `P^infinity` level needs only the weak form —
and proving it IS proving the twin-prime conjecture. Lemma A' is not a
cheaper lemma on the way; it is the target itself wearing work clothes.
Any strategy document claiming to prove the weak run law "first, then
transfer" is circular.

**Fact 3 (the dimension map).** The dimension-1 sibling of the run law
is a solved classical problem: the Jacobsthal function `j(n)` (maximal
gap between integers coprime to `n`) satisfies the classical bounds
`j(n) << omega(n)^2 log^2 omega(n)` (Iwaniec; cruder
`j(n) <= 2 omega(n)^2`-type bounds suffice qualitatively). For the
primorial with `omega = pi(Q) ~ Q/log Q` this is `<< Q^2 (1+o(1))` —
essentially window scale: **the single-survivor analogue of the run law
closes at window scale with known tools.** The open jump is exactly one
dimension: from gaps of the 1-sifted set to gaps of the 2-sifted set.
This locates Lemma A' one dimension above a solved problem, consistent
with #5's deferral classification of the whole-period Jacobsthal form
as too strong, and prescribes the correct target: the
**infinitely-often, window-restricted, dimension-2 Jacobsthal bound**.

## What Would Close the Program

1. **Lemma A′ (recurrent form, preferred)** — integrated degradation of
   scale-relative spacing stays below threshold growth over dormancy
   windows: an averaged statement, the natural product of mean-square
   machinery. **Lemma A (direct form)** — per-layer preservation, the
   special case `J={1}`: stronger than needed and currently blocked by
   the divergent worst-case product.
2. **Lemma B (routine, after A′)** — the P3 calibration.
3. **The seed** — `exists k0 P(seq_k0)`. Explicitly not claimed, not
   measured, and not approachable by finite data: the seed is a
   short-window lower-bound statement of the same parity-barrier class
   identified in [local surplus](local-surplus.md) and
   [short-window discrepancy](short-window-discrepancy.md). What the
   inversion buys is that the seed is needed **once**, not at every layer.

## Limitation

- The perpetuity theorem is only an implication; without a seed it
  certifies nothing about the real sieve.
- **Decay compatibility binds every component**: density falls forever by
  the exact law; any invariant needing non-decaying absolute density is
  refuted in finitely many layers (see the falsifier in Decay
  Compatibility). `S(Q)` must grow on the Mertens scale, never shrink.
- Lemma A may be false at every explicit scale function; the divergence
  of the naive degradation product is a real obstruction, and only the
  rigid kill geometry (spread classes, elevated survival at `h = +-2`)
  gives reason to expect a self-consistent scale exists.
- The invariant deliberately conditions on the real transition; it makes
  no claim that other placement policies preserve P2 — unlike the global
  component, P2's preservation must use where the real filter kills, not
  just how much it kills.

## Related

- [Local surplus](local-surplus.md) — the per-step version; this
  candidate is its inductive closure.
- [Hereditary shot-spacing capacity](hereditary-shot-spacing-capacity.md)
  and [Seven-layer capacity floor](seven-layer-capacity-floor.md) — the
  existing hereditary-capacity program; Lemma A is its open core.
- [Absence of 2-gaps is stable](
  ../properties/sieve-sequence/absence-of-two-gaps-is-stable.md) — the
  nightmare mirror, proved hereditary.
- [Two-gap placement saturation](
  ../properties/sieve-sequence/two-gap-placement-saturation.md) — the
  rigid kill geometry Lemma A relies on.
- [Past-span saturation](
  ../properties/sieve-sequence/past-span-saturation-does-not-determine-placement.md)
  — why the invariant must carry a local component.
- [Window innovation orthogonality](window-innovation-orthogonality.md) —
  the mean-square form of Lemma A's distribution content.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §3.1](
  ../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
  — the exact global recurrence behind Component 1.
- Ticket `tickets/active/spectral-positional-filter-analysis-2026-08-18.md`
  — working memory.
