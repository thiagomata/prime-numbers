# Scientific Merit Review: `articles/`

You're right that the first pass was a style/compliance audit, not a review. A real referee for a
magazine doesn't check whether the paper followed its own house style guide — they ask: is this
true, is it new, does it matter, and who is the audience that should care. This is that pass. I
checked the mathematical claims against the literature (sources at the bottom) rather than just
against this repo's own rules.

## The one-sentence verdict

This project is really two different pieces of work wearing the same "chapter" numbering, and they
should be judged completely differently: chapters 2-5 (modulo, lists, cycles, integrals, Euclid) are
a **solid but non-novel verified-arithmetic exercise** — correct, well-engineered, and already-known
mathematics; chapter 6 (gap-dynamics, sieve-sequence) is where the **actual research question**
lives, and it is honestly scoped but is very likely running into one of the oldest, hardest
obstructions in analytic number theory without naming it.

---

## Part 1: Chapters 2-5 are engineering, not new mathematics — and that's fine, but say so

`modulo.md`, `list.md`, `cycle.md`, `integral.md`, `integral-cycle.md`, and `euclid-theorem.md` prove
things like: modulo is idempotent, sum distributes over list concatenation, a cycle's value doesn't
change if you add a multiple of the period, and there are infinitely many primes. None of this is new
— these are textbook facts, several centuries to two millennia old in the mathematical sense. That's
not a criticism of doing the work; formalizing "obvious" facts from scratch, with no library
shortcuts, is genuinely tedious and is exactly the kind of thing that catches subtle definitional
bugs. But it means the *contribution* here isn't mathematical, it's an engineering one: a
self-contained, dependency-free, machine-checked arithmetic stack built in Stainless.

Two things a real reviewer would ask before accepting that contribution as noteworthy:

**Has this already been done?** Euclid's theorem specifically has been formalized dozens of times —
there's a whole survey paper cataloguing its proofs from 300 BC to 2022, and Lean's mathlib has had
it as `Nat.exists_infinite_primes` for years, alongside Coq, Isabelle/HOL, and HOL Light versions.
Re-proving it in Stainless isn't wrong, but the article should say plainly that this is a
well-trodden formalization exercise, not present it as if verifying Euclid's theorem is itself
noteworthy. The current abstract and conclusion don't overclaim, to their credit, but they also don't
situate the work against this very well-known formalization history — a reader outside this repo
would have no idea this has been done many times before in more mature proof assistants.

**Does Stainless already have this?** EPFL-LARA (Stainless's own team) maintains `bolts`, a public
repository of Stainless-verified examples — data structures, algorithms, a compiler, System F
soundness, red-black trees. I didn't find prime-number or modular-arithmetic content in it, so the
specific material here doesn't appear to duplicate an existing Stainless example. That's a genuine
(small) point in this project's favor for the formal-methods/verification-tooling audience
specifically — "here is a from-scratch, zero-dependency verified arithmetic stack in Stainless" is a
plausible contribution to *that* community (think a workshop paper or tool-demo track at ITP/CPP/NFM,
not a number theory journal), especially if it's positioned as a case study in `.holds` caching and
proof engineering rather than as new mathematics.

**Bottom line for chapters 2-5:** correct, careful, not novel as mathematics. If this is being framed
for "a scientific magazine," the honest framing is "a verified-arithmetic engineering case study,"
not "new results in number theory." The current framing is close to honest already (no false novelty
claims), but it undersells the real audience question: this belongs in front of formal-methods
readers, not number theorists, and the article text doesn't currently make that audience choice
explicit.

---

## Part 2: Chapter 6 is where the real question is — and it's harder than the article lets on

`gap-dynamics.md` and `sieve-sequence.md` are a different animal. Here the project actually engages
a real open problem: does the sieve-of-Eratosthenes-style construction generate twin primes forever?
The article is honest about not proving this — it explicitly says "It does not claim a proof of the
Twin Prime Conjecture" and marks the local-density question as open. That honesty is worth crediting;
plenty of amateur number theory doesn't have it. But there's a deeper issue a real referee would
raise, and it's not in the article at all.

### The parity problem

The specific move this project makes — reduce twin-prime persistence to a **counting/capacity
argument** over a sieve construction (does the local supply of 2-gaps in a window exceed the number
of "filter strikes" that could destroy them) — is structurally the classic sieve-theoretic approach
to prime gaps. Atle Selberg identified in 1949 that this style of argument has a hard ceiling: sieve
methods, on their own, cannot distinguish numbers with an even number of prime factors from numbers
with an odd number (primes have exactly one), which means pure counting/sieve arguments are
provably incapable of establishing lower bounds for primes or twin primes without injecting some
extra analytic ingredient beyond the sieve itself. This is exactly why the actual advances on
prime-gap problems (Zhang's 2013 bounded-gaps proof, later improved by Polymath and by
Maynard-Tao down to a gap of 246, and under stronger conjectures to 6) needed genuinely new
analytic machinery — not just a better sieve, but techniques specifically designed to route around
the parity obstruction.

The project's own internal notes (`articles/learnings/learnings-capacity-argument.md`) name the
open question as "equivalent to the Twin Prime Conjecture in this framework" — but nowhere in the
article or the learnings file is the parity problem mentioned. If the local-density question really
does reduce to "does a pure counting argument over sieve residues detect twin primes," there's a real
chance this isn't a gap that more Stainless proof engineering will close — it may be provably out of
reach for this exact style of argument, the same way it's been out of reach for a century of sieve
theory. A serious reviewer would ask the authors to either (a) explain why their construction
sidesteps the parity obstruction, or (b) acknowledge the connection and reframe the open question as
"this capacity argument, like all pure sieve arguments, likely cannot resolve the local-density
question on its own" rather than presenting it as an engineering problem awaiting more verification
work. This is a caution about the local question itself, not about how it connects to the rest of the
article — see the credit given below for how cleanly that connection is handled.

### Credit where due: the global/local boundary is handled honestly, not sloppily

§5 ("Global versus Local Survival") proves a global growth bound (§4) and then explicitly fences it
off from the local question in §5.3: "global survival does not imply safe-window survival." §6 then
poses the local question ($G_{\text{local}}(p) > p$) as its own separately-labeled open problem,
without pretending the global result supports it. That's the right way to handle an incomplete
result — prove what's provable, name the boundary, don't blur the two. An earlier draft of this
review misread that boundary as a missing derivation the authors owed the reader; it isn't. The
global result stands on its own; the local question is honestly open; nothing here needed fixing.

### The empirical evidence is being asked to do work it can't do

`gap-dynamics.md` reports the inequality holding for all tested primes from $p=37$ to $p=997$ (166
layers), which is a fine, honest thing to show as illustration — a table or a graph of "here's what
we observed" is legitimate context. The problem is the sentence right after it: the growing ratio is
described as "suggesting the inequality is structural, not coincidental." That's not illustration
anymore, that's using the data to argue toward the open claim, and given the global/local boundary
established one section earlier, there is nothing else the empirical numbers could be leaning on —
they're the entire basis for that sentence. Number theory has a long, well-known history of patterns
that hold for enormous computational ranges and then fail: the Mertens conjecture was verified far
beyond what was computationally reasonable by hand and was still eventually disproved; Skewes' number
is the canonical example of a prime-counting inequality flipping only at astronomically large,
uncomputed scales. $p=997$ is nowhere near that kind of range — it's the range where almost any
smooth heuristic looks clean. Show the data, show the graph, and stop there; drop "structural, not
coincidental" (and the similar framing in `draft-empirical-g-local-analysis.md`), since the very next
sentence in the article ("empirical evidence is not a formal proof") already concedes the point that
sentence just undercut.

### A process concern, not an article concern

`articles/learnings/reviewer-notes-gap-dynamic.md` is a transcript-style document that reads like an
AI assistant enthusiastically validating the user's derivations ("Great catch," "airtight,"
"unassailable," "a closed, self-balancing thermodynamic engine," "the loop is perfectly sealed").
This isn't a knock on the finished article — `gap-dynamics.md` itself is properly hedged — but as
someone reviewing the whole research process, I'd flag this file as a risk: it's not independent
peer review, it's collaborative brainstorming with a model that defaults to validating whatever
framing it's given, and its confident tone doesn't track actual mathematical certainty. If this
document was influential in shaping how confident the author feels about the capacity argument, it's
worth discounting that confidence back down and re-deriving it from the math alone, ideally with an
actual number theorist or a more adversarial review pass rather than a conversational one.

**Bottom line for chapter 6:** this is the one part of the project with real research content, and
it's the one part that most needs contact with the existing sieve-theory literature (specifically the
parity problem) before its scope claims can be trusted. The honesty about not proving the Twin Prime
Conjecture is good; the honesty doesn't yet extend to acknowledging *why* this specific style of
argument is suspected to be structurally incapable of closing the gap.

---

## What I'd tell an editor

If this came across my desk for "a scientific magazine": chapters 2-5 are correct and well-executed
but not new — fine as an engineering/tools writeup for a formal-verification audience, not
publishable as number theory. Chapter 6 is the interesting part, but it's not ready to be presented
as a research contribution to a number-theory audience until it engages with the parity problem and
either explains why the capacity argument avoids it or reframes the open question as likely
unreachable by this method alone. As pure documentation of a well-engineered formal-verification
project with an honestly-scoped open research question attached, it's solid. As a claim to be
advancing the twin prime problem, it needs the literature context it's currently missing.

---

## Addendum: Recommended citations for `gap-dynamics.md`

Discussed and refined with the author after this review. The goal was a small number of references
that each anchor a claim already made in the text — not general "related work" padding — so the
article stays self-contained. Final set, in the article's existing numbered-reference format:

1. **Halberstam, H. & Richert, H.-E. (1974). *Sieve Methods*. London Mathematical Society Monographs
   4. Academic Press.** — anchors the "equivalent to the Twin Prime Conjecture in this framework"
   line in §8 Future Work; names the parity-problem limitation shared by pure sieve/counting
   arguments generally, without claiming this project's construction is exempt from it.
2. **Rubinstein, M. & Sarnak, P. (1994). "Chebyshev's bias." *Experimental Mathematics*, 3(3),
   173-197.** — anchors "empirical evidence is not a formal proof" in §6. A tighter analogy than an
   earlier draft's Mertens-conjecture suggestion (that one was rejected as a weak link — Mertens is
   zeta-zero cancellation, a different mechanism). Chebyshev's bias is specifically about a
   residue-class distribution statistic that looks completely stable over any computationally
   reasonable range and still isn't a fixed asymptotic fact — the same genre of claim as
   $G_{\text{local}}(p) > p$, and on-topic (residue classes, prime distribution) rather than borrowed
   from an unrelated corner of the field.
3. **Zhang, Y. (2014). "Bounded gaps between primes." *Annals of Mathematics*, 179(3), 1121-1174.**
   — anchors a one-line note (Future Work or Related Work) that the one unconditional advance on
   prime gaps to date came from techniques outside pure sieve counting, reinforcing (1) without
   belaboring it.

All three attach to sentences already in the article; none introduce a new claim the article doesn't
already make.

---

Sources:
- [Bolts: Stainless Verified Scala Examples (epfl-lara/bolts)](https://github.com/epfl-lara/bolts)
- [Stainless Verification System Tutorial (Kuncak et al.)](https://repositum.tuwien.at/bitstream/20.500.12708/18609/1/Kuncak-2021-Stainless%20Verification%20System%20Tutorial-vor.pdf)
- [Euclid's theorem on the infinitude of primes: a historical survey of its proofs (300 B.C.-2022) and another new proof](https://arxiv.org/pdf/1202.3670)
- [data.nat.prime - mathlib3 docs](https://leanprover-community.github.io/mathlib_docs/data/nat/prime.html)
- [Open question: The parity problem in sieve theory - Terence Tao](https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/)
- [Parity problem (sieve theory) - Wikipedia](https://en.wikipedia.org/wiki/Parity_problem_(sieve_theory))
- [Twin primes and the parity problem (Queen's University)](https://mast.queensu.ca/~murty/TwinPrimes-Parity.pdf)
- [Bounded gaps between primes (Polymath project retrospective)](https://arxiv.org/abs/1409.8361)
- [BOUNDED GAPS BETWEEN PRIMES - Andrew Granville](https://dms.umontreal.ca/~andrew/CurrentEventsArticle.pdf)
