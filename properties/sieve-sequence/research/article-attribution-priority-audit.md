# Article attribution and priority: first-pass findings

**Date:** 2026-10-21. **Article snapshot:** commit1c99c1bf.
**Status:** Internal editorial/source audit. No publication files changed.

The concern is partly substantiated. Much of the mathematics is classical,
and some later article language can make independently derived or specialized
results sound historically new. However, several foundational articles
explicitly present formal verification of established mathematics. It would
be inaccurate to describe the whole corpus as claiming rediscovery.

Proof correctness, machine verification and historical originality are three
different questions. This audit assesses the last question and its framing;
it does not re-run or certify the verification status of the source code.

## Coverage and limits

Reviewed titles, abstracts, contribution/related-work passages, conclusion
prose and selected theorem/proof sections in the ten primary chapter2–7
articles listed below. The two detailed guides were checked as supplements.
Exact source comparisons concentrate on congruence arithmetic, Euclid's
theorem, and the sieve gap-cycle/count results. This is not a literature-wide
priority certificate for every lemma, conditional model or numerical constant.
Line numbers refer to the unchanged article snapshot above.

| Article | Framing assessment | Evidence |
|---|---|---|
| [Division and Modulo](../../../articles/chapter2/modulo.md) | Established arithmetic formalized through a recursive implementation; no demonstrated historical novelty claim. | Abstract lines17–25 says define/verify; line298 explicitly calls native compatibility a fact that is not mathematically new. The one-residue-per-block result also appears in Gauss1801, sectionI, article3 [G]. |
| [Lists](../../../articles/chapter3/list.md) | Familiar list algebra and a concrete verification package. | Lines59–75 acknowledge long-established list libraries and describe the comparison as contextual rather than competitive. |
| [Cycles](../../../articles/chapter4/cycle.md) | Concrete periodic-sequence representations and their checked equivalence; not a discovery of periodicity. | Title/abstract and Related work, lines63–76, acknowledge existing rotation and cyclic-data work. |
| [Discrete Integral](../../../articles/chapter4/integral.md) | Prefix sums/scan represented and verified in Stainless. | Lines47–61 identify the construction as a prefix scan or accumulation and cite existing fold results. |
| [Cycle Integral](../../../articles/chapter4/integral-cycle.md) | Cumulative sums of a periodic list and concrete representation agreement. | Lines50–82 frame an implementation and cite periodic-function/cycle libraries. A full-period shift and quotient/remainder decomposition are elementary consequences of periodic accumulation. No first-discovery evidence is supplied or needed for the stated formalization aim. |
| [Euclid](../../../articles/chapter5/euclid-theorem.md) | Properly attributed ancient theorem, formalized here. | Introduction lines21–30 names ElementsIX.20; lines579–588 explicitly separate Euclid's argument from the Scala/Stainless formalization. Compare [E]. |
| [Sieve Sequence](../../../articles/chapter6/sieve-sequence.md) | Explicitly claims formal contracts, not the wheel idea. Direct gap-cycle related work should still be added. | Lines52–57 say the contribution is not the wheel idea; abstract lines35–38 disclaims a new sieve algorithm. Its copy/merge and two-strike mechanisms have close earlier counterparts in [H]. |
| [Gap Dynamics](../../../articles/chapter6/gap-dynamics.md) | Highest-priority attribution and novelty-positioning problem in this pass. Some results have verified prior overlap; exact signed/local variants remain unclassified. | Sections3.1–3.4, broad new-theorem wording at line108 and AppendixA lines1761–1763; reference list at line1753 contains only the project's foundation article. Abstract lines30–35 specifically locates the proposed new contribution in signed/local results, so it does not explicitly call every global identity new. |
| [Relaxed Almost-Prime](../../../articles/chapter6/relaxed-almost-prime.md) | Largely careful about classical machinery and Chen; specific algebraic variants need priority review. | Lines86–115 disclaim a new existence theorem, credit Chen and standard sieve machinery, and distinguish the custom population. Line5's broad new-properties wording should be qualified. |
| [Survival Frontiers](../../../articles/chapter7/survival-frontiers.md) | Conditional companion-model calculations using acknowledged classical inputs; originality of the exact model package is unestablished. | Lines164–178 distinguish model identities/conditional results; lines309–311 cite Kochen–Stone; lines555–557 identify classical analytic inputs. The global recurrence is inherited or stipulated by the model, not new prime-distribution information. |

The [Sieve Sequence detailed guide](../../../articles/chapter6/sieve-sequence-detailed.md)
and [Survival Frontiers detailed guide](../../../articles/chapter7/survival-frontiers-detailed.md)
identify themselves as explanatory side versions. They should inherit source
corrections from their main articles, not be assessed as independent discoveries.

## Concrete findings in Gap Dynamics

### 1. The global two-gap product and two-strike mechanism have prior sources

Section3.1 (line152 onwards) derives the count product over installed odd
primes of(q-2). Section3.2 (line211 onwards) derives the two forbidden copy
classes, and section3.3 composes them across batches. Holt and Rudd2014 [H]
already state the product in section1.2 (printed p.3) and the two-gap recurrence
in the proof of Corollary6.3 (printed p.26). Their section2, **Lemma2.1**
(printed p.5), gives expansion followed by gap closures.

Their convention includes the last installed prime in the primorial; ours
indexes a stage by the next head. Align those conventions and a cyclic
rotation before comparing counts. These are genuine earlier overlaps, not
evidence of a new count theorem here. Batch multiplication is a direct CRT
consequence. Add point-of-use citations and classify these as recalled or
independently rederived established results.

### 2. The four-strike constellation mechanism is also earlier work

Section3.4 (line344 onwards) studies the word(2,4,2), with endpoints at
offsets0,2,6,8, and derives(r-4) intact copies. Holt–Rudd [H], printed p.11,
explicitly discuss that word and its four closures. Their Lemma3.1 gives the
general intact-copy factor r-j-1 for length j and span less than2r. For
j=3, span8 and incoming r>=5, those hypotheses hold.

Our total-count recurrence also excludes newly formed clusters: after
filters2 and3, no gap2 can be formed by merging and no gap4 can be formed
from two consecutive2s. That bridge must be retained. The comparison proves
earlier overlap of the intact-copy mechanism; it does not assert that the
whole article's exact wording or every general-modulus variant appears
verbatim in [H]. The prime-quadruplet shape is already called classic in the
article itself.

### 3. Several named results are applications of elementary machinery

Section5.1 (line905) solves the first-order recurrence
N_(i+1)=a_i N_i-b_i by multiplication with later product weights and
telescoping. Section5.2 (line961) applies weighted Cauchy–Schwarz to that
identity. These are standard algebraic mechanisms. The selected sieve
observable and how it organizes the open problem can be useful, but a
specialized notation does not establish a new general conservation principle
or inequality. The article already names Cauchy–Schwarz, so it is not hiding
the inequality's classical origin.

The same distinction applies in section9 (line1403): once the sieve-specific
identification B_j=d_t+d_(t-2) is proved, its energy expansion and bound4V
follow from cyclic reindexing and2xy<=x^2+y^2. The exact sieve identification
needs its own literature comparison; the quadratic inequality is elementary.

### 4. The claimed local contribution is not yet established as old or new

Section7 (line1176) computes a sharp18/7 interval bound on a fixed210-periodic
observable. Its proof lists the weights, takes prefix sums and subtracts
their minimum from their maximum. That method is elementary periodic
discrepancy bookkeeping. The exact observable and sharp constant may still
be a worthwhile specialized calculation. This search did not establish its
historical priority, nor priority of the exact signed/local organization.

Accordingly the abstract's explicit new-contribution language at lines30–35
is stronger than the literature comparison currently supports. Recommend
describing the signed/local calculation and formulation concretely while
leaving priority unclaimed until checked. Do not replace it with an equally
unsupported assertion that the whole result was already known.

### 5. Evidence status currently blurs a separate novelty question

AppendixA groups complete-period and local results as new mathematical
results while its status table distinguishes proved from open. Those labels
do not distinguish established results rederived here from potentially
original claims. Its statement about two external mathematical inputs can
mean unproved dependencies used by the self-contained proofs; it is not
necessarily a historical-origin claim. Nevertheless, it does not provide the
missing prior-work positioning.

Add a distinct provenance classification: established/rederived; formalized
here; specialized consequence/calculation; or priority not established.
Common elementary identities do not each need an invented named discoverer.
Relevant standard references and honest contribution scope are sufficient.

## What the historical-age concern establishes

Some underlying mathematics is indeed centuries old. Gauss's original1801
text [G], sectionI, gives residue classes a+km (article2), exactly one
representative of each class in a consecutive block (article3), and addition
and multiplication rules (articles6–7). These directly overlap the subject
matter of the modulo article; Gauss is a verified early exposition here,
not asserted to be the first discoverer of every rule. Euclid's prime
infinitude theorem is preserved in ElementsIX.20 [E]. The current articles
already frame both subjects as formalization work.

The direct gap-cycle reference [H] is from2014. Thus the verified historical
picture includes both ancient/centuries-old ingredients and more recent
earlier research; it should not be flattened into a single age or priority
claim for the entire project.

## Sources inspected

- **[G] Original historical text:** C. F. Gauss (1801),
  [*Disquisitiones arithmeticae*, sectionI](https://www.e-rara.ch/download/pdf/1706845.pdf),
  ETH-Bibliothek scan, arts.2–7. OCR is imperfect; section/date and the
  relevant statements are identifiable. This is earlier evidence, not an
  all-encompassing first-discovery attribution.
- **[E] Original theorem in an online edition:** Euclid,
  [*Elements*, BookIX, Proposition20](https://mathcs.clarku.edu/~djoyce/elements/bookIX/propIX20.html),
  David E. Joyce's edition. Its finite-list construction uses a common
  multiple plus one; the article explains its product specialization.
- **[H] Earlier research paper:** Fred B. Holt and Helgi Rudd (2014),
  [*Eratosthenes sieve and the gaps between primes*](https://arxiv.org/pdf/1408.6002v1),
  section1.2, Lemma2.1, Lemma3.1 and Corollary6.3. Locations above refer to
  v1. No claim that this was the first publication of every covered identity.
- **Modern reference for square-root certification:**
  [NIST DLMF27.18](https://dlmf.nist.gov/27.18). It supports identifying the
  square-safe step as a classical sieve consequence; it is not an original
  historical source for its discovery.

## Recommended editorial action

Prioritize Gap Dynamics: add the direct gap-cycle/count references, identify
the recalled global results, narrow unsupported novelty wording, and position
the signed/local calculations against the literature. Add Holt–Rudd to Sieve
Sequence's related-work comparison while preserving its correctly stated
formalization scope. Qualify broad new-properties wording in the relaxed
article; retain its existing Chen/standard-machinery distinctions. Keep the
companion-model assumptions and classical citations explicit.

These recommendations have not been applied to publications in this audit.
Any implementation must update paired arXiv sources and pass build/parity
gates. Potential originality of specific local variants and of particular
formal proof artifacts remains a separate, unfinished literature question.
