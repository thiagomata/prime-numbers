# Review of Draft Articles — Scientific Quality Assessment

**Date:** 2026-08-15
**Scope:** All six documents in `articles/draft/`, reviewed as scientific papers
(mathematics / formal-verification scholarship), not only against repository
guidelines. Each article is assessed on: abstract/introduction/conclusion
integrity, mathematical rigor and correctness of sketched proofs, statement of
premises and claim boundaries, literature engagement, notation and terminology,
redundancy and structure, reproducibility of empirical claims, and statistical
soundness.

| # | Article | Type | Overall assessment |
|---|---------|------|--------------------|
| 1 | `draft-sieve-foundation.md` | Verified lemmas (bridge article) | Solid, small scope; redundant middle; missing scholarly apparatus |
| 2 | `exercise-local-safe-window-capacity.md` | Pedagogical exercise | Well-posed tasks; not a paper; needs solutions and cross-links |
| 3 | `draft-empirical-g-local-analysis.md` | Superseded empirical record | Honest labeling; interpretive analysis outlives its superseded data |
| 4 | `draft-sieve-gap-survival-math.md` | Superseded mathematical exploration | Good core math; successor section is under-anchored notation |
| 5 | `draft-relaxed-almost-prime-sieve-sequence.md` | Analytic-sieve draft (unverified) | Best claim discipline in the set; zero external citations is a serious gap |
| 6 | `draft-adversariality-phase-transition-2-gap-companions.md` | Probabilistic companion models + empirics | Most substantial; heavy premise load, duplicated results, unstated Poisson/negative-association step |

---

## Cross-Cutting Issues (apply to several or all drafts)

### C1. No engagement with the external literature

This is the single largest scientific weakness of the set. The articles operate
in territory with a deep classical literature, yet cite almost nothing
external:

- The companion/random-benchmark analysis (draft 6) is structurally a
  **random-sieve / Cramér-type model** with a **Borel–Cantelli recurrence**
  argument. The informal prime heuristics of Cramér, Gallagher's work on the
  distribution of primes in short intervals and k-tuples, and the large body of
  work on random sieves are the natural comparison class. None are cited; only
  Kochen–Stone and Hardy & Wright are.
- Draft 5 rebuilds (correctly, as far as the algebra goes) pieces of the
  standard **Chen-type weighted sieve** setup: the relaxed weight
  `a_Q(n) = 1_{gcd(n,W)=1} · 1_{gcd(n+2,Z)=1}` is precisely the usual
  lower-bound-sieve sifting sequence with level `z = X^α`, and the
  §7 refutation is an instance of the **sieve parity barrier** (residue-class
  distribution modulo 3 breaking scalar-density models). The article says
  "Classical Chen theory already supplies..." but cites no source. A referee in
  analytic number theory would reject the paper for this alone.
- Draft 3 invokes Mertens' theorem and the prime number theorem by name only.

**Improvement:** add a real bibliography to every draft that makes analytic
claims (at minimum: Chen 1973; Halberstam–Richert, *Sieve Methods*;
Iwaniec–Kowalski; Gallagher 1976; Cramér 1936; Li–Pan style weighted-sieve
surveys where relevant), and add a short "Relation to known results" paragraph
positioning each construction against it. For draft 5 especially, state
explicitly which parts are standard and which are project-specific.

### C2. No theorem numbering

No draft numbers its theorems, lemmas, or propositions. Results are referenced
by section ("§3.5", "the allocation theorem in §5"), which is brittle under
revision and makes external citation of a specific result impossible. The
phase-diram tables partly compensate, but a formal statement environment
(Theorem 1, Proposition 2, ...) with a premises list would materially improve
scholarly usability — especially in drafts 5 and 6 where the precise premise
set of each result is the whole point.

### C3. Inconsistent front matter and status labeling

- Drafts 3, 4, 5 carry full author blocks; drafts 1, 2 carry none; draft 6 has
  an author block but **no status line at all** (it never says "draft",
  "not Stainless-verified", or a date).
- Status semantics vary: "Draft", "Superseded historical draft", "Review
  draft", "Draft exercise". A single status vocabulary (draft / superseded /
  refuted / exercise / ready) applied uniformly, plus a date on every document,
  would prevent misreading.

### C4. Notation drift across the set

- Safe window: `[h, h²)` (draft 4), `[q, q²)` (draft 2), `[Q, Q²)` (drafts 5,
  6); the head is `h`, `p`, or `Q` depending on the file.
- Draft 6 alone carries four normalized damage quantities (`w_r`, `α_r`,
  `κ_r`, `θ_r`); draft 4's successor section invents another notation system
  (`a_i, A_{u,v}, w_i, W_-, E_b, b_i`) used nowhere else.

**Improvement:** a shared notation section (or a `VOCABULARY.md` mapping)
fixing head symbol and window convention across all drafts, and a table in
draft 6 reducing `κ` explicitly to `w` where they coincide (the text
acknowledges the equality once, then keeps both symbols).

### C5. Inconsistent math rendering

Drafts 1, 4, 5, 6 use the repo-standard ```math LaTeX blocks; draft 3 uses
`$...$` / `$$...$$` and draft 2 uses plain ```text blocks. Whichever the
article pipeline renders, the set should be uniform, since draft 3's inline
math may silently fail to render in the same pipeline.

---

## 1. `draft-sieve-foundation.md`

**Summary.** Bridge article between arithmetic chapters and the full
sieve-sequence specification: five small verified lemmas (unit-cycle candidate
generation, strict monotonicity, distinct primes don't divide each other,
filter preserves other primes, filtered lists contain surviving primes).

### Strengths

- Honest, narrow scope; §8 ("Boundary") explicitly refuses claims the article
  does not prove — exemplary framing integrity.
- All three representation forms present with source links; proofs match the
  displayed Scala.
- Clean pedagogical ordering from generation to filtering.

### Issues

1. **Redundant middle (major).** §4 and §5 prove the *same statement*.
   `assertFilterPreservesAllPrimes` (§5) is literally
   `assertPrimeNotDivisibleByDistinctPrime` (§4) with the argument renamed
   `p → filterPrime`. A paper would state the lemma once and note the filter
   reading as a corollary in one sentence. As written it inflates the lemma
   count (five claimed, four substantively distinct).
2. **Missing scholarly apparatus (moderate).** No author block, no date, no
   references section, no property/status index — inconsistent with the other
   drafts and with what a paper needs even in draft form.
3. **§6 quantifier mismatch (minor).** The math statement quantifies
   `q ∈ L ∧ isPrime(q) ∧ ...` but the Scala lemma is named
   `assertFilteredContainsAllPrimes` and takes `originalPrimes` — nothing
   requires the *other* elements of the list to be prime. The lemma is correct
   as coded, but the name and the surrounding prose ("original primes")
   suggest a stronger hypothesis than is either stated or needed. Either
   rename (`...ContainsPrimeQ`) or state the actual (weaker, fine) hypothesis.
4. **Induction prose is thin (minor).** "the induction hypothesis advances by
   exactly one" is a gesture, not a proof sketch; one more line exhibiting the
   recursive-step identity would make the math self-contained without the code.
5. **No forward map (minor).** §7 lists what the bridge gives but does not
   name *which* verified properties of the sieve-sequence article consume each
   lemma. A dependency table would let a reader verify the bridge claim rather
   than trust it.

### Improvements (priority order)

1. Merge §4/§5 into one lemma + corollary remark.
2. Add front matter, date, property index with verification status, and
   references (internal links suffice here).
3. Fix the §6 naming/quantifier mismatch.
4. Add the one-line recursive-step display to §2 and a lemma-dependency table
   to §7.

---

## 2. `exercise-local-safe-window-capacity.md`

**Summary.** Guided exercise: prove the half-open-interval multiple-count
formula, bound filter strikes by `R(p,q)`, bound destroyed 2-gaps by
`2·R(p,q)`, and derive the pigeonhole survival condition; optional
endpoint-disjoint variant with the sharper `R(p,q)` bound.

### Strengths

- Well-decomposed task ladder; each task is one clean step.
- Excellent claim honesty: repeatedly distinguishes the capacity theorem from
  the abundance question (§1, §6, task 5 note).
- Task 3's two-gaps-per-removed-value argument is correct and well explained.

### Issues

1. **Not a paper (structural).** As an exercise it works, but it lacks
   everything a scholarly document carries: no author, date, references, no
   solution sketch, and no link from each task to the corresponding maintained
   property or candidate file in the repository. If it is intended to become a
   publishable exercise (e.g., for a formal-methods course or article
   appendix), it needs at least a solution outline.
2. **Conventions silently differ from the canonical experiment (moderate).**
   The exercise uses `[q, q²)` with `q` the *next* prime, which matches the
   canonical transition experiment, but never says so — and draft 4 (which it
   lists as prerequisite reading) uses `[h, h²)`. A reader coming from draft 4
   has to discover the convention change unaided. One sentence and a symbol
   table would fix it.
3. **Task 1 stated without proof hints of the standard technique (minor).**
   The counting formula is standard; pointing at the bijection
   `k ↦ k+1` between multiples in `[A,B)` and integers in
   `[[A/a], [B/a))` would make the exercise self-teaching.
4. **"Consecutive accepted values" is load-bearing but informal (minor).**
   Task 3 requires that `(v−2, v)` and `(v, v)` neighbors are *consecutive*
   accepted values for a destroyed gap to count; the definition in §2 says
   "consecutive accepted values before applying the p-filter" but the exercise
   never pins down what happens when `v−2` or `v+2` is itself removed by the
   same filter (both endpoints removed by one strike is one destroyed gap, not
   two). A careful solver will hit this edge; the text should address it
   (the `2·R(p,q)` bound is unaffected, but the bound's tightness argument
   changes).
5. **No status of the stronger variant (minor).** §5's endpoint-disjoint
   variant is exactly the isolation hypothesis discussed in draft 4 §6; say so
   and link, so the exercise connects to the research narrative.

### Improvements

1. Add front matter (status, date, prerequisites table) and a conventions
   paragraph reconciling with draft 4's notation.
2. Add an appendix with solution sketches (one paragraph per task).
3. Handle the both-endpoints-removed edge case explicitly in Task 3.
4. Cross-link the endpoint-disjoint variant to draft 4 §6 and to any
   maintained candidate file.

---

## 3. `draft-empirical-g-local-analysis.md`

**Summary.** Superseded record of the historical Scala `[p, p²)` 2-gap counter
(primes to 997): crossover at p=37, monotone surplus growth, no extinction
events post-crossover, plus a Spark cross-validation section.

### Strengths

- Exemplary supersession labeling: title, abstract, section headers, and
  conclusions all repeat that the convention is incompatible with the
  canonical experiment and nothing here is a proof.
- Property index with an explicit `[Empirical]` status key; a real
  limitations table (§5.4); pointers to the canonical successor data.
- The §4.6 CRT exact-count verification (214,708,725 2-gaps matching
  `∏(r−2)` exactly) is a genuinely valuable audit result.

### Issues

1. **Interpretive analysis outlives its own supersession (major).** §4 is
   full-height analysis — linear regression with `R² > 0.99`, extrapolations
   ("G/p would reach 10 at p ≈ 1270 and 100 at p ≈ 13900"), clustering
   inferences ("more densely clustered in the early positions"), and a
   mechanism explanation of the p=73 dip — all built on data the article's own
   header declares not current evidence. A reader who quotes §4.1 without the
   header gets a misleading asymptotic story. Either demote §4 to explicitly
   historical interpretation (repeat "superseded" in each subsection title) or
   strip the forward extrapolations, which have no audit value.
2. **No statistical rigor anywhere (major, for its empirical genre).** No
   confidence intervals, no regression details (n, method, residuals), no
   uncertainty on the ratio estimates, and monotonicity claims from a single
   deterministic run presented alongside `R²` language borrowed from
   statistics. For a deterministic computation this is survivable, but then
   the regression dressing should go: state the fit is descriptive only.
3. **The Mertens-comparison claim in §4.3 is quantitatively vague
   (moderate).** "exceeds this uniform estimate by a factor of approximately
   2-3 across the range" carries no computation, and the proposed explanation
   is asserted, not tested. Similarly §4.6's "comfortably above the 1 needed"
   and "same order of magnitude" are not analyses.
4. **Reproducibility gap (moderate).** The runner is "pending removal" and its
   command intentionally unpublished — so the tables are not reproducible by a
   reader *by design*. For an audit record, the article should then state the
   dataset's identifying information (row count is given; a checksum or the
   archived path in history would be better) so the numbers can be tied to
   the artifact being audited.
5. **Minor inconsistencies.** §2.4/§3.5 give 166 primes but the k=168 index
   for p=997 appears in the §3.2 table (997 *is* the 168th prime; the table's
   k-column is prime index while §2.4 counts primes from 3, i.e. 167th prime
   overall — worth one reconciling footnote to prevent misreading). The
   reference list is not in a consistent bibliographic style.

### Improvements

1. Decide the document's genre: audit record (keep tables, cut §4.1–§4.4
   extrapolations and mechanism stories) or historical analysis (keep, but
   re-label every subsection and remove the regression `R²` framing or
   justify it).
2. Add a data-provenance block (checksums / archived paths) since
   reproducibility is intentionally unavailable.
3. Reconcile the prime-index columns with one footnote.
4. Fold §4.6 into the canonical successor documentation if it is still live
   evidence, since it is the one section whose value survives the convention
   change.

---

## 4. `draft-sieve-gap-survival-math.md`

**Summary.** Superseded mathematical exploration: copy-or-merge gap dynamics,
stable absence of small gaps, full-period 2-gap survival (`h−2` descendants),
the global-vs-local (safe-window) boundary, local capacity and cluster
arguments, and a closing section describing the current signed-boundary
successor.

### Strengths

- The core structural results (§2–§4) are correct, clearly proved at the
  right level of detail, and genuinely illuminate why full-period CRT
  uniformity does not settle the safe-window question — the article's central
  lesson, stated cleanly in §5.
- §3's parity argument for permanent 2-absence is a nice, complete
  induction.
- Honest about being unverified and superseded; §11 is an accurate claims
  inventory.

### Issues

1. **§12 is under-anchored notation (major).** The "Current Successor
   Boundary" section compresses the successor article's machinery
   (`N_i, a_i, A_{u,v}, w_i, w_{-1}, T, b_i, W_-, E_b`, then `c_t, d_t, V_r,
   B_j`) into half a page with almost no definitions. The claimed results
   (telescoping identity, weighted Cauchy–Schwarz bound, the `|b_7| ≤ 18/7`
   interval bound, the `4V_r` energy bound) cannot be checked from this
   article, and a reader cannot even parse `W_-=\sum w_{i-1}` without the
   successor. As a historical draft it should *summarize* the successor
   qualitatively (one paragraph: what changed, what the new open problem is)
   and delegate the formulas to a link.
2. **No per-claim status markers (moderate).** §11 lists claims 1–6 but does
   not mark which are proved in this article, which are conditional (§6–§7
   depend on isolation/cluster existence hypotheses), and which are empirical
   observations. The conditional nature of §6 is stated in-line (good) but
   claim 5 in §11 reads as established.
3. **Reference [3] points at a superseded draft (minor).** The citation to
   `draft-empirical-g-local-analysis.md` should carry its superseded status
   so the reference chain stays honest.
4. **Front-matter/status mismatch with content (minor).** The header says
   "Superseded historical draft", yet §10 presents the stage-by-stage survival
   condition `|A_h| > h−1` as "a sound historical sufficient condition"
   followed by "Empirical work in this repository has observed this stronger
   inequality" — an appeal to the *other* superseded dataset. The observation
   sentence should cite the canonical successor data or be dropped.
5. **Cluster section §7 (minor).** The width-8 cluster claim is fine, but the
   argument that "the h-filter can strike at most one integer inside this
   width-8 interval" requires h > 8 (stated) — and more importantly the
   cluster must consist of *consecutive accepted values*, which is assumed
   implicitly by the example coordinates. State the consecutiveness
   requirement explicitly.

### Improvements

1. Rewrite §12 as a qualitative summary + link; move the formula dump out.
2. Add status markers (proved / conditional / empirical / open) to the §11
   inventory and convert §11 into a small table.
3. Fix the reference statuses and the §10 empirical sentence.
4. State the consecutiveness premise in §7.

---

## 5. `draft-relaxed-almost-prime-sieve-sequence.md`

**Summary.** Draft of an analytic-sieve article: the relaxed weight (first
endpoint square-safe prime, second endpoint sieved only below
`z = Q^{2α}`, `1/3 < α < 1/2`). Five results: positivity implies
prime-plus-P₂; exact divisor local factor with five local cases and interval
remainder; shifted-divisor discrepancy reducing to prime-progression
remainders; exact bilinear character decomposition; and a modulo-3 character
refutation of scalar-density Type-II orthogonality.

### Strengths

- **The best claim discipline in the set.** Every property section opens by
  stating its population and scope before proving; §9 ("Claim Boundary") and
  Appendix A (evidence/verification status table) are exactly what a referee
  wants to see; the refuted route (§7) is preserved with precise scope of what
  is and is not refuted.
- The mathematics checks out on inspection: the five-case local table `λ_p(m)`
  is correct in each case; the Möbius/Euler restriction to `Z_odd` (using that
  `mn+2` is odd) is handled correctly; the character-orthogonality identity
  and the modulo-3 counterexample (`mn ≡ 2 mod 3` forced on accepted pairs,
  so `χ₃(mn) = −1` exactly) are right.
- Honest, repeated, non-burdensome statements that nothing new here is
  Stainless-verified.

### Issues

1. **No external citations (major — see C1).** The article name-drops "Chen
   theory", "Type-I/Type-II", "lower-bound sieve", "nonprincipal character
   modes" and uses the standard weighted-sieve architecture, yet its reference
   list contains only six *internal* documents. The sieve parity phenomenon is
   the classical context for §7 and is never mentioned. This is the article
   most in need of a literature section and a "which parts are standard"
   paragraph.
2. **Dense, insider-only exposition (moderate).** No definitions of `P₂`,
   Type-I vs Type-II estimates, or the lower-bound-sieve framework are given;
   a reader outside the project cannot follow §§5–8. An analytic-number-theory
   referee could, but would then immediately ask for issue 1. A half-page of
   preliminaries defining the sieve vocabulary would serve both audiences.
3. **No theorem numbering / statement environments (moderate).** Results are
   referenced by section; combined with the long conditional sentence at the
   top of each section, the precise statement of e.g. the §4 result (with its
   exact error term `|E| ≤ R−1`) is hard to cite or restate.
4. **Unexamined constants (minor).** `ϑ_Z = ∏(1 − 1/(p−1))` is stated as "the
   complete-wheel relaxed density" without the one-line derivation (for fixed
   unit `m`, `n ↦ mn` is uniform on units mod p, so exactly one residue class
   is forbidden). The article proves harder things in full; this gap reads as
   an oversight rather than a shortcut.
5. **Abstract formatting (minor).** The `<div align="justify">` wrapper is a
   rendering artifact, inconsistent with the rest of the set, and adds
   nothing.
6. **§3's `X₀(α)` (minor).** The threshold below which `X^{3α} > X+1` is
   asserted to exist; give the explicit bound (`X ≥ 2^{1/(3α−1)}` suffices)
   since everything else in the article is explicit.

### Improvements

1. Add a real bibliography (Chen 1973; Halberstam–Richert; Iwaniec–Kowalski;
   Friedlander–Iwaniec) and a "standard vs new" positioning paragraph;
   explicitly connect §7 to the parity barrier.
2. Add a preliminaries subsection defining `P₂`, Type-I/II, lower-bound sieve.
3. Number the five main results as theorems/propositions with named premise
   lists.
4. Add the one-line `ϑ_Z` derivation and the explicit `X₀(α)`.
5. Drop the HTML justify wrapper.

---

## 6. `draft-adversariality-phase-transition-2-gap-companions.md`

**Summary.** The set's centerpiece: balanced companion processes preserving
the exact `r−2` descendant count while relocating the two deletions (random /
protective / adversarial / mixtures / exact-quota / biased-quota). Proves
allocation-independent global persistence, the cumulative hazard law
`P(Q) = e^{−D(Q)}`, the fixed-w survival class, and the two logarithmic
frontiers (square-window at `c < 1`, head recurrence at `c < 1/2`), plus a
finite allocation theorem, targeting normalization, and an empirical §8.1
comparing the real sieve to the companions.

### Strengths

- The scientific core is sound and, on inspection, correct: the companion
  definitions are clean; the hazard-law algebra, prime-sum asymptotics, and
  Borel–Cantelli bookkeeping (including the Kochen–Stone mixing formulation
  with its explicit definition in §2.1) are right; the exact-quota survival
  factor `(N−J)(N−J−1)/(N(N−1))` and its log expansion are correct; the
  allocation bounds in §5.1/A.6 are sharp and correctly proved; the modulo-3
  coupling discussion and the real-sieve `K_{a,r}` formula correctly
  delimit what transfers.
- Premise honesty is a recurring virtue: nearly every asymptotic conclusion
  repeats its availability/placement/mixing premises; §9 (Limitations) is
  thorough and even flags the expectation-vs-almost-sure gap.
- Empirical sections state data provenance, generating scripts, sample sizes,
  and floors for log-axis plotting; the full-cycle identity (`f_r = 2/r`
  exactly) is proved, not just plotted.
- References include DOIs; the deterministic discrepancy transfer criterion
  in §10 is a genuinely precise formulation of what a twin-prime proof would
  still need.

### Issues

1. **The empty-window bound is an unstated assumption doing load-bearing work
   (major).** Square-window almost-sure results repeatedly use
   `Pr(X_Q = 0) ≤ e^{−λ_Q}` ("the usual form", §4.1; "blind empty-window
   bound", §7.1; A.3, A.5). For a sum of independent indicators this is
   Chernoff; for the *dependent* indicators arising from exact quotas,
   whole-filter coins, block balance, or CRT-coupled placement it is neither
   trivial nor automatic — indeed §9 explicitly warns the dependencies differ.
   The article needs either (a) an explicit lemma deriving the bound under
   each stated dependence structure (negative association would suffice and
   holds for sampling-without-replacement quotas), or (b) the bound promoted
   to a named premise with the same status as mixing/availability. Right now
   it floats between the two.
2. **Duplicated results (moderate).** §7.2 re-derives the §3.4/§3.5 frontiers
   nearly verbatim under the name `κ_r` that the text itself identifies with
   `w_r` ("This is the same quantity called `w_r`"). A.3/A.4 then restate them
   a third time. One derivation with a specialization remark would cut
   ~2 pages and remove the `κ`/`w` symbol split.
3. **No status line / no draft marker (moderate — see C3).** The largest and
   most claim-heavy article in the set is the only one with no status
   declaration. A reader landing on it cannot tell, from the header, that
   every almost-sure statement is conditional on unproven stochastic
   premises. An evidence-status table like draft 5's Appendix A should be
   added, with one row per theorem and a premises column.
4. **The intro's heatmap excursion delays the model by ~5 pages
   (moderate).** The View A/View B alignment discussion (lines 74–128) is a
   careful and honest treatment of a visualization subtlety, but it appears
   before any companion model exists and reads as a rebuttal to an argument
   the reader hasn't seen. Move it to §8 (empirics) or an appendix; the
   introduction needs only the three-scales distinction (which is excellent).
5. **Statistical reporting without uncertainty (moderate).** §8.1: "mean
   ratio 0.967 across 188 heads", "largest observed relative factor 0.0523",
   "signed values between −0.0353 and 0.00908" — point estimates only. The
   data are deterministic, but the *inference* ("the real sieve is
   substantially less destructive than random on these windows") is a
   generalization from 187 transitions; report at least the spread/trend of
   the ratio in `p` (is 0.967 drifting toward or away from 1?) and say
   explicitly that no uncertainty quantification applies to a deterministic
   computation.
6. **Abstract length and final sentence (minor).** The abstract is a full
   paragraph of dense notation (`w_r`, CRT-rate cumulative sum, "summable
   finite-population error conditions derived below"). The closing claim —
   that proving the real sieve stays below the head frontier "would establish
   the twin-prime conjecture" — is technically guarded, but the abstract
   should also say that *none* of the stochastic premises is proven for the
   real sieve, since that is the fact most likely to be lost in citation.
7. **Figure governance (minor).** Nine figures, each with script and data
   links — good — but no version, seed, or parameter-table metadata, so a
   regenerated CSV silently changes published numbers (e.g. the "ratio of
   about 102" at R=251). A one-line figure caption convention citing the
   generating commit or parameter block would make the empirical record
   auditable.
8. **Minor mathematical blemishes.** §5.5: "The prime harmonic series
   diverges at `c=1`" — the *prime zeta-like* series `∑_{Q prime} 1/Q`
   diverges; the wording "prime harmonic series" usually means
   `∑ 1/p`, which is the same thing here, but say which. §4.6's percentage
   table (9.14% at r=101 etc.) invites pointwise misuse that the surrounding
   text then warns against — consider deleting the table or moving it after
   the cumulative-warning paragraph.

### Improvements (priority order)

1. Promote `Pr(X_Q=0) ≤ e^{−λ_Q}` to an explicit named premise or prove it
   per dependence structure; reconcile with §9's own warning.
2. Add a status/evidence table (theorem × premises × status) and a status
   header line.
3. Merge §7.2's `κ`-analysis into §3 as a specialization; delete the duplicate
   derivations in A.3/A.4 or keep the appendix as the single home.
4. Move the View A/View B material to the empirical section or an appendix.
5. Add spread/trend reporting to §8.1 and a deterministic-data disclaimer.
6. Add external citations for the random-sieve comparison class (C1).
7. Figure metadata convention; fix the §5.5 wording; relocate the §4.6
   percentage table.

---

## Priorities for the Set

1. **Bibliography and positioning (C1)** — affects drafts 3, 5, 6; largest
   scientific-credibility gap; the parity-barrier connection in draft 5 §7
   and the random-sieve connection in draft 6 are the two most important
   single additions.
2. **Premise promotion in draft 6** — the empty-window bound is the one place
   where a load-bearing step is currently neither proved nor declared.
3. **Status vocabulary and theorem numbering (C2, C3)** — cheap, mechanical,
   prevents the most likely misreadings of the whole set.
4. **Structural cleanups** — draft 1 §4/§5 merge; draft 4 §12 rewrite;
   draft 3 §4 demotion; draft 6 §7.2 merge and intro relocation.
5. **Statistical honesty pass on draft 3 §4 and draft 6 §8.1** — either
   quantify or explicitly disclaim.

---

## Response to the Review and Claim Disposition

**Response date:** 2026-08-15

The review was checked claim by claim against the current working-tree drafts,
the linked Scala theorem bodies, the extant empirical scripts and data, and the
project's article guidance. The dispositions below distinguish mathematical or
scientific defects from optional editorial improvements. `Accept` means the
diagnosis should guide a later article revision; `Accept with qualification`
means the underlying concern is useful but the review's wording or remedy is
too broad; `Reject` means the stated defect is not supported by the current
document. This response changes no reviewed article.

### Cross-cutting claims

| Claim | Disposition | Worth acting on? | Response |
|---|---|---:|---|
| C1 — external literature | Accept with qualification | Yes: high for draft 5, medium for drafts 3 and 6 | Draft 5 invokes Chen and standard sieve vocabulary while citing only internal sources; draft 3 invokes Mertens without a source; draft 6 would benefit from comparison with probabilistic sieve models. The review overstates the classification, however. Draft 5's weight is Chen-adjacent project-specific pre-sieving, not “precisely” the standard Chen weight, and its modulo-3 character obstruction is not identical to the classical sieve parity barrier. Draft 6 is not simply a Cramér model. Cramér (1936) and Gallagher (1976) are relevant context, but the relation must be stated precisely rather than asserted by analogy. |
| C2 — theorem numbering | Accept with qualification | Optional; most useful for drafts 5 and 6 | Formal theorem numbers would improve external citation, but this is scholarly usability rather than correctness. The drafts already have numbered sections, property indexes, named result sections, and, in draft 6, numbered proof records A.1--A.6. |
| C3 — front matter/status | Accept with qualification | Yes; cheap | Dates and a consistent compact status vocabulary would help. The review is stale in saying draft 6 never states that it is unverified: §1.1 explicitly says its asymptotic theorems are conditional and Stainless verification is pending. The remaining issue is that this status is not visible in the header. |
| C4 — notation drift | Reject as a set-wide defect; accept one local cleanup | Optional | `h`, `p`, `q`, and `Q` often denote genuinely different current-head, next-head, or future-head roles. Forcing one symbol across independent documents could erase meaning. A vocabulary map is optional. In draft 6, consolidating `κ_r` with `w_r` where they are explicitly equal is worthwhile; `α_r` and `θ_r` are not alternative normalized-damage symbols but different quantities. |
| C5 — math rendering | Accept with qualification | Yes if these drafts enter the publication pipeline | The repository standard is fenced `math` blocks plus inline `$...$`. Draft 3's display syntax and draft 2's `text` fences are inconsistent with that standard. For a deliberately plain-text exercise this is low priority; for publication it is a mechanical cleanup. |

The literature recommendation should cite primary sources only after matching
them to the exact comparison being made. Gallagher's 1976 paper studies
Poisson laws for prime counts in short intervals under a uniform prime-tuple
premise; that is useful context, not an identity with the balanced companion.
Likewise, classical parity-barrier literature concerns a sieve's inability to
distinguish parity of the number of prime factors, whereas draft 5 proves a
specific fixed-character correlation modulo 3.

### 1. `draft-sieve-foundation.md`

| Issue | Disposition | Worth acting on? | Response |
|---|---|---:|---|
| 1.1 — §§4/5 duplication | Accept with qualification | Yes | The two displayed propositions are identical, and the Scala source explicitly calls `assertFilterPreservesAllPrimes` a direct restatement that invokes `assertPrimeNotDivisibleByDistinctPrime`. There are still five verified functions, but only four substantively different results. Keep the source wrapper and present it in the article as a filtering corollary rather than a second theorem. |
| 1.2 — scholarly apparatus | Accept | Yes if publication-facing | The draft has a status line, contrary to any implication that it has no front matter at all, but it lacks author, date, references, and a property/status index. Internal references are sufficient for this bridge article. |
| 1.3 — §6 quantifier mismatch | Reject | No | The mathematical statement and Scala theorem match: one selected `q` must be prime and belong to an otherwise unrestricted list `L`. Neither requires every other list element to be prime. `originalPrimes` is only a parameter name, so there is no stronger hidden hypothesis to repair. |
| 1.4 — thin induction prose | Accept | Low priority | Adding the recursive-step identity would make the proof sketch more self-contained and better match the project's step-by-step derivation style. |
| 1.5 — missing forward map | Accept with qualification | Yes | A map should distinguish direct code dependencies from conceptual foundations. Repository-wide use search shows only `assertPrimeNotDivisibleByDistinctPrime` is directly consumed outside its defining property module; the other functions are explanatory foundations rather than direct dependencies of the full transition proof. |

### 2. `exercise-local-safe-window-capacity.md`

| Issue | Disposition | Worth acting on? | Response |
|---|---|---:|---|
| 2.1 — “not a paper” and no solutions | Accept with qualification | Depends on intended genre | The file explicitly declares itself a draft exercise, so lacking paper apparatus is not a scientific defect. A short solution outline and maintained-property links would improve it if it is intended for a course, appendix, or publication. |
| 2.2 — silent convention change | Reject | No required fix | The exercise explicitly defines `p` as the current head, `q` as the next prime, and `[q,q²)` as the next safe window. A cross-document comparison sentence may help, but the convention is not silent. |
| 2.3 — missing Task 1 hint | Accept with qualification | Low priority | A hint is pedagogically useful. It should use the correct multiplier range `ceil(A/a) <= k < ceil(B/a)`; the review's proposed floor-interval bijection is not stated precisely enough. |
| 2.4 — “consecutive” edge case | Reject | No; at most one clarifying sentence | Consecutiveness is already part of the local 2-gap definition. If two removed values hit the same gap, summing the per-value bound counts that gap twice, which only preserves the safe upper bound `destroyed <= 2R`. No tightness claim depends on avoiding the double count. The review also mistypes the second possible pair as `(v,v)` rather than `(v,v+2)`. |
| 2.5 — stronger-variant status/link | Accept | Yes, low priority | Linking endpoint-disjointness to draft 4's isolation hypothesis and the maintained candidate record would improve the research narrative. |

### 3. `draft-empirical-g-local-analysis.md`

The review correctly sensed that this draft is not publication-ready, but it
understated and partly misdiagnosed the problems. The extant
[`results.csv`](../../data/empirical/results.csv),
[`EmpiricalRunner.scala`](../../src/main/scala/v1/chapter7/empirical/EmpiricalRunner.scala),
and [`SegmentedSieve.scala`](../../src/main/scala/v1/chapter7/empirical/SegmentedSieve.scala)
make four stronger corrections possible.

| Issue | Disposition | Worth acting on? | Response |
|---|---|---:|---|
| 3.1 — superseded interpretation remains prominent | Accept | Yes | The extrapolations and mechanism stories should be removed for an audit record or labeled locally as superseded descriptive interpretation. Header caveats alone are too easy to lose when a subsection is quoted. |
| 3.2 — no statistical rigor | Accept with qualification | Yes | The regression needs its population, method, reproduced coefficients, and residual diagnostics, or should be removed. Confidence intervals are not automatically appropriate because the rows are deterministic computed observations rather than a random sample. The correct remedy is to label any fit descriptive and avoid asymptotic inference from it. |
| 3.3 — vague Mertens comparison | Accept, but replace the diagnosis | Urgent | The problem is not merely missing arithmetic. Section 4.3 uses `G₂/φ(M) = ∏(r−2)/(r−1)` as though it were density per integer. The coordinate density is `G₂/M = (1/2)∏(1−2/r)`. At head 31 the former is about `0.2101`, while the latter is about `0.03319`; only the latter predicts roughly 31 gaps in a window of length 930. The claimed 2--3× excess and early clustering inference is therefore unsupported and conflicts with §4.6, which uses `G₂/M` correctly. |
| 3.4 — reproducibility gap | Accept with qualification | Yes | Reproduction is not currently unavailable “by design”: the runner and exact 166-row CSV still exist in the working tree. The draft should cite that artifact and a checksum while retained, or an archival commit if it is later removed. |
| 3.5 — 166/168 indexing footnote | Reject the proposed footnote; replace with a factual correction | Urgent | The CSV has 167 lines: one header plus 166 observations. Its terminal row is `k=167, p=991, p_next=997, G_local=8016, delta=7025`. The article repeatedly relabels this as a measurement at `p=997` and gives it prime index 168. The counts after crossover are also inconsistent: the data contain 156 rows including `p=37` (155 after it) and 146 rows after `p=73`, not 154 and 153. This cannot be reconciled by a notation footnote. |
| 3.A — interval endpoint convention missed by the review | New accepted correction | Urgent | The implementation allocates `hi-lo+1` entries and iterates through `m <= hi`, with `hi=p*p`; it measures the closed interval `[p,p²]`, not `[p,p²)`. The distinction affects the data because `p²` is not removed by the smaller installed primes. The historical draft's title, method, and comparisons must use the implemented convention. |
| 3.B — printed regression missed by the review | New accepted correction | Urgent | The displayed `0.0071p+0.97` is not reproducible from the CSV. Ordinary least squares over all 166 rows gives slope `0.0072095384`, intercept `1.3081670`, and `R²=0.9885071`; restricting to `p>=37` gives slope `0.0070056112`, intercept `1.4408247`, and `R²=0.9918583`. Neither produces the printed fit or its extrapolations. Remove the regression or identify and archive the actual input/transformation. |

The exact complete-period count in §4.6 remains valuable, but its independent
provenance should be cited before it is promoted elsewhere. The immediate task
is to make this historical audit factually self-consistent, not to expand its
statistical presentation.

### 4. `draft-sieve-gap-survival-math.md`

| Issue | Disposition | Worth acting on? | Response |
|---|---|---:|---|
| 4.1 — dense successor notation | Accept with qualification | Yes | The symbols are defined, so the section is parseable, but several successor results and premises are compressed without derivation. A qualitative summary plus an exact successor link better serves a superseded historical draft. |
| 4.2 — no per-claim status | Accept with qualification | Optional | Section 11 already calls the capacity and cluster rules conditional, so it does not present claim 5 as unconditional. A status table would improve scanning but is not a correction of a false claim. |
| 4.3 — reference [3] omits superseded status | Accept | Yes, low priority | The linked title should visibly say it is superseded so that status survives citation chains. |
| 4.4 — status/empirical sentence mismatch | Accept | Yes | The sentence appealing to tested ranges relies on the obsolete experiment and should be dropped or explicitly labeled historical. The canonical `[q,q²)` data do not directly validate the historical `A_h` definition. |
| 4.5 — cluster consecutiveness | Reject | No | Section 1 already defines a 2-gap as a pair of consecutive emitted values, so the two examples in §7 inherit that definition. The four endpoints need not form one consecutive four-value run; width and distinct endpoints are enough for the one-strike argument. |

### 5. `draft-relaxed-almost-prime-sieve-sequence.md`

| Issue | Disposition | Worth acting on? | Response |
|---|---|---:|---|
| 5.1 — no external citations | Accept with qualification | Yes, high priority | Add primary Chen and modern sieve references and distinguish standard machinery from the project-specific moving interval and nested wheels. Do not state that the modulo-3 obstruction “is” the parity barrier; present parity as broader context and this theorem as a specific local-character obstruction. |
| 5.2 — insider-only exposition | Accept | Yes | Define `P₂`, Type I, Type II, and the role of a lower-bound sieve before using them. |
| 5.3 — theorem numbering | Accept | Yes, medium priority | The five main results would benefit from stable names/numbers and explicit premise lists, even though the current section-level scopes are already unusually careful. |
| 5.4 — unexplained `ϑ_Z` | Accept with qualification | Yes, low priority | The later Euler expansion supplies part of the derivation, so the constant is not wholly unexamined. Add the one-line local explanation: among the `p−1` units modulo odd `p`, exactly one class makes `x+2` divisible by `p`. |
| 5.5 — HTML justify wrapper | Accept | Yes, low priority | This is a harmless but unnecessary rendering artifact. |
| 5.6 — implicit `X₀(α)` | Accept | Yes, low priority | The proposed explicit sufficient bound is correct: `X >= 2^(1/(3α−1))` gives `X^(3α) >= 2X > X+1` for `X>1`. |

### 6. `draft-adversariality-phase-transition-2-gap-companions.md`

These dispositions use the current working-tree draft, including its present
scope and evidence language.

| Issue | Disposition | Worth acting on? | Response |
|---|---|---:|---|
| 6.1 — empty-window bound is unstated | Reject as a current major defect; accept a small clarification | Small clarification only | The current text calls blind placement a premise in §3.4, conditions the §4.1 inequality on uniform placement, explicitly assumes the same premise for exact quotas in §7.1, and repeats in §9 that expectation alone is insufficient. The protective-binomial model separately derives its exponential bound. Define “blind empty-window premise” once near the notation, but do not claim the dependency is hidden or automatically inherited by the real sieve. The review's suggestion that negative association automatically resolves every quota/overlap model is itself unproved here. |
| 6.2 — duplicated frontiers | Accept with qualification | Optional | The general `w_r` derivation and §7.2's `κ_r` derivation substantially overlap. Consolidate `κ_r=w_r` into a specialization. Appendix A.3/A.4 is intentionally a proof-record surface, so its repetition need not be deleted. |
| 6.3 — no status marker/table | Accept with qualification | Header status/date: yes; table: optional | The header should expose the draft/conditional/pending status. The review is stale in saying the article never states it: §1.1 already does. A theorem-by-theorem premise table would help but is not required to prevent the claimed complete absence of status. |
| 6.4 — heatmaps delay the model | Accept with qualification | Optional | The two views occur before the model and can be moved for a tighter opening, but they motivate the three spatial scales and explicitly disclaim evidentiary force. “About five pages” is not established by source-line count and should be treated as layout-dependent. |
| 6.5 — point estimates without uncertainty | Reject as a scientific defect; accept descriptive enrichment | Optional | These are exhaustive deterministic summaries of the available rows, not estimates from a defined random sample. Confidence intervals would be meaningless without a sampling model. The article already limits its statements to the observed windows and has a finite-evidence limitation. A range, quantiles, or trend in `p` could improve description without pretending to quantify sampling uncertainty. |
| 6.6 — abstract density/transfer caveat | Accept with qualification | Yes | The abstract is dense and should attach the spatial premise directly to square-window survival. Add one short sentence that the real-sieve transfer premises remain unproved. Its final twin-prime sentence is already guarded by persistent availability and an unproved deterministic discrepancy bound. |
| 6.7 — figure governance | Reject as stated; accept minor metadata normalization | Low priority | Every figure links to scripts and data where applicable, the generators inspected are deterministic, and a random seed is therefore irrelevant. Most generated SVGs already embed commit metadata. Normalize that metadata for the remaining figures if desired; version control also prevents regenerated data from changing literally silently. |
| 6.8 — “prime harmonic series” and percentage table | Reject | No required change | “Prime harmonic series” is standard and immediately follows the displayed `Σ_{Q prime}1/Q^c`, so it is unambiguous. The percentage table is followed immediately by the cumulative-warning paragraph that prevents the pointwise interpretation the review fears. Either may be shortened for taste, but neither is a mathematical blemish. |

### Revised priorities

1. Correct draft 3's factual record before any stylistic work: terminal head,
   row counts, closed interval convention, density denominator, clustering
   inference, and regression provenance.
2. Add external positioning to draft 5, carefully distinguishing its
   project-specific weight and modulo-3 obstruction from Chen's exact setup and
   the classical parity barrier.
3. Add a visible status/date line and a single definition of the blind
   empty-window premise to draft 6; clarify the abstract's spatial and
   real-transfer premises.
4. Apply low-risk scholarly usability improvements where the intended genre
   warrants them: theorem numbering for drafts 5/6, front-matter consistency,
   math-fence normalization, and draft 1's theorem/corollary presentation.
5. Treat the remaining structural suggestions as optional editing: draft 4's
   successor summary, draft 6's heatmap placement and `κ/w` consolidation, and
   descriptive trend summaries for deterministic empirical data.

The original priority placing bibliography first is therefore revised. The
draft-3 factual errors affect the truth of the historical record and must come
before citation, numbering, or layout work. No recommendation in this response
authorizes changing the reviewed articles until a separate revision pass is
requested.

---

## Reviewer Rejoinder to the Author Response

**Date:** 2026-08-15
**Action:** Evaluation of the dispositions above. Every factual counter-claim
in the response was independently re-verified against the working tree before
this rejoinder was written. This rejoinder changes no reviewed article either.

### A. Verification of the response's factual claims

| Author claim | Independent check | Result |
|---|---|---|
| CSV has 167 lines; terminal row `k=167, p=991, p_next=997, G=8016, δ=7025` (3.5) | `wc -l` + `tail` on `data/empirical/results.csv` | **Confirmed.** The article's `p=997, k=168` row carries exactly the p=991 row's values; the mislabel plausibly arises from transcribing `p_next=997` as `p` |
| 156 rows at `p≥37` (155 after), 146 after `p=73` (3.5) | `awk` count over the CSV | **Confirmed.** The article's "154 subsequent" and "remaining 153" are both wrong. The p=71→73 dip (δ 51→50) is real in the data |
| Closed interval `[p, p²]`, not `[p, p²)` (3.A) | `EmpiricalRunner` passes `hi = p * p`; `SegmentedSieve` allocates `hi−lo+1` and strikes `while (m <= hi)` | **Confirmed** |
| Printed regression irreproducible (3.B) | OLS recomputed from the CSV | **Confirmed exactly:** all 166 rows give slope 0.0072095, intercept 1.30817, R² 0.98851; the 156 rows with `p≥37` give slope 0.0070056, intercept 1.44082, R² 0.99186. The printed intercept 0.97 matches neither fit, and `R² > 0.99` holds only for the `p≥37` subset, which the article does not state |
| §4.3 density-denominator error (3.3) | Arithmetic recomputed | **Confirmed.** `G₂/φ(W₂₉) = 214,708,725 / 1,021,870,080 ≈ 0.2101` (per-coprime), `G₂/M ≈ 0.03319` (per-integer), and `930 × 0.03319 ≈ 31` matches the observed ~30. The article divides by φ(W) where the window length demands division by W; the "2–3× excess" and the early-clustering inference are artifacts of that error. This is a genuine factual defect the original review detected only as "vague" — the author's diagnosis is sharper and correct |
| Draft 6 §1.1 states the conditional/pending status (C3, 6.3) | Read §1.1 | **Confirmed.** The original review's wording "never says 'draft' / 'not Stainless-verified'" was inaccurate and is retracted; the surviving ask is header visibility, which the author accepts |
| Figures embed commit metadata (6.7) | `grep -il commit charts/*.svg` | **Confirmed** for several charts |

The response's evidentiary standard is high: every checked claim held. The two
new corrections (3.A, 3.B) and the sharpened 3.3 are accepted in full and
**endorse the response's reordering of priorities**: making the draft-3 record
factually self-consistent precedes all citation, numbering, and layout work.

One addition to 3.5: the sentence "All 166 primes from p=3 to p=997" contains a
second, independent off-by-one — the primes in [3, 997] number 167; the 166
data rows actually span [3, 991]. The correction is not only the terminal-row
label but the stated range itself.

### B. Concessions and retractions

The following dispositions are accepted without further argument:

- **C3 / 6.3 (partial retraction).** As above — the "never states" wording was
  stale; only the header-visibility request remains, by agreement.
- **1.3 (withdrawn).** The article's formal statement quantifies exactly one
  prime `q` and an unrestricted list; it is accurate. The residual is a
  cosmetic Scala parameter-name nit, not an issue.
- **2.2 (downgraded).** The exercise defines `p`, `q`, and `[q, q²)` in its own
  §1, so the convention is not silent; the cross-document sentence the author
  permits is the entire surviving content.
- **2.3 (precision accepted).** The correct hint is the k-range
  `ceil(A/a) ≤ k < ceil(B/a)` (equivalent to the exercise's floor form by
  `ceil(B/a) − 1 = floor((B−1)/a)`); the review's bracket notation was
  imprecise.
- **2.4 (substance conceded).** Double-counting a gap struck at both endpoints
  only inflates the per-value upper bound, so `≤ 2R(p,q)` is safe and no
  tightness claim in the exercise depends on the distinction. The review's own
  text contains the `(v, v)` typo the author identifies — it should read
  `(v, v+2)`; the error is the reviewer's. The one clarifying sentence the
  author allows is still worth adding for solvers.
- **3.4 (framing conceded).** The runner and 166-row CSV exist in the working
  tree, so "unavailable by design" overstated the draft's "pending removal"
  language. The remedy is unchanged: cite the artifact and a checksum while it
  exists.
- **6.1 (over-framing conceded).** The bound `Pr(X_Q=0) ≤ e^{−λ_Q}` *is*
  introduced as a premise in §3.4, conditioned in §4.1, and assumed again in
  §7.1; the review's summary wording "neither proved nor declared" was wrong
  for the current text and is retracted. Two refinements stand, both within
  what the author accepts: (i) the premise should be defined once at first
  use, since "blind-placement empty-window premise" is currently
  reverse-engineerable only from its usage sites; (ii) for the record, the
  review's negative-association remark was scoped to "sampling-without-
  replacement quotas", where it is a provable standard property — it was not
  offered as resolving whole-filter coins, block balance, or CRT-coupled
  placement, and no such claim is maintained.
- **6.5 (reclassified as agreement).** The review's ask was exactly spread /
  trend reporting plus an explicit statement that no sampling model exists;
  the author accepts both. Nothing further is requested.
- **6.7, 6.8, C4 (accepted as stated).** Deterministic generators make seed
  metadata moot and commit metadata exists; "prime harmonic series" is
  unambiguous in context and the percentage table is already followed by the
  cumulative warning; the set-wide notation claim was too blunt, and the local
  `κ`/`w` consolidation the author accepts was its substantive core. (Draft 4's
  `h` and drafts 5/6's `Q` do name the same *role* — current head — so a
  vocabulary *map* remains cheap and useful, but it is stylistic.)

### C. Points maintained, with sharpened wording

1. **C1, draft 5 — the structural claim stands; the classification wording is
   tightened.** The response answers a claim the review did not make: the
   review did not say `a_Q` is "the standard Chen *weight*" (that is the
   weighted-sieve upper weighting); it said the sifting *sequence*
   `1_{(n,W)=1} · 1_{(n+2,Z)=1}` with sifting level `z = X^α` is precisely the
   standard two-dimensional lower-bound-sieve setup for the pair problem, and
   that remains true — nested wheels and a moving interval change the
   *population*, not the *structure*. On the parity barrier the author's
   precision demand is accepted: the modulo-3 theorem is a specific
   fixed-modulus local-character obstruction, and the article should present
   the parity phenomenon as broader context, not claim identity. The same
   tightening applies to draft 6: Cramér/Gallagher are *comparison class*, not
   identity. Net: the original recommendation (real bibliography +
   positioning paragraph, stating which parts are standard) is maintained
   unchanged; only the review's analogical phrasing is corrected.
2. **Priorities.** The response's reordering (draft-3 factual corrections
   first) is endorsed and supersedes the review's original list. The review's
   item 1 (bibliography) becomes item 2; items 2–5 shift accordingly.

### D. Net assessment of the response

The response is of unusually high quality: it concedes what is wrong, rejects
with evidence rather than assertion, and — most importantly — surfaces three
factual defects in draft 3 (terminal-head mislabel with count errors, closed-
interval convention, irreproducible regression) and one density-denominator
error that the original review missed or under-diagnosed. All four were
verified independently and are confirmed. Of the review's original items:

- **Resolved by agreement:** 1.1, 1.2, 1.4, 1.5, 2.1, 2.5, 3.1, 3.2, 4.1–4.4,
  5.2–5.6, 6.2, 6.4, 6.6, C2, C5, and the surviving parts of C3/6.3, C4, 6.1,
  6.5, 6.7.
- **Retracted by the reviewer:** the "never states" wording (C3/6.3), the
  "neither proved nor declared" summary of 6.1, issue 1.3, the "silent
  convention" framing of 2.2, and the "by design" framing of 3.4.
- **Withdrawn as taste:** 6.8.
- **Maintained:** C1's bibliography-and-positioning requirement for drafts 5
  and 6 (with corrected analogical wording), and the one-place definition of
  the blind-placement premise in draft 6 — both already accepted by the author
  in some form, so no open disagreement remains.

No open scientific disagreement is left between review and response. The next
action on the articles themselves should follow the response's revised
priority list, starting with the draft-3 factual corrections as verified in
section A.

### F. Round-2 Application Record (2026-08-15)

The agreed fixes were applied in a separate pass, with every change logged
for team audit in
[`tickets/active/draft-articles-round2-fixes-2026-08-15.md`](../../tickets/active/draft-articles-round2-fixes-2026-08-15.md).
Summary:

- **Draft 3:** all factual corrections applied from fresh CSV recomputation
  (interval, terminal row, range, counts, density denominator, regression,
  monotonicity) — plus one additional defect found during the pass: five rows
  of the §3.2 growth table did not match the retained data.
- **Draft 5:** §1.2 positioning paragraph, §2 sieve vocabulary (P₂, Type-I/II,
  lower-bound sieve), Theorems 1–5 labels, external references [7]–[10].
- **Draft 6:** header status line, one-place blind-placement premise
  definition, abstract real-sieve caveat; §8.1 statistics independently
  verified against the CSVs — all quoted numbers check out, no change needed.
- **Drafts 1/2/4:** front matter, §5-as-corollary presentation, solution
  sketches appendix, §12 qualitative rewrite, reference status labels,
  historical labeling of the §10 empirical appeal.
- Deferred improvement suggestions were NOT applied; they are queued for team
  review in
  [`tickets/future/draft-articles-deferred-improvements-2026-08-15.md`](../../tickets/future/draft-articles-deferred-improvements-2026-08-15.md).

### E. Addendum (post-rejoinder verification pass): one further draft-3 error and a systemic concern

Prompted by the response's discovery that draft 3's summary counts are wrong,
the remaining prose statistics about the same CSV were re-derived. One more
claim fails:

**3.C — new correction. §3.2's G/p monotonicity claim is false.** The article
states the ratio `G_local/p` "increases monotonically (with one small
fluctuation, see Section 3.3)". Direct computation over the 156 rows with
`p ≥ 37` finds **five** non-increasing steps, not one:

| Transition | G/p before | G/p after |
|---|---:|---:|
| 71 → 73 | 1.7183 | 1.6849 |
| 107 → 109 | 2.0467 | 2.0459 |
| 191 → 193 | 2.8377 | 2.8342 |
| 269 → 271 | 3.4238 | 3.4207 |
| 461 → 463 | 4.8807 | 4.8790 |

Two notes. First, the *surplus* `δ` monotonicity claim (§3.3, "strictly
increases at all but one step") is correct as stated — the single δ dip at
71→73 was re-confirmed. The error is confined to the G/p sentence in §3.2 and
to §4.4's closing claim that "This pattern does not recur for any other
adjacent pair" (true for δ, false for G/p). Second, all five G/p dips occur at
twin-prime transitions, which is mechanistically consistent with §4.4's own
explanation (nearly unchanged window, larger denominator) — the data support
that explanation *better* than the article's uniqueness claim, so the fix is
to generalize §4.4 rather than delete it.

**Systemic concern for round 2.** Draft 3's narrative summaries of its own
data have now failed at six independent points: terminal-row label, stated
range (166 vs 167 primes), two post-crossover counts, the regression, and G/p
monotonicity. This pattern indicates the §3–§4 prose was not derived from the
retained CSV and must be *re-derived in full*, not spot-corrected. By the same
logic, the round-1 review verified mathematics but not data — draft 6's §8.1
summary statistics (mean ratio 0.967 over 188 heads; max `w_real = 0.0523`
from p ≥ 1000; the ~102 survival ratio at R = 251; the four fixed-cohort
`c_eff` values) have **not** been independently checked against
`data/candidates/*.csv` and `data/sieve-sequence/*.csv`. A second round should
include a data-verification checklist for those numbers before any of them
survive into a published revision.
