## Goal

Make `articles/chapter6/gap-dynamics-v2.md` self-contained: a reader can follow the complete argument — from complete-period counting through the filter-7 saving and copy-block bridge to the live frontier — without reading any external property or candidate file. Required proofs that aren't in the main body go into the article's own appendices. This is a markdown-only edit (no `.scala`), so no verify cycle applies.

Two findings from exploration shape the approach:
- **#23 and #20 have no canonical property notes** — they exist only as candidate files (`candidates/accepted-anchor-strike-density.md`, 851 lines; `candidates/conditioned-residue-collision-energy.md`, 340 lines). Writing full article sections for them adapts that candidate material into article form. This makes v2 the first place these get formal-style treatment.
- **The article never actually quotes the exhaustion proofs** (`11664`, `1080`, `rho_*` are absent); it only asserts their *conclusion* in §8. So the appendix obligation is narrower than it first appeared: append the exhaustion proofs that the new §5.3 narration will *summarize*, so the reader can drill down without leaving the article.

## New main-body sections (insert in order)

### §5.3 — Why The Capacity Envelope Is Exhausted (NEW, ~80–110 lines)
**Insert at line 1163** (the seam between §5.2/#66 and §6/#82).

Narrated summary of properties #67–#81, following the arc of `learnings-capacity-argument.md` §22.2 but expanded to actually walk the reader through each sub-route. Structure:
1. **Framing** — after #66, the survival question reduces to bounding `E_b`. The natural first attempt is a *capacity envelope*: at each layer, maximize `b_i²` over all residue histograms compatible with the class capacity (#70 gives `E_b ≤ U_cap`).
2. **Why capacity alone is too weak** — #74 proves the per-layer floor `X_i ≥ min(N_i,2B_i,r_iB_i−N_i)²/4` but also that it vanishes at `N_i=0` and `N_i=r_iB_i`; so `r,B` alone give no positive floor.
3. **Native-period Bessel** (#72) intersects prefix Bessel with capacity sharply by a greedy LP, giving `E_b ≤ U_hyb ≤ U_cap`. The gain at cut `k` is governed by overflow `e_k` (#73).
4. **Fixed cuts fail** — #77 (fixed cut after filter 7 fails for `m≥37`) and #78 (every fixed cut fails once `m > P_k(r_k−2)²(1+6/D)²`). State the constants.
5. **Moving cuts lose complete blocks** — #79 + PNT: any threshold-clearing cut with a complete block forces `m = O(log²H)`, but actual chains have `m ~ Q/log Q`, so for large Q no such cut exists. #80: the resulting single incomplete block gives `e_k = 0`.
6. **Stability-gap repair fails** — #81: `Γ_cap ≤ (25P_m/18)(2/5+3N_0/(5S))²` is eventually negligible vs. the `P_mD²/1080` floor.
7. **Verdict** — the capacity-plus-native-Bessel envelope is exhausted; the missing ingredient is *signed* residue information, which sets up §6/#82.

This section *summarizes* rather than re-proves. The actual proofs it leans on go to Appendix C (below).

### §6.5 — The General Coefficient And The Live Frontier: Candidates #23 and #20 (NEW, ~180–240 lines)
**Insert at line 1304** (the seam between §6/#82 and §7/#83).

Two full property-style sections adapted from the candidate notes, so that §7/#83's bridge to "residue energy" and §8/§10's conclusion naming "candidate #23" land for a reader who hasn't read external files.

- **§6.5.1 Candidate #23 — Accepted-boundary discrepancy.** Define `b_i = δ_{0,i} + δ_{−2,i}` (the sum of the two harmful-residue deviations). Adapt the candidate's core identities: the boundary decomposition, the CRT lift-index transform (#49/#50) that cancels the inherited old boundary, and the reduction to a weighted mean-square of Möbius transforms. State the open estimate (signed mean-square cancellation) and that #82's filter-7 calculation is the one-layer instance of this coefficient. ~90–120 lines.
- **§6.5.2 Candidate #20 — Residue-collision energy.** Define `V_r = Σ_t d_t²` and the same-residue autocorrelation expansion `C_r = N_r + 2Σ_h A_r(6rh)`. State the reduction of the two harmful classes to the histogram second moment and the target `C_r ≤ N_r + N_r²/r`. Note that this is the *input* #83's bridge consumes. ~80–110 lines.

Each carries a Population/Scope/Quantifier/Status block matching the article's convention, and a "Stainless And Source Evidence" pointer noting the candidate note as canonical source (the *article* link, not the external file, is now where the reader reads the result).

### §8.5 — The Fixed-Seed Scale Conflict (RESTORED from v1, updated, ~50–60 lines)
**Insert between current §8 and §9** (line ~1503).

Adapt v1 §11's content (lines 621–669): the primorial `M_p` vs `Q²` scale conflict via PNT, concluding that a fixed seed residue has at most one representative in the safe window. Update notation to v2's (`Q` future head, `W_Q` window) and connect it to the exhaustion argument: this is *why* complete-period counting can't place a survivor locally. ~50–60 lines.

### §9.5 — Recent Prime-Producing Sieve Research (RESTORED from v1, updated, ~55–70 lines)
**Insert between current §9 and §10** (line ~1513).

Adapt v1 §13's content (lines 802–855): Ford–Maynard 2024 framework, why Type II is necessary (not just Type I), Green–Sawhney as a methodological contrast. Update to reference the project's deep-dive (`properties/sieve-sequence/research/recent-prime-producing-sieves-deep-dive.md`) and connect to #85's χ₃ obstruction from the relaxed draft. This gives the "why is this hard" literature context the article currently lacks. ~55–70 lines.

## New appendix

### Appendix C — Proofs For The Exhaustion Chain (NEW)
**Insert after Appendix B** (line ~1736).

Full self-contained proofs of the exhaustion steps that §5.3 summarizes, so the reader never leaves the article. Move/adapt from the canonical notes:
- C.1 the Harmful-Capacity Excess Envelope property — sharp harmful-capacity excess envelope (from `sharp-harmful-capacity-excess-envelope.md`, 387 lines → condensed to ~80)
- C.2 the Envelope Width Floor property — width floor needs population slack (from `capacity-envelope-width-floor-needs-population-slack.md`, 320 lines → ~60)
- C.3 the Filter-Seven Cut Failure property — fixed-7 cut cannot clear (from `fixed-seven-cut-cannot-clear-original-threshold.md`, 272 lines → ~70, including the `m≥37` integer arithmetic)
- C.4 the Fixed Native Cut Failure property — every fixed cut fails (from `every-fixed-native-cut-fails-original-threshold.md`, 348 lines → ~75)
- C.5 the Moving-Cut Block Loss property — moving cut loses blocks (from `moving-cut-loses-complete-native-blocks.md`, 283 lines → ~70, PNT clearly marked external)
- C.6 the Incomplete-Block Bessel Bound property — incomplete-block Bessel excludes no capacity (from `incomplete-block-bessel-excludes-no-capacity.md`, 384 lines → ~70)

Each appendix entry is a *condensed* self-contained proof (the key derivation + boxed result + boundary), not a copy of the full note. The canonical notes remain the authoritative source; the appendix is what the article needs to be readable.

(#76, #81 are narrated in §5.3 but light enough not to need a full appendix proof — their constants are stated inline. If during writing they prove load-bearing, add C.7/C.8.)

## Other updates

- **Abstract** (~line 12): add one sentence noting the article now covers the exhaustion chain and the frontier candidates #23/#20, so the framing matches the expanded scope.
- **§1 Introduction dependency list** (~line 49): the numbered list currently has 12 items; add the new sections (§5.3 exhaustion, §6.5 frontier, §8.5 scale conflict, §9.5 sieve research).
- **Appendix A evidence table** (~line 1617): add rows for #20, #23, #70, #74, #77, #78, #79, #80.
- **Appendix B coverage table** (~line 1642): update the "Article treatment" column for the properties that now have full sections or appendix proofs (rows #20, #23, #70, #74, #77–#80 change from "canonical note only" to their new treatment).

## Approach / constraints

- **Markdown only.** No `.scala` touched → green-to-green verification exception applies.
- **No math invention.** Every proof adapts existing verified material (canonical notes for the exhaustion chain; candidate notes for #23/#20; v1 for restored scaffolding). Constants verified in earlier review passes.
- **One section per edit.** Given the `small-changes` discipline, I'll add sections one at a time (§5.3, then §6.5, then §8.5, then §9.5, then Appendix C, then the metadata updates), checking structure/links after each rather than batching.
- **External-theorem honesty preserved.** Wherever PNT/Bertrand/Mertens are used (§5.3 step 5, Appendix C.5, C.6), keep the "external dependency, not Stainless" framing the canonical notes use.
- **Don't touch the canonical property notes or candidate notes.** The article adapts them; it doesn't modify them.

## Order of work
1. §5.3 (exhaustion narration) — the highest-value gap.
2. Appendix C (the proofs §5.3 leans on).
3. §6.5 (#23 and #20 full sections).
4. §8.5 (fixed-seed scale conflict, restored).
5. §9.5 (recent sieve research, restored).
6. Metadata: abstract, §1 dependency list, Appendix A, Appendix B.

I'll pause for your review after step 1 and step 3 (the two largest pieces), so you can course-correct before I commit to the rest.