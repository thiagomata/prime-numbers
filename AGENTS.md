# Prime Numbers — Stainless Verification Project

<context>
SieveSequence: primes: List[BigInt], integral: CycleIntegral. head = primes.head.
Pipeline: nextResidues → nextExpanded → nextFiltered → nextSorted → 
           nextGaps → nextHeadResidueIndex → nextRotatedGaps
Each step calls ONE SieveUtils helper + ONE pre-verified function.
next() uses @extern (MemCycle bottleneck). Run tests first, verify second.

Lessons learned across all tickets are consolidated in `LEARNINGS.md`.
Check it when starting new work — it contains verified techniques,
pitfall avoidance, and timeout resolution strategies.
</context>

<commands>
  <verify>just verify</verify>
  <verify-focus>just verify functionName</verify-focus>
  <verify-log>grep "total:" verify.log</verify-log>
  <fast-compile>sbt 'set stainlessEnabled := false' compile</fast-compile>
  <tests>just test</tests>
</commands>

`just verify` writes its output to `verify.log` in the project root (and `verify-error.log` for errors).
`just verify functionName` compiles the full source tree but asks Stainless to verify only that function via `--functions=functionName`; use it for fast proof iteration only, not as a replacement for final full validation.
To check the latest result WITHOUT re-running, use `<verify-log />` to read the log.
Do NOT run `just verify` twice in a row — check `verify.log` first.
Only re-run `just verify` after making a code change.

<rules>
  <rule id="green-to-green" priority="critical">
    Run <verify /> before ANY code change. Run <verify /> after ANY code change.
    Run <verify /> after ANY change to non-markdown files.
    Stainless timeout IS failure. NEVER proceed from red state.
    Exception: Changes limited to markdown files (*.md) do NOT require verification.
    If a change modifies both code AND markdown files, verification IS required.
  </rule>
  <rule id="small-changes" priority="critical">
    ONE assertion/require/lemma per change. Verify between each.
    Do NOT add 3 assertions at once. If `a && b && c`, split into 3 changes.
  </rule>
  <rule id="stop-and-ask" priority="critical">
    After 3 failed attempts → STOP. Do NOT try variations.
    Output the error and ASK FOR HELP.
  </rule>
  <rule id="never-destroy" priority="critical">
    NEVER: git checkout, git revert, git push --force, rm.
    NEVER remove classes, files, or methods.
    NEVER modify MemCycle, ModCycle, or CycleIntegral.
    If state seems wrong → STOP and ASK.
  </rule>
  <rule id="ticket-first" priority="critical">
    Before any long action (>2 tool calls expected):
    1. Create a ticket in tickets/ describing:
       - Goal, current state, expected state
       - Alternatives considered, risks, assumptions, hypotheses
       - How to validate each assumption and hypothesis
       - How to validate the final result
    2. Search tickets/ for similar tickets. Link them. Update your ticket with their info.
    3. After each interaction loop, update the ticket with:
       - Lessons learned, progress made, assumptions (still valid or changed)
  </rule>
  <rule id="stay-on-track" priority="critical">
    If execution diverges from the original plan → 
    STOP and ASK FOR HELP. Do NOT improvise a new plan.
  </rule>
  <rule id="no-mod-operator" priority="critical">
    NEVER use the `%` (modulo) operator. Always use `Calc.div(a, b)` for division
    and `Calc.mod(a, b)` for modulo. These wrappers use DivMod internally and are
    Stainless-verified. The `%` operator is not natively supported by Stainless and
    will cause failures.
  </rule>
  <rule id="three-representations" priority="high">
    Every property in an article MUST be presented in ALL THREE forms:
    1. **English text** — Explain what the property means, covering the intuition
       (why it's true) and why it matters (what it enables), woven into natural prose
       without explicit labels. Place ABOVE the math as an overview.
    2. **Mathematical symbols** — LaTeX `` ```math \begin{aligned} ``` blocks
       with step-by-step derivations and bracketed labels:
       `[Q.E.D.]`, `[By Definition]`, `[By Lemma X]`, `[By Induction Hypothesis]`,
       `[By Modulo Property]`, `[Substitution]`, `[Simplification]`.
       Mathematical proof WITHIN the property section, after English, before code.
    3. **Scala verification code** — The `.holds` function block followed by a
       **source reference** linking to the exact file and function:
       ```
       This property is verified in the [
         ObjectName::functionName
       ](
         ../src/main/scala/path/to/file.scala
       ).
       ```
    See `PROOF_GUIDE.md` for full details. See finished articles (`integral-cycle.md`,
    `integral.md`, `cycle.md`, `modulo.md`, `list.md`) for real examples.
    Draft articles that skip any of the three forms are NOT ready for publication.
  </rule>
  <rule id="property-completeness" priority="high">
    Before publishing an article, verify that the article covers ALL important
    properties related to its subject. Do NOT rely solely on what is already in the
    draft. Instead:
    1. Search the codebase (src/main/scala/) for ALL verified `.holds` functions
       in the relevant packages — the code may have properties no article documents yet.
    2. Cross-reference with OBJECTS.md to confirm every listed property for that
       module has a corresponding section in the article.
    3. Cross-reference with `articles/learnings-capacity-argument.md` — it contains
       the most comprehensive catalog of proven properties (Section 16 lists 10
       properties, 9 proven, 1 open), documents failed approaches (Section 9),
       and maps the boundary between what is and isn't provable (Section 15).
       Any property listed there that belongs to the article's subject must appear
       in the article.
    4. Identify logical gaps: given the subject, what properties would a reader
       expect to see? (e.g. an article about "cycle integrals" should cover
       equivalence of definitions, invariance by concatenation, index shifts;
       an article about "sieve foundation" should cover unit cycle generation,
       strict monotonicity, filter preservation.)
    5. If a verified property exists but is NOT in the article → add it.
    6. If a property a reader would expect is NEITHER verified NOR in the article
       → flag it as a gap (document in the ticket, do NOT silently skip).
    7. If a property was attempted but verification failed → note it in the
       article as an open problem or limitation.
    8. If a property has a valid mathematical proof but NO corresponding
       Stainless `.holds` verification code → mark it explicitly as
       **"Draft — mathematically proven, Stainless verification pending"**
       in the article. This applies to:
       - The mathematical proof is included (English + LaTeX)
       - The Scala code block is marked as `// TODO: verify with Stainless`
         or omitted with an explicit note
       - The property is clearly distinct from fully verified properties
       - A ticket exists tracking what needs to be verified
       Do NOT silently include unverified math as if it were verified.
       The `three-representations` rule requires all three forms; if form 3
       is missing, the article must say so.
     9. If you CAN draft the missing Scala `.holds` verification for a
        mathematically proven property, do so — but keep it clearly marked
        as a draft:
        - Include the full Scala code block in the article
        - Annotate it with `// DRAFT — not yet verified through Stainless`
          or a similar clear comment
        - The surrounding text must state that this code is a draft and
          has NOT been run through `just verify`
        - Create or update a ticket tracking what needs to be verified
          and what obstacles are expected
        This lets the article serve as a reference for what verification
        work remains, rather than silently skipping form 3.
  </rule>
  <rule id="framing-integrity" priority="high">
    The abstract, introduction, and conclusion MUST accurately reflect what
    the article actually contains. Do NOT overpromise or claim results that
    are not proven within the article. Specifically:
    - **Abstract** — State only what is achieved. If some properties are
      mathematically proven but lack Stainless verification, say so.
      Do NOT claim "verified" for unverified code.
    - **Introduction** — Scope the article honestly. If the article covers
      only a subset of a topic (e.g., foundational lemmas, not the full
      sieve correctness proof), state this clearly.
    - **Conclusion** — Summarize what was proven, nothing more. If there
      are known limitations or open problems adjacent to the topic, note
      them rather than claiming completeness.
    - **Title** — Must not imply a broader result than what is proven.
      (e.g., "Proof of the Twin Prime Conjecture" is never acceptable;
      "Structural Properties of 2-Gaps in Sieve Sequences" is.)
    Cross-check each section against the others: if the conclusion claims
    something the introduction didn't scope, or the abstract promises what
    the body doesn't deliver, fix the mismatch.
  </rule>
  <rule id="no-emojis" priority="medium">
    Do NOT use emojis in articles. Use text markers instead:
    `[Verified]`, `[Open]`, `[Proven]`, `[Failed]`, etc.
    Emojis are inconsistent across renderers, cannot be searched, and
    break the academic tone of the articles.
  </rule>
</rules>

<antipatterns>
  - Rewriting entire files
  - Modifying MemCycle or ModCycle
  - Adding multiple assertions per verify cycle
  - Deleting files to fix compile errors (comment out instead)
  - Using `@extern` without explicit instruction
  - `git checkout` (blocked by opencode.json)
  - Starting a long task without a ticket
  - Using `%` operator instead of DivMod
</antipatterns>

<checklist-before>
  Before EVERY tool call, answer silently:
  <item>Is this exactly ONE small change? (If no → split it)</item>
  <item>Did `just verify` pass on the current state? (Check verify.log via <verify-log />, do NOT re-run)</item>
  <item>Am I about to run a denied command (git checkout, rm, --force)?</item>
  <item>Have I tried this same assertion 3+ times? (If yes → STOP and ASK)</item>
  <item>Am I plan mode or build mode? (Plan = no edits allowed)</item>
  <item>Is this a long action (>2 tool calls)? If yes → create/update a ticket first</item>
  <item>Did I search for similar tickets and link them?</item>
</checklist-before>

<checklist-after>
  After EVERY tool call, answer silently:
  <item>Did it succeed? (If error → read the error, do NOT retry blindly)</item>
  <item>Did `just verify` pass? (Check verify.log via <verify-log />, do NOT re-run)</item>
  <item>Is the total valid count the same or higher than before?</item>
  <item>If the verify timed out → STOP. Do NOT try a different approach.</item>
  <item>If stuck for 3+ attempts → STOP and ASK FOR HELP.</item>
  <item>Is execution still on track with the original plan? (If not → STOP and ASK)</item>
  <item>If this was part of a ticket → update the ticket (progress, lessons, assumptions)</item>
  <item>Did I update OBJECTS.md with new lemmas, methods, or objects?</item>
  <item>Did I update the ticket with the conclusion (outcome, lessons, what's next)?</item>
  <item>Are there articles in `articles/` that should be updated? If so, list them and ask the user.</item>
</checklist-after>
