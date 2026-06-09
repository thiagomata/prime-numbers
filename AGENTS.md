# Prime Numbers — Stainless Verification Project

<context>
SieveSequence: primes: List[BigInt], integral: CycleIntegral. head = primes.head.
Pipeline: nextResidues → nextExpanded → nextFiltered → nextSorted → 
           nextGaps → nextHeadResidueIndex → nextRotatedGaps
Each step calls ONE SieveUtils helper + ONE pre-verified function.
next() uses @extern (MemCycle bottleneck). Run tests first, verify second.
</context>

<commands>
  <verify>just verify</verify>
  <fast-compile>sbt 'set stainlessEnabled := false' compile</fast-compile>
  <tests>sbt 'set stainlessEnabled := false' 'testOnly v1.seq.sieve.*'</tests>
</commands>

<rules>
  <rule id="green-to-green" priority="critical">
    Run <verify /> before ANY change. Run <verify /> after ANY change.
    Stainless timeout IS failure. NEVER proceed from red state.
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
  <item>Did `just verify` pass on the current state? (If not → fix first)</item>
  <item>Am I about to run a denied command (git checkout, rm, --force)?</item>
  <item>Have I tried this same assertion 3+ times? (If yes → STOP and ASK)</item>
  <item>Am I plan mode or build mode? (Plan = no edits allowed)</item>
  <item>Is this a long action (>2 tool calls)? If yes → create/update a ticket first</item>
  <item>Did I search for similar tickets and link them?</item>
</checklist-before>

<checklist-after>
  After EVERY tool call, answer silently:
  <item>Did it succeed? (If error → read the error, do NOT retry blindly)</item>
  <item>Did `just verify` pass? (If timeout → that IS a failure)</item>
  <item>Is the total valid count the same or higher than before?</item>
  <item>If the verify timed out → STOP. Do NOT try a different approach.</item>
  <item>If stuck for 3+ attempts → STOP and ASK FOR HELP.</item>
  <item>Is execution still on track with the original plan? (If not → STOP and ASK)</item>
  <item>If this was part of a ticket → update the ticket (progress, lessons, assumptions)</item>
</checklist-after>
