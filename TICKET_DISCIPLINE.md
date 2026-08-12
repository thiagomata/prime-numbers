# Ticket Discipline

A ticket is the **persistent memory** of a piece of work. It must remain usable
by anyone (including yourself after context loss) who picks it up cold: it holds
the goal, the strategy, the current state, what is learned, what failed, and
the next action. A ticket that only records outcomes at the end has failed at
this job — by then the intermediate reasoning that kept the work on track is
gone.

This document defines the discipline. It is referenced from `AGENTS.md`
(`ticket-first` rule and the before/after checklists). It applies to every
long-running effort (>2 tool calls expected), verification or empirical.

## 1. When a ticket is required

Open a ticket in `tickets/active/` before any long action, per `ticket-first`.
"Long" means more than two tool calls of expected work. Markdown-only edits and
single-shot lookups do not need one.

Use the `tickets/active/TEMPLATE.md` structure as the starting point, then add
the persistent-memory sections below (§2). The template alone is not enough —
it captures planning but not the live state the discipline requires.

## 2. Required sections (the persistent-memory form)

Every active ticket should carry, in addition to the template's planning
content:

- **Goal** — one paragraph: what would make this ticket done. The single
  sentence a future reader needs to know what they're looking at.
- **Strategy** — the through-line: the approach and *why* it was chosen over
  alternatives. When the approach changes, update this — do not let it drift
  silently.
- **Current State** — where the work is *right now*. What is finished, what is
  in progress, what is blocked. A reader who reads only this section should
  know where to resume.
- **What is Learned** — durable facts, decisions, and refinements discovered
  during the work. This is the ticket's accumulation of knowledge, not a
  narrative.
- **Failed Paths** — approaches tried and abandoned, with *why*. Each entry
  must state the reason so it is not retried without a new idea. This is the
  most important section for avoiding loops.
- **Open Concerns** — known risks, unsatisfied preconditions, things that might
  be wrong. Surface them here rather than discovering them at a bad moment.
- **Next Action** — the single concrete next step, with any prerequisite reads
  or checks named explicitly. If the next action is a goal-level decision
  rather than an implementation step, say so and surface it (see §5).
- **Learning Log** — chronological table: date / learning / action. Append a
  row per interaction loop. This is the audit trail.

A ticket missing **Failed Paths** or **Current State** is not in
persistent-memory form, regardless of how detailed its other sections are.

## 3. Update continuously, not at the end

Update the ticket **as work proceeds**, not in a batch at completion:

- After each interaction loop, append a Learning Log row (the `ticket-first`
  rule already requires this).
- When a fact is established or refined, update **What is Learned** and
  **Current State** in the same edit.
- When an approach is tried and fails, add it to **Failed Paths** immediately,
  with the reason. Do not wait to see if a variation works first.
- When the next step changes, update **Next Action** before taking it.

The discipline's value is exactly that the ticket is correct *at every
moment*, so that an interruption (context loss, handoff, stop-and-ask) loses
nothing.

## 4. What goes in Failed Paths

A Failed Paths entry is a debt instrument: it exists so the same work is not
redone. Each entry should answer three questions:

1. **What** was attempted (specific — name the approach, not just the goal).
2. **Why** it failed (the actual reason, not "didn't work").
3. **What would change the verdict** (the condition under which retrying makes
   sense — a new idea, a new ingredient, a resolved dependency). This is
   mandatory, not optional: a "blocked" verdict without a falsifier is a
   permanent foreclosure based on one agent's judgment. See §6.

A entry like *"tried k=3, didn't work"* is useless. An entry like *"k=2
unconditionally reduces to twin primes at late layers; only worth retrying if a
short-window discrepancy bound of strength o(Q²/log²Q) is proved (that itself
is twin-prime-strength per the deep-dive)"* is useful — it names the falsifier,
so a future agent who obtains such a bound knows to re-attack.

Failed Paths should also record **pre-empted plans**: a next step that was
planned but abandoned after a read of existing docs showed it was already known
to be blocked. This prevents future-you from re-planning the same step. Note
that "the docs say it's blocked" is itself a claim that may be wrong (§6) — if
the pre-emption rests on a deep-dive's strength assessment rather than a
proven impossibility, say so, and re-verify the assessment before relying on
it permanently.

## 5. When to stop and surface vs. when to keep going

Do **not** stop at every checkpoint. Stopping has a cost (the user's attention,
lost momentum); it is warranted only when continuing would risk real
derailment. The rule:

- **Keep going** when the next step is clear *and* the ticket is genuinely
  progressing toward the goal — even if there is a fork, if you have a clear
  recommendation and the path is still the same goal, carry it forward
  yourself. Record the decision in the ticket (Current State / Learning Log)
  so the choice is visible, but do not interrupt for approval you don't need.
- **Stop and surface** only when one of these is true:
  1. the previously-defined path needs **strong reconsideration** (a core
     assumption was invalidated, a planned approach was shown to be blocked);
  2. **progress was overestimated** (what looked like a result was actually a
     restatement, a relocation of the wall, or a proxy masquerading as the
     target);
  3. there is **no clear path** from the current state to the goal.

The distinction between "fork with a clear recommendation" (keep going) and
"path needs strong reconsideration" (stop) is judgment, but the bias should be
toward continuing when you're honestly on-track. Surfacing options with a
recommendation is still useful at a genuine fork — but if your recommendation
is clear and the goal hasn't changed, act on it and note it; don't ask.

Examples:
- "Try lemma X" vs. "try lemma Y" when both serve the same goal — keep going,
  pick the better one, record it.
- "Accept the partial result and stop" vs. "pivot to a different milestone" —
  stop and surface; this changes what the work is for.
- "The path I planned is pre-empted by an established result" — stop and
  surface; the path needs strong reconsideration (case 1).
- "I proved a lemma that reduces the target to a known-open problem" — stop
  and surface; progress was overestimated if the reduction looked like a
  solution (case 2).

The `stay-on-track` and `stop-and-ask` rules already require surfacing
divergence. This section sharpens it: stopping is for when the path itself is
in question (cases 1–3 above), not for every fork. At a fork with a clear
recommendation that keeps the same goal, act on the recommendation, record it
in the ticket, and continue.

## 6. Nothing descriptive is ground truth — including this document

Everything **descriptive** in the project — tickets, `LEARNINGS.md`,
`properties/` notes, the analytic deep-dives, `OBJECTS.md`, even conclusions
the current agent wrote earlier — is *one agent's understanding at a moment*.
It is useful: it captures hard-won context and helps avoid repeating known
mistakes. It is **not** indisputable fact. Treat prior conclusions as:

- **Considered by default** — read them before re-deriving; they often save
  real work and catch known pitfalls.
- **Verifiable on demand** — when a prior conclusion is the load-bearing reason
  you're about to stop or change direction, check it against current code/data/
  math before relying on it. "The learnings doc says X is impossible" is a
  signal to investigate X's impossibility claim, not to abandon X.
- **Sometimes disputed** — if your current evidence contradicts a prior
  conclusion, the prior conclusion may be wrong. Record the dispute explicitly
  (a new Failed-Path entry, a Learning Log row, or a correction to the doc
  itself) rather than silently working around it.

This applies with extra force to **Failed Paths** (§4): a "blocked" verdict is
itself a claim that can be wrong. The previous attempt may have misjudged what
is possible, the landscape may have changed (new ingredients, new properties
established since), or the verdict may have been over-pessimistic. A Failed
Path treated as stone blocks the very re-attack that could refute it. So a good
Failed-Path entry names not just the reason but what would need to be true for
the verdict to flip — and re-attack is legitimate when that condition appears
to hold, *even if* a prior agent declared the path closed.

It also applies to **status assessments and "the wall"** language: "this
reduces to a known-open problem" or "this is twin-prime-strength" are claims
worth checking, not verdicts to accept on authority. They may be correct (and
often are), but the cost of accepting a false wall is high — it permanently
forecloses a direction — while the cost of re-verifying is usually small.

The one thing that *is* ground truth: the current code, the current data
files, the current `.holds` lemmas, and the current mathematical definitions.
When a descriptive note and the code/data disagree, the code/data wins until
the note is corrected.

## 7. Tickets survive their work

When a ticket completes or is abandoned:

- Move it to `tickets/done/` or `tickets/trash/` per the `tickets/README.md`
  lifecycle.
- Its durable findings should already be promoted out of the ticket into the
  permanent record: established properties into `properties/`, lemma names into
  `OBJECTS.md`, cross-cutting pitfalls into `LEARNINGS.md`. The ticket is the
  *working memory*; the permanent docs are the *long-term memory*. Do not let
  a result live only in a ticket.
- A closed ticket's Failed Paths are still useful — keep them readable for the
  next person approaching the same problem.

## 8. Anti-patterns

- **Outcome-only tickets**: rich planning up front, no Current State, no Failed
  Paths. The most common failure mode. The discipline exists to prevent this.
- **Learning Log as the only update channel**: appending rows without updating
  Current State / Failed Paths / Next Action means a reader must reconstruct
  the present from the history. They shouldn't have to.
- **Treating the ticket as a diary**: narrative prose ("today I tried...")
  instead of structured state. Use the sections; the Learning Log carries the
  chronological detail.
- **Silent re-planning**: deciding the next step diverged from the ticket's
  strategy and just doing it, without updating Strategy or surfacing. This is
  exactly the derailment the `stay-on-track` rule forbids.
- **Promoting results only at the end**: a result that lives in a ticket and
  nowhere else is invisible to the rest of the project. Promote as you go.

## Reference

- `AGENTS.md` `ticket-first`, `stay-on-track`, `stop-and-ask`, `red-cascade`
  rules — the hard requirements this discipline operationalizes.
- `tickets/active/TEMPLATE.md` — the planning-structure starting point.
- `tickets/active/prove-hereditary-shot-spacing-2026-07-23.md` — a worked
  example of the persistent-memory form (Goal / Strategy / Current State /
  Learned / Failed Paths / Concerns / Next Action / Learning Log).
- `LEARNINGS.md` — the long-term-memory counterpart: cross-cutting pitfalls
  promoted out of individual tickets.
