# A few fixed-window contact checks

Created: 2026-10-26
Status: Bounded empirical check complete

## START HERE

Empirically check whether zero-height integer contacts (focused 2-cells)
remain in a few fixed fences as successive prime filters are installed.
Separate illustrative successes from a negative control; no general
persistence or hypothetical-last-pair conclusion is intended.

## Goal

Report exact initial/final candidates and deletion stages for five preselected
endpoint windows, with independently checked finite certification.

## Strategy

Use [10,50],[100,150],[155,175],[200,250],[1000,1100]. Both endpoints must
remain inside each closed fence. Begin with filters2,3,5; add every further
prime through floor(sqrt(upper endpoint)). Test exact activated prime-height
zeros at integers instead of numerically sampling the continuous graph.
Verify final sets by independent trial primality and preserve a reproducible
read-only snippet in research/, not a new candidate or runtime module.

## Related Work

- [Continuous contacts](../../candidates/continuous-contact-research-directions.md).
- [Previous reverse audit](reverse-rejection-history-audit-2026-10-25.md).
- [Previous jump audit](front-jump-compensation-audit-2026-10-26.md).
- [Square certification](../../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md).

## Current State

Windows chosen before diagnostic execution. Critic and Monitor approved content.
Exact diagnostic passed nestedness and independent primality checks in all
windows. Initial-to-final counts:5->4,5->3,2->0,4->2,11->5. The negative
control [155,175] empties at13 after its first pair is removed by7.
Saved [the research result](../../properties/sieve-sequence/research/fixed-window-contact-check-2026-10-26.md).
Its exact embedded snippet reran successfully; both Markdown files pass links,
fences and whitespace. Monitor independently reproduced the arithmetic and
approved the actual saved note. No runtime sources or articles changed.

## What is Learned

For the unweighted prime-filter height, integer contacts are exact divisibility
conditions. Finite square-root filtering certifies contacts inside a fixed
fence; it need not stabilize the full real-valued curve between integers.
Prime-only filters verify the all-integer construction's zero set, not its
positive heights: composite divisor contributions are omitted. Finite fences
can retain certified pairs or lose every candidate.

## Failed Paths

Pre-empted: treating a positive continuous area or floating-point near-zero
as an integer candidate. Use exact zero indicators; reopen a continuous
sampling argument only with a proved link to integer contacts.
One atomic ticket patch had an unrelated context hunk and failed without
changing a file; the corrected scoped patch succeeded. No arithmetic failure.

## Open Concerns

These ordinary numerical fences cannot be claimed to lie beyond a true last
twin pair. Finite positive examples do not prove recurring nonempty fences.
Activated contacts can remain after the sieve head passes them; distinguish
proper-divisor rejection from simply leaving the forward stream.

## Assumptions and Validation

All lower endpoints exceed5; test each filter only as a proper divisor.
No omitted prime through sqrt(upper), and both pair endpoints must be in
range. Check nested sets, exact killed members, independent trial primality,
embedded snippet rerun, and Markdown links/fences/whitespace. No Scala,
PDF or project Python source gates are affected by the Markdown-only save.

## Next Action

No work remains in this bounded check. Positive fences illustrate certified
twins and the empty fence rules out unconditional initial-contact persistence;
no general trapping result follows from this sample.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-26 | A meaningful few-fence illustration should include an empty final fence, not only known successful regions. | Preselected five endpoint windows and scoped exact integer checks. |
| 2026-10-26 | Four fences retain certified contacts and one empties. All nestedness and independent primality comparisons pass. | Obtained Critic/Monitor content approval for the reproducible finite findings. |
| 2026-10-26 | Exact embedded reproduction and both Markdown checks pass; Monitor independently recomputed and reviewed results. | Completed the five-fence check with the negative control and finite scope explicit. |
