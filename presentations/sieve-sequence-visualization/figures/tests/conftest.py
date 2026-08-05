"""Makes the sibling figure scripts (svg_kit.py, gap_heatmap.py, ...) importable
from this tests/ directory without turning the figures/ directory into a package."""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

# Hand-verified small-stage gap cycles (see articles/chapter6/sieve-sequence.md),
# independent of any code here. Shared by tests that need ground truth to check
# generate_gaps.py's compute_full_period against. verify.py keeps its own copy
# of this same data for its own (non-test) purpose, so this is deliberately
# duplicated rather than imported from there -- tests for the base module
# (generate_gaps.py) shouldn't need to import verify.py, which sits at the top
# of this directory's import stack (it imports gap_heatmap.py).
KNOWN_SMALL_STAGE_GAPS = {
    3: {"all_equal": 2},
    5: {"alternates": [2, 4]},
    7: {"prefix": [4, 2, 4, 2, 4, 6, 2, 6]},
}


def walk_stage(head, tail_primes, count):
    """Mirrors generate_gaps.py's trial-division walk: `count` survivors of
    `head`'s stage (coprime to every prime in tail_primes), with their gaps.
    Shared fixture helper for tests that need small, real stage dicts
    ({"head", "gaps", "survivors"}) without depending on the generated CSV."""
    survivors = []
    candidate = head + 1
    while len(survivors) < count:
        if all(candidate % p != 0 for p in tail_primes):
            survivors.append(candidate)
        candidate += 1
    gaps = []
    previous_value = head
    for survivor in survivors:
        gaps.append(survivor - previous_value)
        previous_value = survivor
    return {"head": head, "gaps": gaps, "survivors": survivors}
