"""Re-runnable checks for the claims this figure set makes, so they stand on
their own rather than "we checked this once in conversation." Run after
generate_gaps.py (and before trusting gap_heatmap.py's output, or before
citing any of the numbers in properties/sieve-sequence/safe-zone-exhaustion-curve.md).

Run: python3 verify.py
Exits 0 if every proven claim holds, 1 otherwise. The unproven estimate
(Property 3 in the properties file) is reported but never fails the run --
it's explicitly a conjecture, not a guarantee, and treating a violation of it
as a bug would misrepresent what's actually been proven.
"""

import sys

from gap_heatmap import (
    estimated_boundary_indices,
    first_composite_index,
    lineage_walk,
    load_stages,
    proven_safe_boundary_indices,
)

KNOWN_SMALL_STAGE_GAPS = {
    3: {"all_equal": 2},
    5: {"alternates": [2, 4]},
    7: {"prefix": [4, 2, 4, 2, 4, 6, 2, 6]},
}


def check_known_small_stages(stages):
    """Stages 1-3 have hand-verified gap cycles (see the conversation history
    and articles/chapter6/sieve-sequence.md) independent of any code here."""
    ok = True
    by_head = {s["head"]: s for s in stages}

    s3 = by_head.get(3)
    if s3 is None or any(g != 2 for g in s3["gaps"]):
        print("FAIL: stage head=3 should have every gap equal to 2 (odd numbers, 2 apart)")
        ok = False

    s5 = by_head.get(5)
    if s5 is None or any(g != (2 if i % 2 == 0 else 4) for i, g in enumerate(s5["gaps"])):
        print("FAIL: stage head=5 should alternate gaps 2, 4, 2, 4, ...")
        ok = False

    s7 = by_head.get(7)
    expected = KNOWN_SMALL_STAGE_GAPS[7]["prefix"]
    if s7 is None or s7["gaps"][:len(expected)] != expected:
        print(f"FAIL: stage head=7 should start with {expected}")
        ok = False

    if ok:
        print("PASS: known small-stage gap cycles (head 3, 5, 7) match hand-verified values")
    return ok


def check_first_composite_is_head_squared(stages):
    """Elementary fact (see safe-zone-exhaustion-curve.md, Property 1): the
    first survivor that isn't prime is always exactly head^2, whenever the
    generated window reaches far enough to observe it at all."""
    ok = True
    checked = 0
    for s in stages:
        idx = first_composite_index(s["survivors"])
        if idx is None:
            continue
        checked += 1
        head = s["head"]
        value = s["survivors"][idx]
        if value != head * head:
            print(f"FAIL: head={head} first composite survivor is {value}, expected {head * head}")
            ok = False
    if ok:
        print(f"PASS: first composite survivor == head^2 exactly, for all {checked} stages where observable")
    return ok


def check_copy_or_merge_theorem_is_exact(stages):
    """Every stage transition's gaps are either copied unchanged or merged by
    exact summation -- lineage_walk's diff must be 0 everywhere it computes
    one, with zero exceptions, across the whole dataset."""
    ok = True
    total_compared = 0
    for row in range(1, len(stages)):
        walk = lineage_walk(stages[row - 1], stages[row])
        total_compared += len(walk)
        for i, (diff, _merge_count, _anchor) in enumerate(walk):
            if diff != 0:
                print(f"FAIL: row {row} (head={stages[row]['head']}) position {i} has nonzero diff {diff}")
                ok = False
    if ok:
        print(f"PASS: copy-or-merge theorem holds exactly across all {total_compared} compared positions")
    return ok


def check_schroeder_bound_never_violated(stages):
    """Property 2 in safe-zone-exhaustion-curve.md is proven for any prime
    p >= 11 -- it must never exceed the real observed boundary wherever we
    have ground truth to check it against."""
    ok = True
    checked = 0
    proven = proven_safe_boundary_indices(stages)
    for s, bound in zip(stages, proven):
        if bound is None:
            continue
        idx = first_composite_index(s["survivors"])
        if idx is None:
            continue
        checked += 1
        if bound > idx:
            print(f"FAIL: head={s['head']} proven bound {bound} exceeds actual {idx} -- Property 2 violated")
            ok = False
    if ok:
        print(f"PASS: Schroeder (2017) proven safe bound never violated, across {checked} checkable stages")
    return ok


def report_estimated_bound_fit(stages):
    """Informational only -- Property 3 is an unproven conjecture, so a
    violation here is reported, not treated as a failure."""
    estimated = estimated_boundary_indices(stages)
    violations = []
    checked = 0
    for s, est in zip(stages, estimated):
        idx = first_composite_index(s["survivors"])
        if idx is None:
            continue
        checked += 1
        if est > idx:
            violations.append((s["head"], est, idx))
    print(f"INFO: estimated (unproven) boundary checked against {checked} stages, "
          f"{len(violations)} violation(s): {violations if violations else 'none'}")


def main() -> int:
    stages = load_stages()
    checks = [
        check_known_small_stages,
        check_first_composite_is_head_squared,
        check_copy_or_merge_theorem_is_exact,
        check_schroeder_bound_never_violated,
    ]
    results = [check(stages) for check in checks]
    report_estimated_bound_fit(stages)

    if all(results):
        print("\nall proven claims verified")
        return 0
    print("\nsome proven claims FAILED verification -- do not cite until fixed")
    return 1


if __name__ == "__main__":
    sys.exit(main())
