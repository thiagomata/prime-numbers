import gap_heatmap as gh


def test_compress_around_two_keeps_twos_and_sums_runs_between_them():
    # Example from the function's own docstring.
    assert gh.compress_around_two([6, 4, 2, 4, 2, 4, 6, 2]) == [10, 2, 4, 2, 10, 2]


def test_compress_around_two_with_no_twos_collapses_to_one_run():
    assert gh.compress_around_two([4, 6, 4]) == [14]


def test_compress_around_two_with_only_twos_is_unchanged():
    assert gh.compress_around_two([2, 2, 2]) == [2, 2, 2]


def test_compress_around_two_is_linear_not_cyclic():
    # Leading/trailing non-2 runs are NOT wrapped together (unlike the Scala
    # compressAround2), since this data is a prefix, not a complete period.
    assert gh.compress_around_two([4, 2, 4]) == [4, 2, 4]


def test_compress_around_two_with_anchor_matches_compress_around_two_values():
    gaps = [6, 4, 2, 4, 2, 4, 6, 2]
    compressed, anchors = gh.compress_around_two_with_anchor(gaps)
    assert compressed == gh.compress_around_two(gaps)
    assert len(compressed) == len(anchors)


def test_compress_around_two_with_anchor_anchors_point_at_the_last_raw_gap():
    # [4, 2, 4]: run "4" (index 0) closes at index 0, the "2" is index 1,
    # trailing run "4" closes at the last index (2).
    compressed, anchors = gh.compress_around_two_with_anchor([4, 2, 4])
    assert compressed == [4, 2, 4]
    assert anchors == [0, 1, 2]


def test_first_composite_index_returns_none_when_all_survivors_are_prime():
    assert gh.first_composite_index([3, 5, 7, 11, 13]) is None


def test_first_composite_index_finds_the_first_non_prime():
    assert gh.first_composite_index([3, 5, 7, 9, 11]) == 3


def test_first_composite_index_head_squared_is_always_the_first_composite():
    # Property 1 (safe-zone-exhaustion-curve.md): for a stage's own generated
    # sequence, the first composite survivor is always exactly head^2.
    head = 7
    survivors = [head, head + 4, head + 6, head * head]
    assert gh.first_composite_index(survivors) == 3


def test_estimated_boundary_indices_stage_one_uses_only_the_2_filter():
    # Stage 1 (head=3): density is exactly 1/2 (only "not even" applied so far).
    stages = [{"head": 3}]
    [index] = gh.estimated_boundary_indices(stages)
    assert index == 0.5 * (3 * 3 - 3)


def test_estimated_boundary_indices_is_always_computed_never_none():
    stages = [{"head": 3}, {"head": 5}, {"head": 7}]
    indices = gh.estimated_boundary_indices(stages)
    assert len(indices) == 3
    assert all(index is not None for index in indices)


def test_proven_safe_boundary_indices_is_none_below_head_11():
    stages = [{"head": 3}, {"head": 5}, {"head": 7}]
    assert gh.proven_safe_boundary_indices(stages) == [None, None, None]


def test_proven_safe_boundary_indices_is_never_larger_than_the_true_boundary():
    # Schroeder's bound is proven to never exceed the true first-composite
    # index, for any prime head >= 11.
    for head in (11, 13, 17, 19, 23, 29):
        [bound] = gh.proven_safe_boundary_indices([{"head": head}])
        assert bound is not None
        assert bound <= head * head - head


def test_hex_to_rgb_parses_standard_hex_colors():
    assert gh.hex_to_rgb("#ffffff") == (255, 255, 255)
    assert gh.hex_to_rgb("#000000") == (0, 0, 0)
    assert gh.hex_to_rgb("2a78d6") == (0x2a, 0x78, 0xd6)


def test_ramp_color_endpoints_match_the_ramp_anchors():
    ramp = ["#000000", "#ffffff"]
    assert gh.ramp_color(0.0, ramp) == (0, 0, 0)
    assert gh.ramp_color(1.0, ramp) == (255, 255, 255)


def test_ramp_color_clamps_out_of_range_positions():
    ramp = ["#000000", "#ffffff"]
    assert gh.ramp_color(-5.0, ramp) == gh.ramp_color(0.0, ramp)
    assert gh.ramp_color(5.0, ramp) == gh.ramp_color(1.0, ramp)


def test_ramp_color_midpoint_is_the_average_of_neighboring_anchors():
    ramp = ["#000000", "#ffffff"]
    assert gh.ramp_color(0.5, ramp) == (128, 128, 128)


def test_lerp_rgb_endpoints_and_midpoint():
    assert gh.lerp_rgb((0, 0, 0), (100, 100, 100), 0.0) == (0, 0, 0)
    assert gh.lerp_rgb((0, 0, 0), (100, 100, 100), 1.0) == (100, 100, 100)
    assert gh.lerp_rgb((0, 0, 0), (100, 100, 100), 0.5) == (50, 50, 50)


def test_build_equalized_color_map_covers_every_distinct_value():
    color_by_value = gh.build_equalized_color_map([2, 2, 2, 4, 6])
    assert set(color_by_value) == {2, 4, 6}


def test_build_equalized_color_map_is_monotonic_in_value_order():
    # Histogram equalization must still preserve order along the ramp, even
    # though position spacing is by frequency rather than raw magnitude.
    ramp = ["#000000", "#808080", "#ffffff"]
    color_by_value = gh.build_equalized_color_map([2, 2, 2, 2, 4, 6, 8], ramp=ramp)
    values_in_order = sorted(color_by_value)
    brightness = [sum(color_by_value[v]) for v in values_in_order]
    assert brightness == sorted(brightness)


def _walk_stage(head, tail_primes, count):
    """Mirrors generate_gaps.py's trial-division walk: `count` survivors of
    `head`'s stage (coprime to every prime in tail_primes), with their gaps."""
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


def test_lineage_walk_diff_is_zero_across_a_real_stage_transition():
    # Real head=3 -> head=5 transition: the copy-or-merge theorem guarantees
    # diff is exactly 0 everywhere the walk can compute it.
    prev = _walk_stage(3, [2], 20)
    cur = _walk_stage(5, [2, 3], 8)
    walk = gh.lineage_walk(prev, cur)
    assert len(walk) == len(cur["gaps"])
    assert all(diff == 0 for diff, _merge_count, _anchor in walk)


def test_lineage_walk_merges_exactly_where_a_prev_survivor_is_removed():
    # head=3's survivors that are multiples of 3 (9, 15, 21, ...) are exactly
    # the ones the new head=5 filter doesn't add -- so every other cur gap
    # merges two prev gaps, matching the known alternating [2,4] cycle.
    prev = _walk_stage(3, [2], 20)
    cur = _walk_stage(5, [2, 3], 8)
    walk = gh.lineage_walk(prev, cur)
    merge_counts = [merge_count for _diff, merge_count, _anchor in walk]
    assert merge_counts == [1, 2, 1, 2, 1, 2, 1, 2]


def test_lineage_walk_anchor_points_at_the_closing_prev_gap_index():
    prev = _walk_stage(3, [2], 20)
    cur = _walk_stage(5, [2, 3], 8)
    walk = gh.lineage_walk(prev, cur)
    anchors = [anchor for _diff, _merge_count, anchor in walk]
    # anchors are strictly increasing prev-gap indices, one per cur gap.
    assert anchors == sorted(set(anchors))
    assert len(anchors) == len(cur["gaps"])


def test_lineage_walk_stops_early_when_prev_runs_out_of_gaps():
    prev = _walk_stage(3, [2], 3)  # too few prev gaps to cover cur's full window
    cur = _walk_stage(5, [2, 3], 8)
    walk = gh.lineage_walk(prev, cur)
    assert len(walk) < len(cur["gaps"])
