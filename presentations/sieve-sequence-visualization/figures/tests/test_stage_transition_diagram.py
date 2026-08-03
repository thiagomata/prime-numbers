import stage_transition_diagram as std


def test_build_transition_stage_zero_is_the_synthesized_no_filter_case():
    transition = std.build_transition(0)
    assert transition["head_before"] == 2
    assert transition["head_after"] == 3
    assert transition["tail_before"] == []
    assert transition["new_prime"] == 2
    assert transition["modulus_before"] == 1
    assert transition["modulus_after"] == 2


def test_build_transition_stage_one_matches_head_3_to_5():
    transition = std.build_transition(1)
    assert transition["head_before"] == 3
    assert transition["head_after"] == 5
    assert transition["tail_before"] == [2]
    assert transition["tail_after"] == [2, 3]
    assert transition["new_prime"] == 3
    assert transition["modulus_before"] == 2
    assert transition["modulus_after"] == 6


def test_build_transition_stage_two_matches_head_5_to_7():
    transition = std.build_transition(2)
    assert transition["head_before"] == 5
    assert transition["head_after"] == 7
    assert transition["tail_before"] == [2, 3]
    assert transition["new_prime"] == 5
    assert transition["modulus_before"] == 6
    assert transition["modulus_after"] == 30


def test_generate_numbers_window_walks_the_cycle_forward_from_head():
    numbers, gaps = std.generate_numbers_window(3, [2], 5)
    assert numbers == [3, 5, 7, 9, 11]
    assert gaps == [2, 2, 2, 2]


def test_generate_numbers_window_repeats_a_multi_element_cycle():
    numbers, gaps = std.generate_numbers_window(5, [2, 4], 5)
    assert numbers == [5, 7, 11, 13, 17]
    assert gaps == [2, 4, 2, 4]


def test_generate_numbers_window_single_sample_has_no_gaps():
    numbers, gaps = std.generate_numbers_window(5, [2, 4], 1)
    assert numbers == [5]
    assert gaps == []


def test_compute_steps_base_unit_matches_stage_ones_known_gap_cycle():
    transition = std.build_transition(1)
    steps = std.compute_steps(transition)
    assert steps["base_unit"] == [2]
    assert steps["new_base_unit"] == [2, 4]


def test_compute_steps_repeat_unit_tiles_base_unit_new_prime_times():
    transition = std.build_transition(1)
    steps = std.compute_steps(transition)
    assert steps["repeat_unit"] == steps["base_unit"] * transition["new_prime"]


def test_compute_steps_rotated_unit_is_repeat_unit_shifted_left_by_one():
    transition = std.build_transition(2)  # period-2 base unit: rotation is visible here
    steps = std.compute_steps(transition)
    repeat_unit = steps["repeat_unit"]
    assert steps["rotated_unit"] == repeat_unit[1:] + repeat_unit[:1]


def test_compute_steps_kept_gaps_close_the_loop_to_new_base_unit():
    # The whole point of step 4's rotation: filtering the kept survivors
    # produces exactly the new stage's TRUE periodic gap cycle, not just a
    # prefix of it.
    transition = std.build_transition(1)
    steps = std.compute_steps(transition)
    period_len = len(steps["new_base_unit"])
    assert steps["kept_gaps"][:period_len] == steps["new_base_unit"]


def test_compute_steps_filters_out_exactly_the_multiples_of_new_prime():
    transition = std.build_transition(1)
    steps = std.compute_steps(transition)
    new_prime = transition["new_prime"]
    assert all(value % new_prime != 0 for value in steps["kept"])
    dropped = set(steps["values"]) - set(steps["kept"])
    assert dropped and all(value % new_prime == 0 for value in dropped)


def test_row_width_accounts_for_gaps_between_chips():
    assert std.row_width(1, w=10, gap=5) == 10
    assert std.row_width(3, w=10, gap=5) == 10 * 3 + 5 * 2


def test_row_width_zero_chips_is_zero():
    assert std.row_width(0) == 0
