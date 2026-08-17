import base64

import pytest

from sieve_sequence import gap_heatmap as gh
from conftest import walk_stage as _walk_stage


def _small_stages():
    """Three real, small stages (heads 3, 5, 7) -- enough for a heatmap
    builder to run end to end without touching the real (large, gitignored)
    dataset."""
    return [
        _walk_stage(3, [2], 30),
        _walk_stage(5, [2, 3], 20),
        _walk_stage(7, [2, 3, 5], 15),
    ]


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


def test_shared_two_gap_offsets_track_compressed_head_changes():
    stages = [
        {"head": 5, "gaps": [4, 6, 2, 4, 2]},
        {"head": 9, "gaps": [6, 2, 4, 2]},
        {"head": 15, "gaps": [2, 4, 2]},
        {"head": 17, "gaps": [4, 2]},
    ]
    assert gh.shared_two_gap_offsets(stages) == [0, 0, 1, 2]


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
    brightness = [sum(color_by_value[value]) for value in values_in_order]
    assert brightness == sorted(brightness)


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


def test_simple_shift_row_diff_matches_lineage_walk_before_the_first_merge():
    # Before any merge, a constant offset IS the true one, so both approaches
    # must agree exactly (see simple_shift_row_diff's own docstring).
    prev = _walk_stage(3, [2], 20)
    cur = _walk_stage(5, [2, 3], 8)
    walk = gh.lineage_walk(prev, cur)
    shift_diffs = gh.simple_shift_row_diff(prev, cur)
    first_merge = next(i for i, (_diff, merge_count, _anchor) in enumerate(walk) if merge_count > 1)
    assert shift_diffs[:first_merge] == [0] * first_merge


def test_simple_shift_row_diff_drifts_after_the_first_merge():
    prev = _walk_stage(3, [2], 20)
    cur = _walk_stage(5, [2, 3], 8)
    shift_diffs = gh.simple_shift_row_diff(prev, cur)
    # Since prev's own gaps are all constant (2), the fixed-offset comparison
    # still lands on a "2" every other position by coincidence even after the
    # merge -- so the reliable signal isn't "every position now differs", it's
    # that this stops matching lineage_walk's true (always-0) diff, which
    # simple_shift_row_diff's docstring explains is expected past the row's
    # first real merge.
    assert shift_diffs == [0, 2, 0, 2, 0, 2, 0, 2]
    lineage_diffs = [diff for diff, _merge_count, _anchor in gh.lineage_walk(prev, cur)]
    assert lineage_diffs == [0] * len(lineage_diffs)
    assert shift_diffs != lineage_diffs


def test_compute_ages_per_row_first_row_starts_at_age_one():
    stages = [_walk_stage(3, [2], 8), _walk_stage(5, [2, 3], 4)]
    ages_per_row = gh.compute_ages_per_row(stages)
    assert ages_per_row[0] == [1] * len(stages[0]["gaps"])


def test_compute_ages_per_row_resets_to_one_on_merge_else_increments():
    stages = [_walk_stage(3, [2], 20), _walk_stage(5, [2, 3], 8)]
    ages_per_row = gh.compute_ages_per_row(stages)
    # Known cycle: merge_count alternates 1, 2, 1, 2, ... (see the lineage_walk
    # test above) -- a merge (index 1, 3, 5, 7) resets age to 1; a copy
    # (index 0, 2, 4, 6) increments the row-0 ancestor's age (1) to 2.
    assert ages_per_row[1] == [2, 1, 2, 1, 2, 1, 2, 1]


def test_choose_compressed_width_defaults_to_the_shortest_row():
    assert gh.choose_compressed_width([[1, 2, 3], [1, 2], [1, 2, 3, 4]]) == 2


def test_choose_compressed_width_percentile_100_is_the_longest_row():
    assert gh.choose_compressed_width([[1, 2, 3], [1, 2], [1, 2, 3, 4]], percentile=100) == 4


def test_known_prefix_len_stops_at_the_first_none():
    assert gh.known_prefix_len([1, 2, 3, None, 5]) == 3


def test_known_prefix_len_is_full_length_when_nothing_is_unknown():
    assert gh.known_prefix_len([1, 2, 3]) == 3


def test_choose_age_width_defaults_to_the_shortest_known_prefix():
    ages_per_row = [[1, 2, 3], [1, None, None], [1, 2, 3, 4]]
    assert gh.choose_age_width(ages_per_row) == 1


# --- calibration_values / run_ages_for_calibration ---------------------
# These back the fix for build_compressed_heatmap / build_age_heatmap /
# build_age_2focused_heatmap calibrating their color ramp on the full,
# untruncated row data while only rendering a truncated target_width of
# columns -- the ramp's colors no longer matched what was actually on screen.

def test_calibration_values_truncates_to_target_width():
    rows = [[1, 2, 3, 4], [5, 6, 7, 8]]
    assert gh.calibration_values(rows, target_width=2) == [1, 2, 5, 6]


def test_calibration_values_ignores_data_beyond_target_width():
    # The core regression: a distinct value that only appears beyond
    # target_width must never leak into the calibration set.
    rows = [[1, 1, 1, 999]]
    assert 999 not in gh.calibration_values(rows, target_width=3)


def test_calibration_values_excludes_the_given_value():
    rows = [[2, 4, 2, 6]]
    assert gh.calibration_values(rows, target_width=4, exclude=2) == [4, 6]


def test_calibration_values_skips_none_entries():
    rows = [[1, None, 3]]
    assert gh.calibration_values(rows, target_width=3) == [1, 3]


def test_run_ages_for_calibration_excludes_two_gaps_and_none_ages():
    compressed_per_row = [[2, 10, 2, 4]]
    ages_2focused_per_row = [[None, 3, None, 1]]
    assert gh.run_ages_for_calibration(compressed_per_row, ages_2focused_per_row, target_width=4) == [3, 1]


def test_run_ages_for_calibration_ignores_data_beyond_target_width():
    compressed_per_row = [[10, 2, 999]]
    ages_2focused_per_row = [[5, None, 7]]
    assert gh.run_ages_for_calibration(compressed_per_row, ages_2focused_per_row, target_width=2) == [5]


# --- sample_for_legend ---------------------------------------------------

def test_sample_for_legend_returns_everything_under_the_cap():
    assert gh.sample_for_legend([1, 2, 3], cap=24) == [1, 2, 3]


def test_sample_for_legend_always_keeps_first_and_last_over_the_cap():
    sampled = gh.sample_for_legend(list(range(100)), cap=10)
    assert sampled[0] == 0
    assert sampled[-1] == 99


def test_sample_for_legend_keeps_requested_values_even_over_the_cap():
    sampled = gh.sample_for_legend(list(range(1, 100)), cap=10, keep=(0,))
    assert 0 in sampled


# --- heatmap_cell_size / heatmap_canvas_width / draw_row_head_labels ----

def test_heatmap_cell_size_has_a_floor_of_one_pixel_wide():
    cell_w, _cell_h = gh.heatmap_cell_size(display_width=4000, num_stages=1000)
    assert cell_w == 1


def test_heatmap_cell_size_has_a_floor_of_two_pixels_tall():
    _cell_w, cell_h = gh.heatmap_cell_size(display_width=4000, num_stages=1000)
    assert cell_h == 2


def test_heatmap_cell_size_caps_height_at_twenty_pixels():
    _cell_w, cell_h = gh.heatmap_cell_size(display_width=10, num_stages=2)
    assert cell_h == 20  # uncapped this would be 900 // 2 == 450


def test_heatmap_canvas_width_fits_the_grid_when_the_legend_is_narrow():
    assert gh.heatmap_canvas_width(label_w=90, grid_w=500, legend_slot_count=2) == 90 + 500 + 20


def test_heatmap_canvas_width_widens_for_a_legend_wider_than_the_grid():
    # Regression: an earlier heatmap builder used to compute canvas_w without
    # this safeguard, so a legend needing more room than the grid got clipped.
    canvas_w = gh.heatmap_canvas_width(label_w=90, grid_w=50, legend_slot_count=20)
    assert canvas_w == 90 + 20 * 32
    assert canvas_w > 90 + 50 + 20


def test_draw_row_head_labels_labels_every_row_when_there_are_few():
    canvas = gh.Canvas(200, 200)
    stages = [{"head": 3}, {"head": 5}, {"head": 7}]
    gh.draw_row_head_labels(canvas, stages, label_w=90, top_margin=50, cell_h_display=10)
    labels = [el for el in canvas.elements if "h=" in el]
    assert len(labels) == 3
    assert "h=3" in labels[0]
    assert "h=7" in labels[-1]


def test_draw_row_head_labels_thins_out_for_many_rows():
    canvas = gh.Canvas(200, 200)
    stages = [{"head": h} for h in range(200)]
    gh.draw_row_head_labels(canvas, stages, label_w=90, top_margin=50, cell_h_display=2)
    labels = [el for el in canvas.elements if "h=" in el]
    assert len(labels) == 40  # label_every = max(1, 200 // 40) = 5 -> rows 0, 5, ..., 195 (40 of them)


# --- render_grid_png -----------------------------------------------------

def test_build_compressed_grid_png_places_exact_row_offsets():
    green = bytes(gh.hex_to_rgb(gh.TWO_GAP_COLOR))
    white = b"\xff\xff\xff"
    result = gh.build_compressed_grid_png(
        [{}, {}], [[2], [2]], {}, width=1, row_offsets=[0, 1]
    )
    assert result == (2, 2, [green + white, white + green])


def test_build_compressed_grid_png_preserves_fixed_stagger():
    green = bytes(gh.hex_to_rgb(gh.TWO_GAP_COLOR))
    white = b"\xff\xff\xff"
    result = gh.build_compressed_grid_png(
        [{}, {}], [[2], [2]], {}, width=1, stagger=1
    )
    assert result == (2, 2, [green + white, white + green])


def test_render_grid_png_writes_the_same_bytes_it_returns_as_a_data_uri(tmp_path):
    rows_rgb = [bytes((255, 0, 0) * 2), bytes((0, 255, 0) * 2)]
    png_path = str(tmp_path / "grid.png")
    uri = gh.render_grid_png(png_path, width_px=2, height_px=2, rows_rgb=rows_rgb)

    assert uri.startswith("data:image/png;base64,")
    with open(png_path, "rb") as png_file:
        file_bytes = png_file.read()
    assert base64.b64decode(uri.split(",", 1)[1]) == file_bytes


# --- build_*_heatmap: bug-fix regressions and caching equivalence --------

def test_build_age_2focused_heatmap_reserves_no_unused_boundary_curve_space(tmp_path, monkeypatch):
    # Regression: this view never calls draw_boundary_curves (its x-axis is
    # 2-focused compression, not raw gap index, so the curves' indices
    # wouldn't line up), but it used to reserve legend_h=122 anyway -- copied
    # from build_age_heatmap, which needs that space for its boundary-curve
    # caption. That left ~32px of unexplained blank space at the bottom.
    # It must reserve the same legend_h (90) as its true sibling,
    # build_compressed_heatmap.
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path))
    cell_sizes = []
    original = gh.heatmap_cell_size

    def spy(display_width, num_stages):
        result = original(display_width, num_stages)
        cell_sizes.append(result)
        return result

    monkeypatch.setattr(gh, "heatmap_cell_size", spy)
    stages = _small_stages()
    canvas = gh.build_age_2focused_heatmap(stages)

    _cell_w, cell_h = cell_sizes[0]
    grid_h = len(stages) * cell_h
    legend_h = canvas.height - 50 - grid_h  # top_margin is always 50
    assert legend_h == 90


def test_build_compressed_heatmap_calibrates_on_the_rendered_target_width(tmp_path, monkeypatch):
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path))
    seen_widths = []
    original = gh.calibration_values

    def spy(rows, target_width, **kwargs):
        seen_widths.append(target_width)
        return original(rows, target_width, **kwargs)

    monkeypatch.setattr(gh, "calibration_values", spy)
    stages = _small_stages()
    compressed_per_row = [gh.compress_around_two(stage["gaps"]) for stage in stages]
    expected = min(gh.choose_compressed_width(compressed_per_row), gh.MAX_DISPLAY_WIDTH)

    gh.build_compressed_heatmap(stages)
    assert seen_widths == [expected]


def test_build_compressed_heatmap_forwards_exact_row_offsets(tmp_path, monkeypatch):
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path))
    seen_offsets = []
    original = gh.build_compressed_grid_png

    def spy(*args, **kwargs):
        seen_offsets.append(kwargs["row_offsets"])
        return original(*args, **kwargs)

    monkeypatch.setattr(gh, "build_compressed_grid_png", spy)
    gh.build_compressed_heatmap(_small_stages(), row_offsets=[0, 0, 1])
    assert seen_offsets == [[0, 0, 1]]


def test_build_age_heatmap_calibrates_on_the_rendered_target_width(tmp_path, monkeypatch):
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path))
    seen_widths = []
    original = gh.calibration_values

    def spy(rows, target_width, **kwargs):
        seen_widths.append(target_width)
        return original(rows, target_width, **kwargs)

    monkeypatch.setattr(gh, "calibration_values", spy)
    stages = _small_stages()
    ages_per_row = gh.compute_ages_per_row(stages)
    expected = min(gh.choose_age_width(ages_per_row), gh.MAX_DISPLAY_WIDTH)

    gh.build_age_heatmap(stages)
    assert seen_widths == [expected]


def test_build_age_2focused_heatmap_calibrates_on_the_rendered_target_width(tmp_path, monkeypatch):
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path))
    calls = []
    original = gh.run_ages_for_calibration

    def spy(compressed_per_row, ages_2focused_per_row, target_width):
        calls.append(target_width)
        return original(compressed_per_row, ages_2focused_per_row, target_width)

    monkeypatch.setattr(gh, "run_ages_for_calibration", spy)
    gh.build_age_2focused_heatmap(_small_stages())
    assert len(calls) == 1


def test_build_age_heatmap_matches_whether_ages_per_row_is_precomputed_or_not(tmp_path, monkeypatch):
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path))
    stages = _small_stages()
    ages_per_row = gh.compute_ages_per_row(stages)

    default = gh.build_age_heatmap(stages, png_name="a.png")
    precomputed = gh.build_age_heatmap(stages, png_name="b.png", ages_per_row=ages_per_row)
    def _strip_timestamps(svg):
        lines = svg.splitlines(True)
        return "".join(l for l in lines if "<!-- Generated:" not in l)
    assert _strip_timestamps(default.render()) == _strip_timestamps(precomputed.render())


def test_every_heatmap_builder_renders_a_well_formed_svg(tmp_path, monkeypatch):
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path))
    stages = _small_stages()
    builders = [
        gh.build_heatmap, gh.build_compressed_heatmap,
        gh.build_simple_shift_diff_heatmap,
        gh.build_age_heatmap, gh.build_age_2focused_heatmap,
    ]
    for build in builders:
        canvas = build(stages)
        svg = canvas.render()
        assert svg.startswith("<svg "), build.__name__
        assert svg.rstrip().endswith("</svg>"), build.__name__
        assert canvas.width > 0 and canvas.height > 0, build.__name__


# --- validate_stages: structural sanity checks on loaded stage data --------

def test_validate_stages_accepts_real_well_formed_stages():
    gh.validate_stages(_small_stages())  # must not raise


def test_validate_stages_rejects_an_empty_stage_list():
    with pytest.raises(ValueError, match="no stages"):
        gh.validate_stages([])


def test_validate_stages_rejects_a_head_below_two():
    stages = _small_stages()
    stages[0]["head"] = 1
    with pytest.raises(ValueError, match="not a valid prime head"):
        gh.validate_stages(stages)


def test_validate_stages_rejects_a_stage_with_no_survivors():
    stages = _small_stages()
    stages[0]["survivors"] = []
    with pytest.raises(ValueError, match="no survivors"):
        gh.validate_stages(stages)


def test_validate_stages_rejects_survivors_that_are_not_strictly_increasing():
    stages = _small_stages()
    stages[0]["survivors"][2] = stages[0]["survivors"][1]  # duplicate, not increasing
    with pytest.raises(ValueError, match="strictly increasing"):
        gh.validate_stages(stages)


def test_validate_stages_rejects_gaps_and_survivors_of_mismatched_length():
    stages = _small_stages()
    stages[0]["gaps"].pop()
    with pytest.raises(ValueError, match="must match 1:1"):
        gh.validate_stages(stages)


def test_validate_stages_rejects_a_gap_that_does_not_connect_to_its_survivor():
    stages = _small_stages()
    stages[0]["gaps"][2] += 1  # now disagrees with the recorded survivor
    with pytest.raises(ValueError, match="does not connect"):
        gh.validate_stages(stages)


def test_validate_stages_skips_the_gap_consistency_check_when_gaps_are_absent():
    # hit_miss_heatmap.py's synthesized stage 0 has survivors but no "gaps"
    # key at all -- validate_stages must still accept it.
    gh.validate_stages([{"head": 2, "survivors": [2, 3, 4, 5]}])


# --- main(): empty/missing-CSV guard --------------------------------------

def test_main_raises_a_clear_error_when_the_csv_is_missing(tmp_path, monkeypatch):
    monkeypatch.setattr(gh, "CSV_PATH", str(tmp_path / "missing.csv"))
    with pytest.raises(SystemExit, match="not found"):
        gh.main()


def test_main_raises_a_clear_error_when_the_csv_has_no_stage_rows(tmp_path, monkeypatch):
    # Regression: main() used to only check that the CSV file existed, not
    # that it had any data rows. If generate_gaps.py was killed right after
    # writing the header, load_stages() returned [] and build_heatmap crashed
    # with a bare IndexError on stages[0] instead of a clear message.
    csv_path = tmp_path / "empty.csv"
    csv_path.write_text("stage_index,head,gap,survivor\n")
    monkeypatch.setattr(gh, "CSV_PATH", str(csv_path))
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path / "out"))
    with pytest.raises(SystemExit, match="no stage rows"):
        gh.main()


def test_main_raises_a_clear_error_when_a_stage_row_is_corrupted(tmp_path, monkeypatch):
    # A gap column that doesn't connect its own row's survivors is exactly
    # what a misaligned or partially-overwritten CSV row looks like -- must
    # fail loudly before any heatmap is built, not draw a wrong picture.
    csv_path = tmp_path / "corrupt.csv"
    csv_path.write_text(
        "stage_index,head,gap_index,gap,survivor\n"
        "1,3,0,2,5\n"
        "1,3,1,99,9\n"  # gap 99 does not connect survivor 5 to survivor 9
    )
    monkeypatch.setattr(gh, "CSV_PATH", str(csv_path))
    monkeypatch.setattr(gh, "OUT_DIR", str(tmp_path / "out"))
    with pytest.raises(SystemExit, match="failed validation"):
        gh.main()
