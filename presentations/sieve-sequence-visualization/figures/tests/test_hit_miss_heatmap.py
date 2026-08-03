from fractions import Fraction

import hit_miss_heatmap as hmh

SAMPLE_CSV = hmh.SAMPLE_CSV_PATH


def test_sample_csv_is_present():
    # This fixture is committed specifically so this module's tests (and the
    # figure itself) don't depend on the large, gitignored full dataset.
    import os
    assert os.path.exists(SAMPLE_CSV), f"missing committed sample CSV: {SAMPLE_CSV}"


def test_load_stages_synthesizes_stage_zero_with_no_filter():
    stages = hmh.load_stages(SAMPLE_CSV, 1)
    assert len(stages) == 1
    assert stages[0]["head"] == 2
    assert stages[0]["survivors"][:5] == [2, 3, 4, 5, 6]


def test_load_stages_reads_the_requested_number_of_stages():
    stages = hmh.load_stages(SAMPLE_CSV, 4)
    assert len(stages) == 4
    assert [stage["head"] for stage in stages] == [2, 3, 5, 7]


def test_load_stages_stage_one_survivors_match_odd_numbers_from_head():
    stages = hmh.load_stages(SAMPLE_CSV, 2)
    stage_one = stages[1]
    assert stage_one["head"] == 3
    assert stage_one["survivors"][:5] == [5, 7, 9, 11, 13]


def test_stage_captions_stage_zero_has_flagged_fraction_one():
    stages = hmh.load_stages(SAMPLE_CSV, 2)
    captions = hmh.stage_captions(stages)
    flagged_str, period_str = captions[0]
    assert flagged_str == f"flagged fraction: {Fraction(1, 1)}"
    assert period_str == "gaps repeat: [1]"


def test_stage_captions_stage_one_flagged_fraction_is_one_half():
    stages = hmh.load_stages(SAMPLE_CSV, 2)
    captions = hmh.stage_captions(stages)
    flagged_str, _period_str = captions[1]
    assert flagged_str == f"flagged fraction: {Fraction(1, 2)}"


def test_stage_captions_prints_short_periods_in_full():
    stages = hmh.load_stages(SAMPLE_CSV, 4)
    captions = hmh.stage_captions(stages)
    # stage 2 (head=5): period [2, 4]
    assert captions[2][1] == "gaps repeat: [2,4]"
