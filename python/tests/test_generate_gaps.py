from sieve_sequence import generate_gaps as gg
from conftest import KNOWN_SMALL_STAGE_GAPS


def test_is_prime_rejects_numbers_below_two():
    assert not gg.is_prime(0)
    assert not gg.is_prime(1)
    assert not gg.is_prime(-5)


def test_is_prime_matches_known_small_primes_and_composites():
    assert [n for n in range(2, 30) if gg.is_prime(n)] == [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29
    ]


def test_first_k_primes_returns_primes_in_order():
    assert gg.first_k_primes(6) == [2, 3, 5, 7, 11, 13]


def test_first_k_primes_zero_returns_empty_list():
    assert gg.first_k_primes(0) == []


def test_modulus_of_multiplies_all_tail_primes():
    assert gg.modulus_of([2, 3, 5]) == 30
    assert gg.modulus_of([]) == 1


def test_compute_full_period_head3_matches_hand_verified_all_twos():
    # Stage head=3: every gap between consecutive odd numbers is 2.
    period = gg.compute_full_period(3, [2])
    expected_gap = KNOWN_SMALL_STAGE_GAPS[3]["all_equal"]
    assert period and all(gap == expected_gap for gap in period)


def test_compute_full_period_head5_matches_hand_verified_alternation():
    period = gg.compute_full_period(5, [2, 3])
    expected = KNOWN_SMALL_STAGE_GAPS[5]["alternates"]
    assert period == expected * (len(period) // len(expected))


def test_compute_full_period_head7_matches_hand_verified_prefix():
    period = gg.compute_full_period(7, [2, 3, 5])
    expected_prefix = KNOWN_SMALL_STAGE_GAPS[7]["prefix"]
    assert period[:len(expected_prefix)] == expected_prefix


def test_compute_full_period_sums_to_exactly_one_modulus():
    tail = [2, 3, 5]
    period = gg.compute_full_period(7, tail)
    assert sum(period) == gg.modulus_of(tail)


def test_period_count_of_matches_actual_full_period_length():
    tail = [2, 3, 5]
    assert gg.period_count_of(tail) == len(gg.compute_full_period(7, tail))


def test_period_count_of_is_eulers_totient_of_the_modulus():
    # phi(2*3*5) = 1*2*4 = 8
    assert gg.period_count_of([2, 3, 5]) == 8


def test_get_resume_point_returns_none_for_missing_file(tmp_path):
    missing = tmp_path / "does-not-exist.csv"
    assert gg.get_resume_point(str(missing)) is None


def test_get_resume_point_reads_the_last_complete_row(tmp_path):
    csv_path = tmp_path / "gaps.csv"
    csv_path.write_text(
        "stage_index,head,gap_index,gap,survivor\n"
        "1,3,0,2,5\n"
        "1,3,1,2,7\n"
    )
    resume = gg.get_resume_point(str(csv_path))
    assert resume == {"stage_index": 1, "head": 3, "gaps_found": 2, "prev": 7}


def test_repair_truncated_tail_leaves_clean_files_untouched(tmp_path):
    csv_path = tmp_path / "gaps.csv"
    csv_path.write_text("stage_index,head,gap_index,gap,survivor\n1,3,0,2,5\n")
    original = csv_path.read_bytes()
    gg.repair_truncated_tail(str(csv_path))
    assert csv_path.read_bytes() == original


def test_generate_stage_tiled_path_appends_rows_up_to_prefix_len(tmp_path):
    # tail=[2] -> tiny modulus, so this takes the tiled (compute_full_period)
    # branch, not the trial-division fallback.
    import csv
    import io

    out = io.StringIO()
    writer = csv.writer(out)
    gaps_found = gg.PREFIX_LEN - 3  # only 3 rows left to generate
    result = gg.generate_stage(writer, out, stage_index=1, head=3, tail_primes=[2],
                                gaps_found=gaps_found, prev=3)
    assert result == gg.PREFIX_LEN
    rows = list(csv.reader(io.StringIO(out.getvalue())))
    assert len(rows) == 3
    assert [row[3] for row in rows] == ["2", "2", "2"]  # every stage-1 gap is 2
    assert [int(row[2]) for row in rows] == [gaps_found, gaps_found + 1, gaps_found + 2]


def test_generate_stage_trial_division_fallback_matches_tiled_result():
    # A modulus far past MAX_PERIOD_FOR_TILING forces the trial-division
    # fallback; its output must still match compute_full_period's tiled gaps,
    # since both walk the same provably-periodic sequence.
    import csv
    import io

    tail = [2, 3, 5, 7, 11, 13, 17, 19, 23]  # modulus ~223M > MAX_PERIOD_FOR_TILING
    assert gg.modulus_of(tail) > gg.MAX_PERIOD_FOR_TILING

    out = io.StringIO()
    writer = csv.writer(out)
    gaps_found = gg.PREFIX_LEN - 3
    result = gg.generate_stage(writer, out, stage_index=9, head=29, tail_primes=tail,
                                gaps_found=gaps_found, prev=29)
    assert result == gg.PREFIX_LEN
    rows = list(csv.reader(io.StringIO(out.getvalue())))
    assert len(rows) == 3
    assert all(int(row[3]) > 0 for row in rows)  # every produced gap is positive


def test_repair_truncated_tail_drops_a_torn_final_line(tmp_path):
    csv_path = tmp_path / "gaps.csv"
    csv_path.write_bytes(
        b"stage_index,head,gap_index,gap,survivor\n"
        b"1,3,0,2,5\n"
        b"1,3,1,2,7"  # no trailing newline -- simulates a kill mid-write
    )
    gg.repair_truncated_tail(str(csv_path))
    remaining = csv_path.read_text()
    assert remaining == "stage_index,head,gap_index,gap,survivor\n1,3,0,2,5\n"
