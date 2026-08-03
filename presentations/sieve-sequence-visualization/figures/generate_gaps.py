"""Computes the first PREFIX_LEN gaps for each of NUM_STAGES sieve stages and
appends them to a CSV. The CSV is the *only* persisted state -- there is no
separate progress file that could drift out of sync with it.

Generation is strictly sequential: stage N+1 never starts until stage N has
written all PREFIX_LEN of its rows. So the very last line of the CSV fully
determines where to resume -- which stage was in progress, how many of its
gaps are already recorded (gap_index + 1), and the exact integer to continue
searching from (the `survivor` column, the actual value found for that gap).
Every earlier stage is therefore guaranteed complete, with no need to scan
or re-check them. Recovery is an O(1) read of the tail of the file, not an
O(rows generated so far) scan.

This means the process can be killed at any moment -- mid-stage, between
rows, whenever -- and rerunning always picks up from the last row it
actually managed to write, never recomputing finished work and never losing
more than the single row in flight. If that very last line was a torn
mid-write, it is truncated away entirely before anything else runs, so the
file always starts a fresh run from the end of its last complete row.

Stage k has head prime h_k; a value v > h_k survives iff it is not divisible
by any prime below h_k. The gap sequence is provably periodic with period M_k
= product of the primes below h_k (see articles/chapter6/sieve-sequence.md).
For small-head stages M_k is small enough to compute directly by sieving one
full period once, then tiling it -- far cheaper than continuing trial
division out to PREFIX_LEN, especially since those early, high-consumption-
ratio stages are exactly the bottleneck that limits how far lineage tracking
(e.g. gap_heatmap.py's age view) can trace forward before running out of
data. Large-head stages have an astronomically large M_k (primorial growth)
and fall back to the walk-forward trial-division approach, which stays cheap
regardless of how large M_k truly is.

Run: python3 generate_gaps.py
Output: ../../../data/sieve-sequence/first_gaps_per_seq.csv
"""

import csv
import os

DATA_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "data", "sieve-sequence")
CSV_PATH = os.path.join(DATA_DIR, "first_gaps_per_seq.csv")

NUM_STAGES = 200
PREFIX_LEN = 100000

# Above this, a stage's full period is too expensive to sieve directly, and
# trial division (via generate_stage's fallback loop) is used instead. Below
# it, tiling one exactly-computed period is far cheaper than walking that far
# via trial division. 15M covers stage heads up to 23 (period ~9.7M); the
# next stage (head=29, period ~223M) already falls outside it.
MAX_PERIOD_FOR_TILING = 15_000_000

CSV_HEADER = ["stage_index", "head", "gap_index", "gap", "survivor"]


def is_prime(n: int) -> bool:
    """Trial division primality test, only ever called on small n (building
    the initial list of stage heads), so no sieve is needed here."""
    if n < 2:
        return False
    for d in range(2, int(n**0.5) + 1):
        if n % d == 0:
            return False
    return True


def first_k_primes(k: int):
    """The first k primes in increasing order, found by trial division from 2 up."""
    primes = []
    n = 2
    while len(primes) < k:
        if is_prime(n):
            primes.append(n)
        n += 1
    return primes


def read_tail_lines(path: str, num_lines: int = 3):
    """Reads the last `num_lines` complete lines of a file without scanning
    it from the start, by seeking backward from the end in growing chunks."""
    with open(path, "rb") as file_handle:
        file_handle.seek(0, os.SEEK_END)
        file_size = file_handle.tell()
        block_size = 4096
        data = b""
        while True:
            read_size = min(block_size, file_size)
            file_handle.seek(file_size - read_size)
            data = file_handle.read(read_size)
            if data.count(b"\n") > num_lines or read_size >= file_size:
                break
            block_size *= 2
    lines = [line.decode() for line in data.splitlines() if line.strip()]
    return lines[-num_lines:]


def get_resume_point(csv_path: str):
    """Returns {"stage_index", "head", "gaps_found", "prev"} describing the
    furthest stage with any rows written, or None if there is no data yet.
    Tries the last tail line first, then the ones before it, in case the
    very last line was a torn mid-write."""
    if not os.path.exists(csv_path) or os.path.getsize(csv_path) == 0:
        return None
    for line in reversed(read_tail_lines(csv_path)):
        parts = line.strip().split(",")
        if len(parts) != 5:
            continue
        try:
            stage_index, head, gap_index, _gap, survivor = (int(p) for p in parts)
        except ValueError:
            continue
        return {"stage_index": stage_index, "head": head, "gaps_found": gap_index + 1, "prev": survivor}
    return None


def modulus_of(tail_primes) -> int:
    """Product of tail_primes -- the period length M of the stage's gap cycle."""
    modulus = 1
    for p in tail_primes:
        modulus *= p
    return modulus


def compute_full_period(head: int, tail_primes):
    """Exact one-period gap cycle: every integer in [head, head+M) coprime to
    every prime in tail_primes, as consecutive differences, where M =
    modulus_of(tail_primes). The trial-division walk in generate_stage is
    provably periodic with exactly this period, so tiling it is identical to
    continuing the walk -- just far cheaper once M is small enough to
    enumerate directly. (Matches the independent verification against known
    S1-S4 values done earlier in this project's history.)"""
    modulus = modulus_of(tail_primes)
    survivors = [candidate for candidate in range(head, head + modulus)
                 if all(candidate % p != 0 for p in tail_primes)]
    gaps = [survivors[i + 1] - survivors[i] for i in range(len(survivors) - 1)]
    gaps.append(head + modulus - survivors[-1])
    return gaps


def period_count_of(tail_primes) -> int:
    """Exact count of survivors in one full period, with no sieving needed:
    since the modulus M = product(tail_primes) is squarefree by construction
    (distinct primes), Euler's totient formula gives phi(M) = product(p-1)
    exactly."""
    count = 1
    for p in tail_primes:
        count *= (p - 1)
    return count


def generate_stage(writer, csv_file, stage_index, head, tail_primes, gaps_found, prev):
    """Appends gaps [gaps_found, PREFIX_LEN) for this stage to `writer`,
    flushing `csv_file` after every row so a kill mid-stage loses at most one
    row. Uses the exact tiled period when it's cheap enough (see
    MAX_PERIOD_FOR_TILING), otherwise falls back to walking forward by trial
    division. Returns the final gaps_found (always PREFIX_LEN on success)."""
    modulus = modulus_of(tail_primes)
    # Tiling only pays off once PREFIX_LEN needs more than one full period --
    # sieving the whole modulus to serve a request smaller than one period is
    # strictly more work than just walking forward the needed amount.
    if modulus <= MAX_PERIOD_FOR_TILING and period_count_of(tail_primes) <= PREFIX_LEN:
        period = compute_full_period(head, tail_primes)
        period_len = len(period)
        while gaps_found < PREFIX_LEN:
            gap = period[gaps_found % period_len]
            candidate = prev + gap
            writer.writerow([stage_index, head, gaps_found, gap, candidate])
            csv_file.flush()
            prev = candidate
            gaps_found += 1
        return gaps_found

    candidate = prev + 1
    while gaps_found < PREFIX_LEN:
        if all(candidate % p != 0 for p in tail_primes):
            gap = candidate - prev
            writer.writerow([stage_index, head, gaps_found, gap, candidate])
            csv_file.flush()
            prev = candidate
            gaps_found += 1
        candidate += 1
    return gaps_found


def repair_truncated_tail(path: str) -> None:
    """If a prior run was killed mid-write, the file may end in a torn,
    incomplete line. Leaving it in place is dangerous: it's a well-formed-looking
    but incomplete CSV row (e.g. a missing trailing field), which get_resume_point
    is careful enough to skip, but a simpler downstream reader (like
    gap_heatmap.py, which only reads a couple of columns) could half-parse it as
    a phantom extra gap. So rather than just closing it off, drop it entirely --
    truncate the file back to the end of its last complete, newline-terminated
    line."""
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        return
    with open(path, "rb") as file_handle:
        file_handle.seek(0, os.SEEK_END)
        size = file_handle.tell()
        file_handle.seek(-1, os.SEEK_END)
        if file_handle.read(1) == b"\n":
            return  # already ends cleanly, nothing to repair

        block_size = 4096
        pos = size
        cut_at = 0
        while pos > 0:
            step = min(block_size, pos)
            pos -= step
            file_handle.seek(pos)
            chunk = file_handle.read(step)
            nl = chunk.rfind(b"\n")
            if nl != -1:
                cut_at = pos + nl + 1
                break
            block_size *= 2

    with open(path, "r+b") as file_handle:
        file_handle.truncate(cut_at)


def main() -> None:
    """Resume (or start) generation of all NUM_STAGES stages' first PREFIX_LEN
    gaps each, appending rows to CSV_PATH as described in the module docstring."""
    os.makedirs(DATA_DIR, exist_ok=True)
    repair_truncated_tail(CSV_PATH)
    resume = get_resume_point(CSV_PATH)
    write_header = not os.path.exists(CSV_PATH) or os.path.getsize(CSV_PATH) == 0

    start_stage_index = 1
    resume_here = None
    if resume:
        if resume["gaps_found"] >= PREFIX_LEN:
            start_stage_index = resume["stage_index"] + 1
        else:
            start_stage_index = resume["stage_index"]
            resume_here = resume

    heads = first_k_primes(NUM_STAGES + 1)[1:]  # skip 2; stages start at head=3
    tail = [2]  # every stage head is odd (>=3), so 2 always belongs in its filter set
    with open(CSV_PATH, "a", newline="") as csv_file:
        writer = csv.writer(csv_file)
        if write_header:
            writer.writerow(CSV_HEADER)
            csv_file.flush()

        for stage_index, head in enumerate(heads, start=1):
            if stage_index < start_stage_index:
                tail.append(head)
                continue

            if stage_index == start_stage_index and resume_here:
                if resume_here["head"] != head:
                    raise SystemExit(
                        f"resume mismatch: CSV says stage {stage_index} head={resume_here['head']}, "
                        f"but the configured stage sequence expects head={head}. "
                        "NUM_STAGES or the prime sequence must have changed since first_gaps_per_seq.csv was written."
                    )
                gaps_found, prev = resume_here["gaps_found"], resume_here["prev"]
                print(f"stage {stage_index}/{len(heads)} head={head} resuming from gap {gaps_found}")
            else:
                gaps_found, prev = 0, head

            gaps_found = generate_stage(writer, csv_file, stage_index, head, tail, gaps_found, prev)
            tail.append(head)
            print(f"stage {stage_index}/{len(heads)} head={head} done ({gaps_found} gaps)")

    print(f"all {len(heads)} stages present in {CSV_PATH}")


if __name__ == "__main__":
    main()
