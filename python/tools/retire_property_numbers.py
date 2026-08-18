"""One-off migration: retire bare "Property #N" references repo-wide.

Reads the N -> path mapping from Appendix B in gap-dynamics-v3.md (plus the
two manually-known #87/#88 entries), joins it against the short-name
registry in properties/sieve-sequence/README.md (path -> short name) to get
an N -> short name table, then rewrites every "Property #N" occurrence found
anywhere in the repo (markdown files only) using that short name instead.

Rules (see tickets/../missing plan for full rationale):
  1. Header lines: "## <n>. Property #M -- Title" -> "## <n>. Short Name"
  2. Markdown link text: "[Property #M]" -> "[Short Name]" (URL untouched)
  3. Possessive prose: "Property #M's" -> "the Short Name property's"
  4. Bare prose: "Property #M" -> "the Short Name property" (capitalized
     "The" if at the start of a line/sentence)
  5. Header lines with 2+ distinct numbers are NOT auto-rewritten -- printed
     as "HARD CASE" for manual rewording, since a blind multi-name
     substitution reads badly.
  6. Appendix table rows ("| #N | ... |") have their leading "#N" column
     dropped and their link text switched to the short name -- handled as a
     separate pass over the two known Appendix B files only.

Run: python3 scripts/retire_property_numbers.py [--apply]
Without --apply, prints a dry-run summary only.
"""

from __future__ import annotations

import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
APPENDIX_SOURCE = os.path.join(REPO, "articles/chapter6/gap-dynamics-v3.md")
REGISTRY_SOURCE = os.path.join(REPO, "properties/sieve-sequence/README.md")
APPENDIX_FILES = [
    os.path.join(REPO, "articles/chapter6/gap-dynamics-v2.md"),
    os.path.join(REPO, "articles/chapter6/gap-dynamics-v3.md"),
]

# Static N -> short name table. Originally derived by joining Appendix B
# (articles/chapter6/gap-dynamics-v3.md, N -> path) against the registry
# (properties/sieve-sequence/README.md, path -> short name) -- hardcoded here
# because the first application run already rewrote Appendix B itself (its
# "#N" column is gone by design, per Rule 5), so it can no longer be
# re-derived from that source on a second run.
NUMBER_TO_SHORTNAME: dict[int, str] = {
    1: "Global 2-Gap Count", 2: "Global 2-Gap Cluster Count", 3: "Batched 2-Gap Survival",
    4: "Copy-Index Filter Frequency", 5: "2-Gap Isolation", 6: "Accepted Local Strikes",
    7: "Local Survival Threshold", 8: "Safe-Window Certification", 9: "Reverse-Engineered Head Scenario",
    10: "Perfect Scenario Infinitude", 11: "Count-Forces-Survival Threshold", 12: "Rotation Invariance",
    13: "Absence Stability", 14: "Batched Discrepancy Boundary", 15: "Fixed-k Shot Spacing",
    16: "Pair Separation Premise", 17: "Local Count Shot-Capacity Premise", 18: "Seven-Layer Capacity Floor",
    19: "Close-Pair Matching Bound", 20: "Raw Close-Pair Attrition", 21: "Matching Attrition Bound",
    22: "Post-Filter-3 Harmful Capacity", 23: "Two-Class Collision Survival", 24: "Weighted Chain Survival",
    25: "Weighted Deletion Conservation", 26: "Pair Local Factor", 27: "Pair-Correlation Average",
    28: "Fourier Correlation Bound", 29: "Localized Fourier Boundary", 30: "Conductor-Decay Destruction",
    31: "Large-Sieve Budget Mismatch", 32: "First-Deletion Terminal Energy", 33: "Endpoint Excess-Imbalance Split",
    34: "Orthogonal Residue-Energy Split", 35: "Möbius Strike-Density Sum", 36: "Endpoint Discrepancy Contraction",
    37: "Weighted Error Composition", 38: "Strike-Error Quadratic Variation", 39: "Prime-Square Boundary Formula",
    40: "Harmless-Energy Pair Correlation", 41: "Harmless-Class Uniformity", 42: "Harmless Spectral Excess",
    43: "CRT Fiber Translation", 44: "Inverse-Phase Gram Matrix", 45: "Phase-Operator Norm Bound",
    46: "Conductor Phase-Block Bound", 47: "Ramanujan Cross-Conductor Geometry", 48: "Strike Divisor-Activation Kernel",
    49: "Strike CRT Lift-Index", 50: "Strike Summatory Remainder", 51: "Cross-Layer CRT Orthogonality",
    52: "Localized-Layer Gram Matrix", 53: "First-Deletion Variance Identity", 54: "Active Two-Class Variance",
    55: "First-Deletion Reindexing", 56: "Joint Capacity Envelope", 57: "Endpoint Capacity Insufficiency",
    58: "Sampling-Density Recombination", 59: "Pointwise Margin Insufficiency", 60: "Harmful-Residue Box Bound",
    61: "Sixfold-Capacity Energy Envelope", 62: "Sixfold Population-Ratio Threshold", 63: "Capacity Threshold Hierarchy",
    64: "Late-Layer Sixfold Floor", 65: "One-Layer Ellipse Non-Composition", 66: "Terminal Harmful-Excess Energy",
    67: "Integral Profile Attainment", 68: "Harmful-Excess Stability Decomposition", 69: "Capacity Minimizer Separation",
    70: "Harmful-Capacity Excess Envelope", 71: "Paired CRT Primorial Scale", 72: "Native-Period Hybrid Envelope",
    73: "Native-Period Capacity Overflow", 74: "Envelope Width Floor", 75: "Seven-Layer Density Floor",
    76: "Seven-Layer Overflow Forcing", 77: "Filter-Seven Cut Failure", 78: "Fixed Native Cut Failure",
    79: "Moving-Cut Block Loss", 80: "Incomplete-Block Bessel Bound", 81: "Capacity Stability Gap",
    82: "Filter-Seven Excess Bound", 83: "Copy-Block Excess Control", 84: "Divisor Local Factor",
    85: "Bilinear Character Obstruction", 86: "Cofactor Progression Discrepancy", 87: "Danger-Annulus Decomposition",
    88: "Filter Adversariality Score",
}


APPENDIX_ROW_RE = re.compile(r"^\| #(\d+) \| \[(.+?)\]\((.+?)\) \| (.+?) \|$", re.M)


def build_number_to_shortname() -> dict[int, str]:
    return dict(NUMBER_TO_SHORTNAME)


HEADER_RE = re.compile(r"^(#{1,6}\s+(?:\d+\.\s*)?)[Pp]ropert(?:y|ies) #(\d+)\s*(?:[—-]\s*)?(.*)$")
LINK_RE = re.compile(r"\[[Pp]ropert(?:y|ies) #(\d+)\]")
POSSESSIVE_RE = re.compile(r"[Pp]ropert(?:y|ies) #(\d+)'s")
BARE_RE = re.compile(r"[Pp]ropert(?:y|ies) #(\d+)")
# Only counts actual "Property #N" / "Properties #N" occurrences (any case)
# for the multi-number hard-case check -- a bare "#N" elsewhere in the line
# (e.g. a "candidate #12" reference, out of scope for this pass) must not
# trigger it.
PROPERTY_MENTION_RE = re.compile(r"[Pp]ropert(?:y|ies) #(\d+)")
# "Properties #75--#81" / "#75-#81" style ranges -- always a hard case, since
# a range implies several properties named in one place.
RANGE_RE = re.compile(r"#\d+\s*[-–—]{1,2}\s*#?\d+")
# The specific, regular sub-case "Propert(y|ies) #N--#M" IS safely automated:
# rewritten as "the properties from <first> through <last>", not flagged.
PROPERTY_RANGE_RE = re.compile(r"[Pp]ropert(?:y|ies) #(\d+)\s*[-–—]{1,2}\s*#?(\d+)")


def range_sub_factory(line: str, table: dict[int, str]):
    def range_sub(m: re.Match) -> str:
        n1, n2 = int(m.group(1)), int(m.group(2))
        s1, s2 = table.get(n1), table.get(n2)
        if s1 is None or s2 is None:
            return m.group(0)
        start = m.start()
        preceding = line[:start]
        at_sentence_start = (
            start == 0
            or preceding.rstrip().endswith((".", "!", "?"))
            or preceding.strip() == ""
        )
        article = "The" if at_sentence_start else "the"
        return f"{article} properties from {s1} through {s2}"

    return range_sub


def rewrite_line(line: str, table: dict[int, str], flagged: list[str]) -> str:
    # Handle the regular "Propert(y|ies) #N--#M" range sub-case first, so it
    # never trips the multi-number hard-case flag below.
    line = PROPERTY_RANGE_RE.sub(range_sub_factory(line, table), line)

    header_match = HEADER_RE.match(line)
    if header_match:
        numbers_in_line = set(int(n) for n in PROPERTY_MENTION_RE.findall(line))
        if len(numbers_in_line) > 1 or RANGE_RE.search(line):
            flagged.append(line.rstrip("\n"))
            return line
        prefix, num, rest = header_match.groups()
        short = table.get(int(num))
        if short is None:
            flagged.append(line.rstrip("\n"))
            return line
        rest = rest.strip()
        return f"{prefix}{rest if rest else short}\n" if line.endswith("\n") else f"{prefix}{rest if rest else short}"

    numbers_in_line = set(int(n) for n in PROPERTY_MENTION_RE.findall(line))
    if len(numbers_in_line) > 1 or (numbers_in_line and RANGE_RE.search(line)):
        flagged.append(line.rstrip("\n"))
        return line

    def link_sub(m: re.Match) -> str:
        n = int(m.group(1))
        short = table.get(n)
        return f"[{short}]" if short else m.group(0)

    def possessive_sub(m: re.Match) -> str:
        n = int(m.group(1))
        short = table.get(n)
        return f"the {short} property's" if short else m.group(0)

    def bare_sub(m: re.Match) -> str:
        n = int(m.group(1))
        short = table.get(n)
        if short is None:
            return m.group(0)
        start = m.start()
        preceding = line[:start]
        at_sentence_start = (
            start == 0
            or preceding.rstrip().endswith((".", "!", "?"))
            or preceding.strip() == ""
        )
        article = "The" if at_sentence_start else "the"
        return f"{article} {short} property"

    line = LINK_RE.sub(link_sub, line)
    line = POSSESSIVE_RE.sub(possessive_sub, line)
    line = BARE_RE.sub(bare_sub, line)
    return line


def rewrite_appendix_table(text: str, table_by_num: dict[int, str]) -> str:
    def row_sub(m: re.Match) -> str:
        n, _title, rel_path, extra = m.groups()
        short = table_by_num.get(int(n))
        if short is None:
            return m.group(0)
        return f"| [{short}]({rel_path}) | {extra} |"

    return APPENDIX_ROW_RE.sub(row_sub, text)


def find_candidate_files() -> list[str]:
    files = []
    for root, dirs, names in os.walk(REPO):
        for skip in (".git", ".zcode"):
            if skip in dirs:
                dirs.remove(skip)
        for name in names:
            if name.endswith(".md"):
                path = os.path.join(root, name)
                content = open(path, encoding="utf-8").read()
                if PROPERTY_MENTION_RE.search(content):
                    files.append(path)
    return files


def main() -> int:
    apply = "--apply" in sys.argv
    table = build_number_to_shortname()
    print(f"Built short-name table for {len(table)} properties.")

    files = find_candidate_files()
    print(f"Found {len(files)} files containing 'Property #'.")

    total_flagged: list[tuple[str, str]] = []
    for path in files:
        text = open(path, encoding="utf-8").read()
        is_appendix = path in APPENDIX_FILES
        if is_appendix:
            text = rewrite_appendix_table(text, table)

        flagged: list[str] = []
        lines = text.splitlines(keepends=True)
        new_lines = [rewrite_line(line, table, flagged) for line in lines]
        new_text = "".join(new_lines)

        for f in flagged:
            total_flagged.append((os.path.relpath(path, REPO), f))

        if new_text != text:
            rel = os.path.relpath(path, REPO)
            remaining = len(PROPERTY_MENTION_RE.findall(new_text))
            print(f"{'WRITE' if apply else 'DRY-RUN'} {rel}: rewritten, {remaining} 'Property #N' remain")
            if apply:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(new_text)

    if total_flagged:
        print(f"\n{len(total_flagged)} HARD CASES flagged for manual rewording:")
        for rel, line in total_flagged:
            print(f"  {rel}: {line}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
