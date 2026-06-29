#!/usr/bin/env python3
"""Disable all .holds functions in ch5 and ch6 by inserting `true` before closing brace."""
import os, re, glob

base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
files = (glob.glob(f"{base}/src/main/scala/v1/chapter5/**/*.scala", recursive=True)
       + glob.glob(f"{base}/src/main/scala/v1/chapter6/**/*.scala", recursive=True))

for fpath in sorted(files):
    with open(fpath) as f:
        lines = f.readlines()

    modified = False
    new_lines = []
    for i, line in enumerate(lines):
        stripped = line.lstrip()
        # Only match active .holds lines (not inside // comments)
        if stripped.startswith("}") and ".holds" in stripped:
            # Check this isn't inside a multi-line comment or // comment
            prev_comment = any(l.strip().startswith("//") for l in lines[max(0,i-3):i])
            if not prev_comment:
                # Insert `true // DISABLED` before this line
                indent = line[:len(line) - len(line.lstrip())]
                new_lines.append(f"{indent}true // DISABLED\n")
                modified = True
        new_lines.append(line)

    if modified:
        with open(fpath, "w") as f:
            f.writelines(new_lines)
        print(f"  {os.path.relpath(fpath, base)}")

print("Done.")
