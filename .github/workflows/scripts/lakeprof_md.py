#!/usr/bin/env python3
"""Render a lakeprof top-N JSON file as a markdown table.

Input shape (from lakeprof_topn.py):

    {"top_modules": [{"name": "...", "dur_seconds": 12.34}, ...]}

Output (stdout): a GitHub-flavored markdown table

    | rank | module | seconds |
    |------|--------|---------|
    | 1    | ...    | 12.34   |
    ...

If `top_modules` is empty, prints a single-line note instead of a table.
Stdlib only.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--in", dest="in_path", required=True,
        help="Path to lakeprof.topn.json",
    )
    args = parser.parse_args(argv)

    in_path = Path(args.in_path)
    if not in_path.is_file():
        print(f"_lakeprof: input not found ({in_path})_")
        return 0  # markdown should not break the run

    try:
        with in_path.open("r", encoding="utf-8") as f:
            doc = json.load(f)
    except json.JSONDecodeError as exc:
        print(f"_lakeprof: malformed input — {exc}_")
        return 0

    rows = doc.get("top_modules") or []
    if not rows:
        print("_lakeprof: no module timings recorded._")
        return 0

    print()
    print("| rank | module | seconds |")
    print("|------|--------|---------|")
    for i, row in enumerate(rows, start=1):
        name = str(row.get("name", "")).replace("|", r"\|")
        dur = row.get("dur_seconds", 0.0)
        try:
            dur_str = f"{float(dur):.2f}"
        except (TypeError, ValueError):
            dur_str = str(dur)
        print(f"| {i} | `{name}` | {dur_str} |")
    return 0


if __name__ == "__main__":
    sys.exit(main())
