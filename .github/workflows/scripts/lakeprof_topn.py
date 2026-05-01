#!/usr/bin/env python3
"""Extract top-N slowest modules from a lakeprof chrome-trace JSON file.

Input: a chrome-trace JSON document produced by `lakeprof report
--save-chrome-trace`. Either a top-level array of `trace_event` records,
or an object with a `traceEvents` field (Chrome's "object" form). Each
record has `name`, `ph`, `dur` (microseconds), and friends.

Output: a JSON document of the shape

    {
      "top_modules": [
        {"name": "EvmAsm.Evm64.DivMod.Spec.CallAddback",
         "dur_seconds": 87.31},
        ...
      ]
    }

`top_modules` is sorted by `dur_seconds` descending, capped at N entries
(default 20 via --n). `dur_seconds` is the raw lakeprof microsecond
duration divided by 1_000_000 and rounded to two decimals (per design
note docs/949-lakeprof-design.md).

Stdlib only.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def load_events(path: Path) -> list[dict]:
    """Load chrome-trace events from a file.

    Accepts either an array (the most common lakeprof shape) or an
    object with a ``traceEvents`` field. Anything else is an error.
    """
    with path.open("r", encoding="utf-8") as f:
        doc = json.load(f)
    if isinstance(doc, list):
        return doc
    if isinstance(doc, dict) and isinstance(doc.get("traceEvents"), list):
        return doc["traceEvents"]
    raise ValueError(
        f"unexpected chrome-trace shape in {path}: "
        f"top-level must be a list or an object with 'traceEvents'"
    )


def top_modules(events: list[dict], n: int) -> list[dict]:
    """Return the top-N (name, dur_seconds) records, ph='X' only."""
    rows: list[tuple[str, float]] = []
    for ev in events:
        # Only "complete" events carry a duration; other phases (B/E,
        # M = metadata, etc.) don't.
        if ev.get("ph") != "X":
            continue
        name = ev.get("name")
        dur_us = ev.get("dur")
        if not isinstance(name, str) or not isinstance(dur_us, (int, float)):
            continue
        rows.append((name, float(dur_us) / 1_000_000.0))
    # Sort by duration descending, ties broken by name ascending for
    # determinism across reruns.
    rows.sort(key=lambda r: (-r[1], r[0]))
    out: list[dict] = []
    for name, dur_s in rows[: max(0, n)]:
        out.append({"name": name, "dur_seconds": round(dur_s, 2)})
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--in", dest="in_path", required=True,
        help="Path to lakeprof chrome-trace JSON (lakeprof.trace.json)",
    )
    parser.add_argument(
        "--out", dest="out_path", required=True,
        help="Path to write top-N JSON (lakeprof.topn.json)",
    )
    parser.add_argument(
        "--n", dest="n", type=int, default=20,
        help="Number of top entries to keep (default: 20)",
    )
    args = parser.parse_args(argv)

    in_path = Path(args.in_path)
    if not in_path.is_file():
        print(f"error: input not found: {in_path}", file=sys.stderr)
        return 2
    try:
        events = load_events(in_path)
    except (ValueError, json.JSONDecodeError) as exc:
        print(f"error: failed to parse {in_path}: {exc}", file=sys.stderr)
        return 2

    top = top_modules(events, args.n)

    out_path = Path(args.out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        json.dump({"top_modules": top}, f, indent=2, sort_keys=True)
        f.write("\n")
    print(
        f"lakeprof_topn: wrote {len(top)} entries to {out_path}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
