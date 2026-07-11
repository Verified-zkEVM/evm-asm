#!/usr/bin/env python3
"""Report transaction-count histograms for cached EEST zkevm stateless fixtures.

The report decodes each fixture block's ``statelessInputBytes`` through the
local execution-specs Amsterdam stateless input decoder, then counts
``new_payload_request.execution_payload.transactions``. The fixture JSON side
channels are used only for discovery and labels.

Typical use from the repo root:

    uv run --directory execution-specs --quiet python3 ../scripts/eest-stateless-tx-count-histogram.py

That command uses the local execution-specs checkout and does not require
network once its dependencies are available.
"""
from __future__ import annotations

import argparse
import heapq
import json
import os
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

DEFAULT_THRESHOLDS = (16, 64, 256, 1024)

@dataclass(frozen=True)
class BlockRow:
    relpath: str
    test_name: str
    block_index: int
    input_bytes: bytes

@dataclass(frozen=True)
class CountRow:
    tx_count: int
    relpath: str
    test_name: str
    block_index: int

def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]

def default_fixture_tag() -> str:
    env = os.environ.get("EEST_FIXTURE_TAG")
    if env:
        return env
    tag_file = repo_root() / "scripts" / "eest-fixture-tag.txt"
    try:
        tag = tag_file.read_text().strip()
    except OSError:
        tag = "tests-zkevm@v0.6.0"
    return tag or "tests-zkevm@v0.6.0"

def default_fixtures_dir(tag: str) -> Path:
    env = os.environ.get("EEST_FIXTURES_DIR")
    if env:
        return Path(env)
    return repo_root() / "gen-out" / "eest-fixtures" / tag / "fixtures" / "fixtures"

def parse_hex_bytes(s: str) -> bytes:
    return bytes.fromhex(s[2:] if s.startswith("0x") else s)

def iter_stateless_blocks(fixtures_dir: Path) -> Iterable[BlockRow]:
    json_files = sorted(p for p in fixtures_dir.rglob("*.json") if ".meta" not in p.parts)
    for fixture_path in json_files:
        relpath = str(fixture_path.relative_to(fixtures_dir))
        try:
            doc = json.loads(fixture_path.read_text())
        except (json.JSONDecodeError, OSError) as exc:
            print(f"warn: cannot parse {fixture_path}: {exc}", file=sys.stderr)
            continue
        if not isinstance(doc, dict):
            continue
        for test_name, tc in doc.items():
            blocks = tc.get("blocks") if isinstance(tc, dict) else None
            if not isinstance(blocks, list):
                continue
            for block_index, block in enumerate(blocks):
                if not isinstance(block, dict):
                    continue
                sib = block.get("statelessInputBytes")
                if not sib:
                    continue
                try:
                    input_bytes = parse_hex_bytes(sib)
                except ValueError as exc:
                    print(f"warn: bad statelessInputBytes in {relpath} {test_name}#b{block_index}: {exc}", file=sys.stderr)
                    continue
                yield BlockRow(relpath, test_name, block_index, input_bytes)

def load_tx_counter():
    try:
        from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
        from ethereum_types.bytes import Bytes
    except ImportError as exc:
        raise RuntimeError(
            "execution-specs dependencies are unavailable. Run with e.g. "
            "`uv run --directory execution-specs --quiet python3 "
            "../scripts/eest-stateless-tx-count-histogram.py`, or install the "
            "local execution-specs environment first."
        ) from exc

    def tx_count(blob: bytes) -> int:
        stateless_input = deserialize_stateless_input(Bytes(blob))
        return len(stateless_input.new_payload_request.execution_payload.transactions)

    return tx_count

def parse_thresholds(raw: str) -> tuple[int, ...]:
    if not raw:
        return ()
    vals: list[int] = []
    for part in raw.split(","):
        part = part.strip()
        if not part:
            continue
        try:
            val = int(part, 0)
        except ValueError as exc:
            raise argparse.ArgumentTypeError(f"invalid threshold {part!r}") from exc
        if val < 0:
            raise argparse.ArgumentTypeError("thresholds must be nonnegative")
        vals.append(val)
    return tuple(sorted(set(vals)))

def short_name(test_name: str) -> str:
    return test_name.split("::")[-1] if "::" in test_name else test_name

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", default=default_fixture_tag(), help="fixture tag under gen-out/eest-fixtures")
    parser.add_argument("--fixtures-dir", type=Path, default=None, help="fixture root containing blockchain_tests")
    parser.add_argument("--filter", default="", help="keep rows whose relpath or test name contains this substring")
    parser.add_argument("--skip", type=int, default=0, help="skip first N selected stateless blocks")
    parser.add_argument("--limit", type=int, default=0, help="cap selected stateless blocks after --skip; 0 means no cap")
    parser.add_argument("--thresholds", type=parse_thresholds, default=DEFAULT_THRESHOLDS, help="comma-separated N values for counts of tx_count > N")
    parser.add_argument("--top", type=int, default=10, help="number of highest-tx blocks to print")
    parser.add_argument("--tsv", action="store_true", help="emit machine-readable TSV instead of the human report")
    args = parser.parse_args()

    if args.skip < 0:
        parser.error("--skip must be nonnegative")
    if args.limit < 0:
        parser.error("--limit must be nonnegative")
    if args.top < 0:
        parser.error("--top must be nonnegative")

    fixtures_dir = args.fixtures_dir or default_fixtures_dir(args.tag)
    if not fixtures_dir.is_dir():
        print(f"error: fixtures directory not found: {fixtures_dir}", file=sys.stderr)
        return 1

    try:
        decode_tx_count = load_tx_counter()
    except RuntimeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    selected_seen = 0
    decoded = 0
    fixture_files: set[str] = set()
    hist: Counter[int] = Counter()
    above: Counter[int] = Counter({t: 0 for t in args.thresholds})
    top_heap: list[tuple[int, int, CountRow]] = []

    for row in iter_stateless_blocks(fixtures_dir):
        if args.filter and args.filter not in row.relpath and args.filter not in row.test_name:
            continue
        if selected_seen < args.skip:
            selected_seen += 1
            continue
        selected_seen += 1
        if args.limit and decoded >= args.limit:
            break
        try:
            count = decode_tx_count(row.input_bytes)
        except Exception as exc:
            print(f"error: execution-specs failed to decode {row.relpath} {row.test_name}#b{row.block_index}: {exc}", file=sys.stderr)
            return 1
        fixture_files.add(row.relpath)
        hist[count] += 1
        for threshold in args.thresholds:
            if count > threshold:
                above[threshold] += 1
        count_row = CountRow(count, row.relpath, row.test_name, row.block_index)
        if args.top:
            item = (count, decoded, count_row)
            if len(top_heap) < args.top:
                heapq.heappush(top_heap, item)
            elif item[0] > top_heap[0][0]:
                heapq.heapreplace(top_heap, item)
        decoded += 1

    max_count = max(hist) if hist else 0
    top_rows = [item[2] for item in sorted(top_heap, key=lambda x: (-x[0], x[1]))]

    if args.tsv:
        print("metric	value")
        print(f"fixtures_dir	{fixtures_dir}")
        print(f"fixture_files	{len(fixture_files)}")
        print(f"stateless_blocks	{decoded}")
        print(f"max_tx_count	{max_count}")
        for threshold in args.thresholds:
            print(f"tx_count_gt_{threshold}	{above[threshold]}")
        print("histogram_tx_count	blocks")
        for count in sorted(hist):
            print(f"{count}	{hist[count]}")
        print("top_tx_count	relpath	block_index	test")
        for row in top_rows:
            print(f"{row.tx_count}	{row.relpath}	{row.block_index}	{short_name(row.test_name)}")
        return 0

    print(f"fixtures_dir: {fixtures_dir}")
    print(f"fixture files with selected stateless blocks: {len(fixture_files)}")
    print(f"stateless blocks decoded: {decoded}")
    print(f"max tx_count: {max_count}")
    for threshold in args.thresholds:
        print(f"tx_count > {threshold}: {above[threshold]}")
    print()
    print("Histogram (tx_count -> stateless blocks):")
    for count in sorted(hist):
        print(f"  {count:5d}  {hist[count]}")
    if top_rows:
        print()
        print(f"Top {len(top_rows)} blocks by tx_count:")
        for row in top_rows:
            print(f"  {row.tx_count:5d}  {row.relpath}  block={row.block_index}  test={short_name(row.test_name)}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
