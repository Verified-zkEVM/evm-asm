#!/usr/bin/env python3
"""Inspect EIP-7934 zkevm fixtures for block/stateless-input equivalence.

Run from the repo root via execution-specs dependencies, for example:

    uv run --directory execution-specs --quiet python3 \
        ../scripts/eest-eip7934-input-equivalence.py \
        ../gen-out/eest-fixtures/zkevm@v0.4.0/fixtures/fixtures/blockchain_tests/for_amsterdam/osaka/eip7934_block_rlp_limit/max_block_rlp_size/block_at_rlp_size_limit_boundary.json

The check intentionally does not feed raw fixture RLP to the guest. It reports
whether the structured stateless input carries the same block-size-relevant data
that execution-specs validates with len(rlp.encode(block)).
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
from ethereum_rlp import rlp


def _hex_bytes(s: str) -> bytes:
    return bytes.fromhex(s[2:] if s.startswith("0x") else s)


def iter_stateless_blocks(path: Path):
    doc = json.loads(path.read_text())
    for test_name, test_case in doc.items():
        blocks = test_case.get("blocks") if isinstance(test_case, dict) else None
        if not isinstance(blocks, list):
            continue
        short = test_name.split("::")[-1] if "::" in test_name else test_name
        for block_index, block in enumerate(blocks):
            if not isinstance(block, dict):
                continue
            sib = block.get("statelessInputBytes")
            raw_rlp = block.get("rlp")
            if sib and raw_rlp:
                yield short, block_index, _hex_bytes(sib), _hex_bytes(raw_rlp)


def inspect(path: Path) -> int:
    rows = []
    for (
        test_name,
        block_index,
        stateless_input,
        block_rlp,
    ) in iter_stateless_blocks(path):
        decoded_input = deserialize_stateless_input(stateless_input)
        payload = decoded_input.new_payload_request.execution_payload
        decoded_block = rlp.decode(block_rlp)
        header = decoded_block[0]
        header_extra_data = bytes(header[12])
        rows.append(
            (
                test_name,
                block_index,
                hashlib.sha256(stateless_input).hexdigest()[:16],
                len(payload.extra_data),
                len(header_extra_data),
                len(payload.transactions),
                sum(len(tx) for tx in payload.transactions),
                len(payload.withdrawals),
                len(block_rlp),
            )
        )

    print(
        "test	block	stateless_sha16	payload_extra_len	"
        "fixture_header_extra_len	tx_count	tx_bytes	withdrawals	block_rlp_len"
    )
    for row in rows:
        print("	".join(str(x) for x in row))

    mismatches = [row for row in rows if row[3] != row[4]]
    if mismatches:
        print(f"mismatch: {len(mismatches)} block(s) differ in extra_data length")
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", type=Path)
    args = parser.parse_args()
    return inspect(args.fixture)


if __name__ == "__main__":
    raise SystemExit(main())
