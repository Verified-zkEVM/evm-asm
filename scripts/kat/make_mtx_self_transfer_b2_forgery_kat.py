#!/usr/bin/env python3
"""Materialize the tracked multi-tx self-transfer B2 false-accept KAT.

The fixture is deliberately a fully pinned forged stateless input.  It was
made from a two-transaction block containing a nonzero self-transfer by
claiming the pre-fix B2 running balance (which incorrectly subtracted value)
and then re-pinning the state root, receipts root, bloom, and payload hash.
Execution-specs rejects it.  A guest must reject it too.

The script writes the packed ziskemu input from the tracked JSON fixture.  It
is useful for local guest checks without relying on the transient diagnostic
ELF that was used to read the pre-fix B2 running value.
"""

from __future__ import annotations

import argparse
import json
import struct
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
FIXTURE = REPO / "fixtures/kat/mtx-self-transfer-b2/self_transfer_b2_forgery.json"
CASE = "tests/kat_mtx_self_transfer_b2/forge[fork_Amsterdam-blockchain_test]"


def frame(blob: bytes) -> bytes:
    return struct.pack("<Q", len(blob)) + blob + b"\0" * ((-8 - len(blob)) % 8)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path, nargs="?", default=Path("/tmp/mtx_self_transfer_b2_forgery.bin"))
    args = parser.parse_args()

    fixture = json.loads(FIXTURE.read_text())
    raw = fixture[CASE]["blocks"][0]["statelessInputBytes"]
    blob = bytes.fromhex(raw.removeprefix("0x"))
    args.output.write_bytes(frame(blob))
    print(f"wrote {args.output} ({len(blob)} byte stateless input)")


if __name__ == "__main__":
    main()
