#!/usr/bin/env python3
"""Construct the B2.3 sender-under-debit false-accept regression input.

The script first raises the final BAL balance of the shared sender in the
two-transaction fixture.  Replaying the staged blob through the verdict-v2
probe yields the forged BAL-derived state root; pass that root with ``--root``
to produce the final framed input.  execution-specs rejects the result, and a
guest must reject it through B2.3 (failure code 57).
"""

from __future__ import annotations

import argparse
import dataclasses
import struct
from pathlib import Path

from ethereum.crypto.hash import Hash32, keccak256
from ethereum.forks.amsterdam.execution_engine.validation_helpers import _payload_header
from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
from ethereum.forks.amsterdam.stateless_host import serialize_stateless_input
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes32


DEFAULT_INPUT = Path("/tmp/fc668/in/00220_test_multiple_transfers_same_block_fork_Amsterdam-blockchain_test__b0.input")
SENDER = bytes.fromhex("f6c3a9edc1afa0ad5b720e4d42e1437c43d3b3ff")


def frame(blob: bytes) -> bytes:
    return struct.pack("<Q", len(blob)) + blob + b"\0" * ((-8 - len(blob)) % 8)


def rehash(inp, payload):
    request = inp.new_payload_request
    header = _payload_header(payload, request.parent_beacon_block_root, request.execution_requests)
    payload = dataclasses.replace(payload, block_hash=Hash32(keccak256(rlp.encode(header))))
    return serialize_stateless_input(dataclasses.replace(inp, new_payload_request=dataclasses.replace(request, execution_payload=payload)))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--stage", type=Path, default=Path("/tmp/sender_balance_forge_stage.input"))
    parser.add_argument("--stage-framed", type=Path, default=Path("/tmp/sender_balance_forge_stage.bin"))
    parser.add_argument("--output", type=Path, default=Path("/tmp/sender_balance_forge.bin"))
    parser.add_argument("--root", help="BAL-derived state root from the staged v2 replay")
    args = parser.parse_args()

    if args.root:
        inp = deserialize_stateless_input(Bytes(args.stage.read_bytes()))
        payload = dataclasses.replace(inp.new_payload_request.execution_payload, state_root=Bytes32(bytes.fromhex(args.root.removeprefix("0x"))))
        args.output.write_bytes(frame(rehash(inp, payload)))
        return

    framed = args.input.read_bytes()
    inp = deserialize_stateless_input(Bytes(framed[8 : 8 + int.from_bytes(framed[:8], "little")]))
    payload = inp.new_payload_request.execution_payload
    bal = rlp.decode(payload.block_access_list)
    row = next(item for item in bal if bytes(item[0]) == SENDER)
    assert len(row[3]) == 2, row[3]
    old = int.from_bytes(bytes(row[3][-1][1]), "big")
    row[3][-1][1] = (old + 1).to_bytes(len(row[3][-1][1]), "big")
    args.stage.write_bytes(rehash(inp, dataclasses.replace(payload, block_access_list=Bytes(rlp.encode(bal)))))
    args.stage_framed.write_bytes(frame(args.stage.read_bytes()))
    print(f"forged sender {SENDER.hex()} final balance {old}->{old + 1}")


if __name__ == "__main__":
    main()
