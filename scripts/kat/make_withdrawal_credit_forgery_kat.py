#!/usr/bin/env python3
"""Construct the MTx withdrawal-credit false-accept probe from EEST 00565.

The canonical block gives ``c0f6…1992b`` 5 gwei after tx one and 15 gwei
after its withdrawal.  This generator changes the BAI-2 declared final back
to 5 gwei, re-pins the payload state root to the root derived by the guest
from that forged BAL, and re-hashes the payload.  Amsterdam execution-specs
must reject: EIP-4895 still applies the 10-gwei credit.  It is deliberately a
source-side generator, rather than an offset patch, so the SSZ and header
hash stay structurally valid.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import struct
from pathlib import Path

from ethereum.crypto.hash import Hash32, keccak256
from ethereum.forks.amsterdam.execution_engine.validation_helpers import _payload_header
from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input, run_stateless_guest
from ethereum.forks.amsterdam.stateless_host import serialize_stateless_input
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes32


RECIPIENT = bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b")
BAI_TWO = b"\x02"
FORGED_POST = (5_000_000_000).to_bytes(5, "big")


def framed_blob(path: Path) -> Bytes:
    framed = path.read_bytes()
    length = struct.unpack_from("<Q", framed)[0]
    return Bytes(framed[8 : 8 + length])


def forge(blob: Bytes, guest_root: str) -> Bytes:
    original = deserialize_stateless_input(blob)
    payload = original.new_payload_request.execution_payload
    bal = rlp.decode(payload.block_access_list)
    row = next(item for item in bal if bytes(item[0]) == RECIPIENT)
    balance_changes = row[3]
    change = next(item for item in balance_changes if bytes(item[0]) == BAI_TWO)
    assert bytes(change[1]) == (15_000_000_000).to_bytes(5, "big")
    change[1] = FORGED_POST
    payload = dataclasses.replace(
        payload,
        block_access_list=rlp.encode(bal),
        state_root=Bytes32(bytes.fromhex(guest_root.removeprefix("0x"))),
    )
    header = _payload_header(
        payload,
        original.new_payload_request.parent_beacon_block_root,
        original.new_payload_request.execution_requests,
    )
    payload = dataclasses.replace(payload, block_hash=Hash32(keccak256(rlp.encode(header))))
    return serialize_stateless_input(dataclasses.replace(
        original,
        new_payload_request=dataclasses.replace(original.new_payload_request, execution_payload=payload),
    ))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path, help="framed canonical EEST 00565 input")
    parser.add_argument("output", type=Path)
    parser.add_argument("--guest-root", required=True, help="guest sv_recomputed root")
    args = parser.parse_args()

    forged = forge(framed_blob(args.input), args.guest_root)
    result = bytes(run_stateless_guest(forged))
    assert result[32] == 0, "execution-specs must reject forged withdrawal credit"
    args.output.write_text(json.dumps({
        "tests/kat_mtx_withdrawal_credit/forge[fork_Amsterdam-blockchain_test]": {
            "network": "Amsterdam",
            "blocks": [{
                "statelessInputBytes": "0x" + bytes(forged).hex(),
                "statelessOutputBytes": "0x" + result.hex(),
            }],
        },
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
