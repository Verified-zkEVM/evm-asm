#!/usr/bin/env python3
"""Generate the 03099 recipient-storage materialization false-accept guard.

The source is the canonical v0.6.2 03099 framed input.  The generated block
omits the recipient's BAL storage changes and re-pins the payload state root
and block hash to the root computed by the pre-fix guest.  execution-specs
rejects this forged block; a guest must never accept it merely because its
recipient runtime arena failed to materialize.
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path, help="framed canonical 03099 ziskemu input")
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--guest-root",
        required=True,
        help="pre-fix guest-computed state root, without 0x",
    )
    args = parser.parse_args()

    framed = args.input.read_bytes()
    length = struct.unpack_from("<Q", framed)[0]
    original = deserialize_stateless_input(Bytes(framed[8 : 8 + length]))
    payload = original.new_payload_request.execution_payload
    bal = rlp.decode(payload.block_access_list)
    recipient = bytes(rlp.decode(payload.transactions[0])[3])
    target = next(item for item in bal if bytes(item[0]) == recipient)
    assert target[1], "03099 must carry recipient storage changes before forging"
    target[1] = []
    payload = dataclasses.replace(payload, block_access_list=rlp.encode(bal))
    payload = dataclasses.replace(payload, state_root=Bytes32(bytes.fromhex(args.guest_root)))
    header = _payload_header(
        payload,
        original.new_payload_request.parent_beacon_block_root,
        original.new_payload_request.execution_requests,
    )
    payload = dataclasses.replace(payload, block_hash=Hash32(keccak256(rlp.encode(header))))
    forged = serialize_stateless_input(dataclasses.replace(
        original,
        new_payload_request=dataclasses.replace(original.new_payload_request, execution_payload=payload),
    ))
    result = bytes(run_stateless_guest(forged))
    assert result[32] == 0, "execution-specs must reject the forged storage omission"
    args.output.write_text(json.dumps({
        "tests/kat_recipient_storage_arena_fail_closed/forge[fork_Amsterdam-blockchain_test]": {
            "network": "Amsterdam",
            "blocks": [{
                "statelessInputBytes": "0x" + bytes(forged).hex(),
                "statelessOutputBytes": "0x" + result.hex(),
            }],
        },
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
