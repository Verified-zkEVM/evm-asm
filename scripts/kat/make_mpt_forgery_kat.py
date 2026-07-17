#!/usr/bin/env python3
"""Generate the tracked v0.6.2 full-guest MPT/BAL forgery KAT fixtures.

The control fixture is a canonical expected-valid Amsterdam block.  The five
exploit blocks alter only trust-bearing bytes in its schema-prefixed
``statelessInputBytes`` and record the strict execution-specs result:

* a witness-state child-hash byte;
* an invalid RLP envelope on that witness node;
* an unused valid RLP leaf at the ByteList[1025] boundary, with all SSZ offsets
  repaired;
* a BAL account post-balance; and
* a BAL storage post-value.
* a substituted root-referenced child node, a code preimage, and a BAL nonce.

All five are protocol-invalid and must produce ``successful_validation = 0``.
The files this writes are consumed directly by the KAT runner; the original
EEST fixture is only the reproducible source for the canonical control input.

Usage (from the repository root):

    EEST_FIXTURES_DIR=/path/to/tests-zkevm@v0.6.2/fixtures/fixtures \\
      uv run --directory execution-specs --quiet python3 \\
      scripts/kat/make_mpt_forgery_kat.py
"""

from __future__ import annotations

import argparse
import json
import os
import struct
from pathlib import Path

import rlp
from ethereum.forks.amsterdam.stateless_guest import (
    deserialize_stateless_input,
    run_stateless_guest,
)
from ethereum_types.bytes import Bytes


FIXTURE_REL = Path(
    "blockchain_tests/for_amsterdam/amsterdam/"
    "eip2780_reduce_intrinsic_tx_gas/authorization_charges/"
    "account_write_authority_is_recipient.json"
)


def pack(blob: bytes) -> bytearray:
    """Return ziskemu host framing; the KAT stores only the guest-visible blob."""
    framed = bytearray(struct.pack("<Q", len(blob)) + blob)
    framed.extend(b"\0" * ((-len(framed)) % 8))
    return framed


def blob_of(framed: bytes) -> bytes:
    length = struct.unpack_from("<Q", framed)[0]
    return framed[8 : 8 + length]


def spec_output(blob: bytes) -> bytes:
    return bytes(run_stateless_guest(Bytes(blob)))


def select_valid_blob(path: Path) -> bytes:
    doc = json.loads(path.read_text())
    for test_case in doc.values():
        for block in test_case.get("blocks", []):
            raw = block.get("statelessInputBytes")
            if raw is None:
                continue
            blob = bytes.fromhex(raw.removeprefix("0x"))
            if spec_output(blob)[32] == 1:
                return blob
    raise ValueError("canonical source fixture contains no expected-valid stateless block")


def mutations(control: bytes) -> dict[str, bytes]:
    """Produce the five fixed-size/offset-repaired adversarial inputs."""
    base = pack(control)
    # Host file offset 8 starts the schema prefix; V2's SSZ base skips 2 bytes.
    s0 = 10
    u32 = lambda data, pos: struct.unpack_from("<I", data, pos)[0]
    witness = s0 + u32(base, s0 + 4)
    state = witness + u32(base, witness)
    first = u32(base, state)
    count = first // 4
    assert count >= 2 and first == 4 * count
    node = state + first
    assert base[node : node + 2] == b"\xf8\x51", "canonical fixture layout changed"

    out: dict[str, bytes] = {}
    forged_node = bytearray(base)
    forged_node[node + 13] ^= 1
    out["forged_witness_node"] = blob_of(forged_node)

    malformed = bytearray(base)
    malformed[node + 1] = 0x52
    out["malformed_witness_node"] = blob_of(malformed)

    # The root has hash references to nodes 3 and 4.  Substitute the latter's
    # valid bytes at node 3 without changing any offsets: the parent still
    # commits to node 3's old hash, so lookup must fail rather than use bytes
    # merely because they are a well-formed witness entry.
    child3 = state + u32(base, state + 12)
    child3_end = state + u32(base, state + 16)
    child4 = child3_end
    child4_end = state + u32(base, state + 20)
    assert child3_end - child3 == child4_end - child4
    substituted_child = bytearray(base)
    substituted_child[child3:child3_end] = base[child4:child4_end]
    out["substituted_witness_child"] = blob_of(substituted_child)

    # Mutate a non-empty code witness byte.  The selected canonical fixture
    # executes this code; its account leaf commits to the old code hash.
    codes_off = u32(base, witness + 4)
    headers_off = u32(base, witness + 8)
    codes = witness + codes_off
    code_count = u32(base, codes) // 4
    assert code_count >= 2
    code1 = codes + u32(base, codes + 4)
    code1_end = codes + (u32(base, codes + 8) if code_count > 2 else headers_off - codes_off)
    assert code1_end - code1 >= 2
    forged_code = bytearray(base)
    forged_code[code1 + 1] ^= 1
    out["forged_witness_code_preimage"] = blob_of(forged_code)

    decoded = deserialize_stateless_input(Bytes(control))
    bal = bytes(decoded.new_payload_request.execution_payload.block_access_list)
    bal_start = control.find(bal)
    assert bal_start >= 0 and control.find(bal, bal_start + 1) < 0

    def forge_bal(name: str, needle: bytes, before: int, after: int) -> None:
        framed = bytearray(base)
        pos = bal.find(needle)
        assert pos >= 0 and bal.find(needle, pos + 1) < 0, f"{name} layout changed"
        at = 8 + bal_start + pos + len(needle) - 1
        assert framed[at] == before
        framed[at] = after
        out[name] = blob_of(framed)

    forge_bal("forged_bal_post_balance", bytes.fromhex("c3c20165"), 0x65, 0x64)
    forge_bal("forged_bal_storage_value", bytes.fromhex("c5c4808203e8"), 0xE8, 0xE9)
    # Account 9 has balance change [1, 0x65], nonce change [1, 1], and a code
    # change. Locate the nonce inside its individual RLP record, not globally.
    accounts = rlp.decode(bal)
    account9 = rlp.encode(accounts[9])
    account9_off = bal.find(account9)
    assert account9_off >= 0 and bal.find(account9, account9_off + 1) < 0
    nonce = bytes.fromhex("c3c20101")
    nonce_off = account9.find(nonce)
    assert nonce_off >= 0 and account9.find(nonce, nonce_off + 1) < 0
    forged_nonce = bytearray(base)
    nonce_pos = 8 + bal_start + account9_off + nonce_off + len(nonce) - 1
    assert forged_nonce[nonce_pos] == 1
    forged_nonce[nonce_pos] = 2
    out["forged_bal_nonce"] = blob_of(forged_nonce)
    out["overlong_witness_node"] = with_unused_state_leaf(control, 1025)
    return out


def with_unused_state_leaf(control: bytes, size: int) -> bytes:
    """Append an unused valid RLP leaf of exactly ``size`` to witness.state."""
    base = pack(control)
    s0 = 10
    u32 = lambda data, pos: struct.unpack_from("<I", data, pos)[0]
    witness = s0 + u32(base, s0 + 4)
    state_off = u32(base, witness)
    codes_off = u32(base, witness + 4)
    state = witness + state_off
    end = witness + codes_off
    count = u32(base, state) // 4
    offsets = [u32(base, state + 4 * i) for i in range(count)]
    nodes = [
        bytes(base[state + start : state + (offsets[i + 1] if i + 1 < count else codes_off - state_off)])
        for i, start in enumerate(offsets)
    ]
    # A canonical leaf: compact HP terminator path 0x20 plus a zero value.
    # At the boundary sizes below, RLP overhead is exactly seven bytes.
    leaf = rlp.encode([b"\x20", b"\0" * (size - 7)])
    assert len(leaf) == size
    nodes.append(leaf)
    pos = 4 * len(nodes)
    new_state = bytearray()
    for item in nodes:
        new_state += struct.pack("<I", pos)
        pos += len(item)
    new_state += b"".join(nodes)
    delta = len(new_state) - (end - state)
    framed = bytearray(base)
    framed[state:end] = new_state
    for pos in (witness + 4, witness + 8):
        struct.pack_into("<I", framed, pos, u32(base, pos) + delta)
    witness_off = u32(base, s0 + 4)
    for pos in (s0, s0 + 4, s0 + 8, s0 + 12):
        old = u32(base, pos)
        if old > witness_off:
            struct.pack_into("<I", framed, pos, old + delta)
    payload_len = struct.unpack_from("<Q", framed)[0] + delta
    struct.pack_into("<Q", framed, 0, payload_len)
    del framed[8 + payload_len :]
    framed.extend(b"\0" * ((-len(framed)) % 8))
    return blob_of(framed)


def record(name: str, blob: bytes, expected: int) -> dict[str, str]:
    output = spec_output(blob)
    assert output[32] == expected, f"execution-specs unexpectedly accepted/rejected {name}"
    return {
        "statelessInputBytes": "0x" + blob.hex(),
        "statelessOutputBytes": "0x" + output.hex(),
    }


def fixture(name: str, blocks: list[dict[str, str]]) -> dict[str, object]:
    return {
        f"tests/kat_mpt_forgery/{name}[fork_Amsterdam-blockchain_test]": {
            "network": "Amsterdam",
            "blocks": blocks,
        }
    }


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    default_fixtures = root / "gen-out/eest-fixtures/tests-zkevm@v0.6.2/fixtures/fixtures"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fixtures-dir",
        type=Path,
        default=Path(os.environ.get("EEST_FIXTURES_DIR", default_fixtures)),
    )
    parser.add_argument(
        "--out-dir", type=Path, default=root / "fixtures/kat/mpt-forgery"
    )
    args = parser.parse_args()

    control = select_valid_blob(args.fixtures_dir / FIXTURE_REL)
    forged = mutations(control)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    controls = [
        record("control", control, 1),
        record("boundary_1023", with_unused_state_leaf(control, 1023), 1),
        record("boundary_1024", with_unused_state_leaf(control, 1024), 1),
    ]
    (args.out_dir / "mpt_forgery_control.json").write_text(
        json.dumps(fixture("mpt_forgery_control", controls), indent=2) + "\n"
    )
    exploits = [record(name, blob, 0) for name, blob in forged.items()]
    (args.out_dir / "mpt_forgery_exploits.json").write_text(
        json.dumps(fixture("mpt_forgery_exploits", exploits), indent=2) + "\n"
    )
    print(f"wrote {len(controls)} accepted boundary controls + {len(exploits)} forged KAT blocks to {args.out_dir}")


if __name__ == "__main__":
    main()
