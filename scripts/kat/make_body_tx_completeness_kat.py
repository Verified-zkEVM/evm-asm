#!/usr/bin/env python3
"""Generate tracked body-tx completeness KAT fixtures (pnq91).

Class: drop/mutate body transactions while re-pinning header commitments
(tx_root via rehash, and optionally gas_used/receipts_root/bloom to
body-consistent N-1 values) while RETAINING the original N-tx state_root +
BAL + witness. Reference must reject (succ=0). Guest false-accepts the
primary body-consistent variant until the body-tx justification fix lands
(bead evm-asm-pnq91; same body-op-justification family as lukr5/rgtkz/7rbp3).

Primary exploit:
  tx_drop_final_body_consistent_repinned
    drop final body tx (+ matching public key), re-execute remaining txs
    via apply_body to obtain body-consistent gas_used/receipts_root/bloom,
    rehash block_hash, retain N-tx BAL/state_root/witness.

Source EEST fixture (v0.6.2 multi-tx):
  blockchain_tests/for_amsterdam/amsterdam/
  eip8037_state_creation_gas_cost_increase/state_gas_set_code/
  multi_tx_block_auth_and_sstore.json

Usage (from repository root):

    EEST_FIXTURES_DIR=/path/to/tests-zkevm@v0.6.2/fixtures/fixtures \\
      uv run --directory execution-specs --quiet python3 \\
      scripts/kat/make_body_tx_completeness_kat.py

Writes:
  fixtures/kat/body-tx-completeness/body_tx_completeness_control.json
  fixtures/kat/body-tx-completeness/body_tx_completeness_primary.json
  fixtures/kat/body-tx-completeness/body_tx_completeness_exploits.json
"""

from __future__ import annotations

import argparse
import json
import os
from dataclasses import replace
from pathlib import Path

from ethereum.crypto.hash import keccak256
from ethereum.forks.amsterdam import vm
from ethereum.forks.amsterdam.block_access_lists import BlockAccessListBuilder
from ethereum.forks.amsterdam.bloom import logs_bloom
from ethereum.forks.amsterdam.execution_engine.validation_helpers import (
    _payload_header,
)
from ethereum.forks.amsterdam.fork import apply_body
from ethereum.forks.amsterdam.fork_types import Bloom
from ethereum.forks.amsterdam.state_tracker import BlockState
from ethereum.forks.amsterdam.stateless import (
    build_code_db,
    build_node_db,
    validate_headers,
)
from ethereum.forks.amsterdam.stateless_guest import (
    deserialize_stateless_input,
    run_stateless_guest,
)
from ethereum.forks.amsterdam.stateless_host import serialize_stateless_input
from ethereum.forks.amsterdam.witness_state import WitnessState
from ethereum.merkle_patricia_trie import Trie, root
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes
from ethereum_types.numeric import Uint

FIXTURE_REL = Path(
    "blockchain_tests/for_amsterdam/amsterdam/"
    "eip8037_state_creation_gas_cost_increase/state_gas_set_code/"
    "multi_tx_block_auth_and_sstore.json"
)

REPO = Path(__file__).resolve().parents[2]
OUT_DIR = REPO / "fixtures" / "kat" / "body-tx-completeness"


def fixture_path(fixtures_dir: Path) -> Path:
    return fixtures_dir / FIXTURE_REL


def first_valid(path: Path) -> Bytes:
    for case in json.loads(path.read_text()).values():
        for block in case.get("blocks", []):
            raw = block.get("statelessInputBytes")
            if raw is None:
                continue
            blob = Bytes(bytes.fromhex(raw.removeprefix("0x")))
            if bytes(run_stateless_guest(blob))[32] != 1:
                continue
            inp = deserialize_stateless_input(blob)
            n = len(inp.new_payload_request.execution_payload.transactions)
            if n >= 2:
                return blob
    raise ValueError(f"no multi-tx valid fixture in {path}")


def rehash(payload, parent_beacon_block_root, requests):
    header = _payload_header(payload, parent_beacon_block_root, requests)
    return replace(payload, block_hash=keccak256(rlp.encode(header)))


def with_payload(inp, payload, requests=None) -> Bytes:
    npr = inp.new_payload_request
    reqs = npr.execution_requests if requests is None else requests
    payload = rehash(payload, npr.parent_beacon_block_root, reqs)
    return serialize_stateless_input(
        replace(
            inp,
            new_payload_request=replace(
                npr, execution_payload=payload, execution_requests=reqs
            ),
        )
    )


def empty_receipts_root():
    return root(Trie(secured=False, default=None))


def body_consistent_header_fields(inp, txs, public_keys):
    """Re-execute txs against parent witness; return gas/receipts/bloom.

    Does NOT return state_root or BAL — those stay at the N-tx values for the FA.
    """
    payload = inp.new_payload_request.execution_payload
    witness = inp.witness
    decoded_headers, block_hashes = validate_headers(witness.headers)
    parent_header = decoded_headers[-1]
    pre_state = WitnessState(
        _node_db=build_node_db(witness.state),
        _state_root=parent_header.state_root,
        _code_db=build_code_db(witness.codes),
    )
    block_state = BlockState(pre_state=pre_state)
    block_env = vm.BlockEnvironment(
        chain_id=inp.chain_config.chain_id,
        state=block_state,
        block_gas_limit=payload.gas_limit,
        block_hashes=block_hashes,
        coinbase=payload.fee_recipient,
        number=payload.block_number,
        base_fee_per_gas=payload.base_fee_per_gas,
        time=payload.timestamp,
        prev_randao=payload.prev_randao,
        excess_blob_gas=payload.excess_blob_gas,
        parent_beacon_block_root=inp.new_payload_request.parent_beacon_block_root,
        block_access_list_builder=BlockAccessListBuilder(),
        slot_number=payload.slot_number,
        transaction_public_keys=public_keys,
    )
    out = apply_body(
        block_env=block_env,
        transactions=txs,
        withdrawals=payload.withdrawals,
    )
    gas_used = max(out.block_gas_used, out.block_state_gas_used)
    receipts_root = root(out.receipts_trie)
    bloom = logs_bloom(out.block_logs)
    return gas_used, receipts_root, bloom


def mutations(base: Bytes) -> dict[str, Bytes]:
    inp = deserialize_stateless_input(base)
    payload = inp.new_payload_request.execution_payload
    txs = payload.transactions
    assert len(txs) >= 2, len(txs)
    pks = inp.public_keys
    assert len(pks) == len(txs), (len(pks), len(txs))

    drop_one = with_payload(inp, replace(payload, transactions=txs[:-1]))
    drop_first = with_payload(inp, replace(payload, transactions=txs[1:]))
    drop_one_zero_gas = with_payload(
        inp,
        replace(
            payload,
            transactions=txs[:-1],
            gas_used=Uint(0),
            receipts_root=empty_receipts_root(),
            logs_bloom=Bloom(b"\x00" * 256),
        ),
    )

    gas_n1, receipts_n1, bloom_n1 = body_consistent_header_fields(
        inp, txs[:-1], pks[:-1]
    )
    drop_one_body_consistent = with_payload(
        replace(inp, public_keys=pks[:-1]),
        replace(
            payload,
            transactions=txs[:-1],
            gas_used=gas_n1,
            receipts_root=receipts_n1,
            logs_bloom=bloom_n1,
        ),
    )

    gas_drop_first, receipts_drop_first, bloom_drop_first = (
        body_consistent_header_fields(inp, txs[1:], pks[1:])
    )
    drop_first_body_consistent = with_payload(
        replace(inp, public_keys=pks[1:]),
        replace(
            payload,
            transactions=txs[1:],
            gas_used=gas_drop_first,
            receipts_root=receipts_drop_first,
            logs_bloom=bloom_drop_first,
        ),
    )

    last = bytes(txs[-1])
    if not last:
        raise ValueError("empty last tx")
    mutated = last[:-1] + bytes([(last[-1] ^ 0x01) & 0xFF])
    mutate_last = with_payload(
        inp, replace(payload, transactions=txs[:-1] + (Bytes(mutated),))
    )
    phantom = with_payload(inp, replace(payload, transactions=txs + (txs[-1],)))
    drop_all = with_payload(inp, replace(payload, transactions=()))
    drop_all_body_consistent = with_payload(
        replace(inp, public_keys=()),
        replace(
            payload,
            transactions=(),
            gas_used=Uint(0),
            receipts_root=empty_receipts_root(),
            logs_bloom=Bloom(b"\x00" * 256),
        ),
    )

    return {
        "control_honest": base,
        "tx_drop_final_body_consistent_repinned": drop_one_body_consistent,
        "tx_drop_first_body_consistent_repinned": drop_first_body_consistent,
        "tx_drop_final_zero_gas_receipts_repinned": drop_one_zero_gas,
        "tx_drop_all_body_consistent_repinned": drop_all_body_consistent,
        "tx_drop_final_root_repinned": drop_one,
        "tx_drop_first_root_repinned": drop_first,
        "tx_mutate_final_root_repinned": mutate_last,
        "tx_phantom_dup_final_root_repinned": phantom,
        "tx_drop_all_root_repinned": drop_all,
    }


def case_doc(case_name: str, blocks: list[dict]) -> dict:
    return {
        case_name: {
            "network": "Amsterdam",
            "blocks": blocks,
        }
    }


def block_entry(name: str, blob: Bytes, out: bytes) -> dict:
    return {
        "statelessInputBytes": "0x" + bytes(blob).hex(),
        "statelessOutputBytes": "0x" + out.hex(),
        "name": name,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--fixtures-dir",
        type=Path,
        default=Path(
            os.environ.get(
                "EEST_FIXTURES_DIR",
                "/tmp/evm-asm-u9gu8/gen-out/eest-fixtures/"
                "tests-zkevm@v0.6.2/fixtures/fixtures",
            )
        ),
    )
    ap.add_argument("--out-dir", type=Path, default=OUT_DIR)
    args = ap.parse_args()

    src = fixture_path(args.fixtures_dir)
    if not src.is_file():
        raise SystemExit(f"source fixture missing: {src}")

    muts = mutations(first_valid(src))
    control_blob = muts.pop("control_honest")
    control_out = bytes(run_stateless_guest(control_blob))
    assert control_out[32] == 1, "control must accept"

    primary_name = "tx_drop_final_body_consistent_repinned"
    primary_blob = muts[primary_name]
    primary_out = bytes(run_stateless_guest(primary_blob))
    assert primary_out[32] == 0, "primary must be ref-rejected"

    exploit_blocks = []
    for name, blob in muts.items():
        out = bytes(run_stateless_guest(blob))
        assert out[32] == 0, f"reference unexpectedly accepted {name}"
        exploit_blocks.append(block_entry(name, blob, out))
        print(f"{name}: ref succ={out[32]}")

    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "body_tx_completeness_control.json").write_text(
        json.dumps(
            case_doc(
                "tests/kat_body_tx_completeness/"
                "body_tx_completeness_control[fork_Amsterdam-blockchain_test]",
                [block_entry("control_honest", control_blob, control_out)],
            ),
            indent=2,
        )
        + "\n"
    )
    (args.out_dir / "body_tx_completeness_primary.json").write_text(
        json.dumps(
            case_doc(
                "tests/kat_body_tx_completeness/"
                "body_tx_completeness_primary[fork_Amsterdam-blockchain_test]",
                [block_entry(primary_name, primary_blob, primary_out)],
            ),
            indent=2,
        )
        + "\n"
    )
    (args.out_dir / "body_tx_completeness_exploits.json").write_text(
        json.dumps(
            case_doc(
                "tests/kat_body_tx_completeness/"
                "body_tx_completeness_exploits[fork_Amsterdam-blockchain_test]",
                exploit_blocks,
            ),
            indent=2,
        )
        + "\n"
    )
    print(f"wrote control + primary + {len(exploit_blocks)} exploits to {args.out_dir}")
    print("bead: evm-asm-pnq91 (red until body-tx justification fix lands)")


if __name__ == "__main__":
    main()
