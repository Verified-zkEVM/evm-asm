#!/usr/bin/env python3
"""Generate tracked multi-drop body-completeness KAT fixtures (lljmj).

Class: drop ALL body transactions AND body withdrawals while re-pinning
header commitments (tx_root via rehash, gas_used/receipts_root/bloom to
empty-body-consistent values) while RETAINING original BAL + state_root +
witness. Extreme of the body-op-justification family (pnq91 + lukr5 combo).

Reference must reject (succ=0). Guest false-accepts until the body-op
justification fix lands (bead evm-asm-lljmj; folds into pnq91/evm-asm3
44/45 skip-list work).

Primary exploit:
  multi_drop_all_tx_and_body_wd_body_consistent
    empty transactions + empty withdrawals + body-consistent gas/receipts/bloom
    + rehashed block_hash; BAL/state_root retained from original body effects.

Source EEST fixture (v0.6.2, has body withdrawals + >=1 tx + BAL):
  blockchain_tests/for_amsterdam/amsterdam/
  eip7928_block_level_access_lists/block_access_lists/
  bal_gas_limit_boundary.json

Also emits body_wd_drop_repinned (lukr5-class, same source) as exploit bundle.

Usage (from repository root):

    EEST_FIXTURES_DIR=/path/to/tests-zkevm@v0.6.2/fixtures/fixtures \\
      uv run --directory execution-specs --quiet python3 \\
      scripts/kat/make_body_multi_drop_kat.py

Writes:
  fixtures/kat/body-multi-drop/body_multi_drop_control.json
  fixtures/kat/body-multi-drop/body_multi_drop_primary.json
  fixtures/kat/body-multi-drop/body_multi_drop_exploits.json
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
    "eip7928_block_level_access_lists/block_access_lists/"
    "bal_gas_limit_boundary.json"
)

REPO = Path(__file__).resolve().parents[2]
OUT_DIR = REPO / "fixtures" / "kat" / "body-multi-drop"


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
            p = inp.new_payload_request.execution_payload
            if not p.withdrawals:
                continue
            if len(p.transactions) < 1:
                continue
            return blob
    raise ValueError(f"no valid wd+tx fixture in {path}")


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


def body_consistent(inp, txs, public_keys, withdrawals):
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
    out = apply_body(block_env=block_env, transactions=txs, withdrawals=withdrawals)
    gas_used = max(out.block_gas_used, out.block_state_gas_used)
    return gas_used, root(out.receipts_trie), logs_bloom(out.block_logs)


def mutations(base: Bytes) -> dict[str, Bytes]:
    inp = deserialize_stateless_input(base)
    payload = inp.new_payload_request.execution_payload
    txs = payload.transactions
    pks = inp.public_keys
    wds = payload.withdrawals
    assert wds, "need body withdrawals"
    assert len(txs) >= 1, len(txs)
    assert len(pks) == len(txs), (len(pks), len(txs))

    # lukr5-class: drop body withdrawals only, rehash, retain BAL/state
    body_wd_drop = with_payload(inp, replace(payload, withdrawals=()))

    # lljmj primary: drop ALL txs + ALL body withdrawals, body-consistent header
    gas0, rr0, bloom0 = body_consistent(inp, (), (), ())
    multi_empty = with_payload(
        replace(inp, public_keys=()),
        replace(
            payload,
            transactions=(),
            withdrawals=(),
            gas_used=gas0,
            receipts_root=rr0,
            logs_bloom=bloom0,
        ),
    )

    # partial multi-drop: keep first tx only + drop withdrawals (if n>=2)
    partials: dict[str, Bytes] = {}
    if len(txs) >= 2:
        gas_p, rr_p, bloom_p = body_consistent(inp, txs[:1], pks[:1], ())
        partials["partial_keep_first_tx_drop_wd_body_consistent"] = with_payload(
            replace(inp, public_keys=pks[:1]),
            replace(
                payload,
                transactions=txs[:1],
                withdrawals=(),
                gas_used=gas_p,
                receipts_root=rr_p,
                logs_bloom=bloom_p,
            ),
        )
    else:
        # n=1: drop only tx keep withdrawals body-consistent (pnq91-class on this src)
        gas1, rr1, bloom1 = body_consistent(inp, (), (), wds)
        partials["tx_drop_all_keep_wd_body_consistent"] = with_payload(
            replace(inp, public_keys=()),
            replace(
                payload,
                transactions=(),
                gas_used=gas1,
                receipts_root=rr1,
                logs_bloom=bloom1,
            ),
        )

    # empty body without body-consistent re-pin (gas still N-tx) — should also reject
    multi_empty_gas_stale = with_payload(
        replace(inp, public_keys=()),
        replace(payload, transactions=(), withdrawals=()),
    )

    return {
        "control_honest": base,
        "multi_drop_all_tx_and_body_wd_body_consistent": multi_empty,
        "body_wd_drop_repinned": body_wd_drop,
        "multi_drop_all_tx_and_body_wd_stale_gas": multi_empty_gas_stale,
        **partials,
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

    primary_name = "multi_drop_all_tx_and_body_wd_body_consistent"
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
    (args.out_dir / "body_multi_drop_control.json").write_text(
        json.dumps(
            case_doc(
                "tests/kat_body_multi_drop/"
                "body_multi_drop_control[fork_Amsterdam-blockchain_test]",
                [block_entry("control_honest", control_blob, control_out)],
            ),
            indent=2,
        )
        + "\n"
    )
    (args.out_dir / "body_multi_drop_primary.json").write_text(
        json.dumps(
            case_doc(
                "tests/kat_body_multi_drop/"
                "body_multi_drop_primary[fork_Amsterdam-blockchain_test]",
                [block_entry(primary_name, primary_blob, primary_out)],
            ),
            indent=2,
        )
        + "\n"
    )
    (args.out_dir / "body_multi_drop_exploits.json").write_text(
        json.dumps(
            case_doc(
                "tests/kat_body_multi_drop/"
                "body_multi_drop_exploits[fork_Amsterdam-blockchain_test]",
                exploit_blocks,
            ),
            indent=2,
        )
        + "\n"
    )
    print(f"wrote control + primary + {len(exploit_blocks)} exploits to {args.out_dir}")
    print("bead: evm-asm-lljmj (red until body-op justification fix lands)")


if __name__ == "__main__":
    main()
