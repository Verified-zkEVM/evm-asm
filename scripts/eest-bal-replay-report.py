#!/usr/bin/env python3
"""Report BAL replay dimensions for generated EEST stateless inputs.

Run after scripts/codegen-eest-stateless-check.sh has produced
gen-out/eest-run/manifest.tsv.

Recommended:
  uv run --directory execution-specs --quiet python3 \
    ../scripts/eest-bal-replay-report.py --details --filter withdrawal_requests

After an EEST harness run, restrict the report to completed failures/errors:
  uv run --directory execution-specs --quiet python3 \
    ../scripts/eest-bal-replay-report.py --failures-only --details

Model a proposed `block_state_root` witness cap:
  uv run --directory execution-specs --quiet python3 \
    ../scripts/eest-bal-replay-report.py --failures-only --bsr-cap 65536

Model a proposed BAL row cap as well:
  uv run --directory execution-specs --quiet python3 \
    ../scripts/eest-bal-replay-report.py --failures-only \
      --bsr-cap 262144 --bsr-bal-cap 1024
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def add_execution_specs_to_path(root: Path) -> None:
    src = root / "execution-specs" / "src"
    if src.is_dir():
        sys.path.insert(0, str(src))


def unpack_zisk_input(path: Path) -> bytes:
    data = path.read_bytes()
    if len(data) < 8:
        raise ValueError("input shorter than zisk length prefix")
    n = int.from_bytes(data[:8], "little")
    blob = data[8 : 8 + n]
    if len(blob) != n:
        raise ValueError(f"input truncated: want {n} bytes, have {len(blob)}")
    return blob


def count_storage_writes(account_changes) -> int:
    return sum(len(slot.changes) for slot in account_changes.storage_changes)


def is_changed(account_changes) -> bool:
    return (
        bool(account_changes.storage_changes)
        or bool(account_changes.balance_changes)
        or bool(account_changes.nonce_changes)
        or bool(account_changes.code_changes)
    )


def decode_bal(input_path: Path):
    from ethereum.forks.amsterdam.block_access_lists import (  # type: ignore
        BlockAccessList,
    )
    from ethereum.forks.amsterdam.stateless_guest import (  # type: ignore
        deserialize_stateless_input,
    )
    from ethereum_rlp import rlp  # type: ignore

    blob = unpack_zisk_input(input_path)
    stateless_input = deserialize_stateless_input(blob)
    payload = stateless_input.new_payload_request.execution_payload
    bal = rlp.decode_to(BlockAccessList, payload.block_access_list)
    return stateless_input, payload, bal


MODELED_SYSTEM_ADDRESSES = {
    "0000f90827f1c53a10cb7a02335b175320002935",
    "000f3df6d732807ef1319fb7b8bb8522d0beac02",
}
WITHDRAWAL_REQUEST_ADDRESS = "00000961ef480eb55e80d19ad83579a64c007002"
BLOCK_STATE_ROOT_WITNESS_CAP = 32768
BLOCK_STATE_ROOT_BAL_CAP = 512


def summarize(
    input_path: Path,
    *,
    bsr_cap: int,
    bsr_bal_cap: int,
) -> tuple[dict[str, int], list[dict[str, str]]]:
    stateless_input, payload, bal = decode_bal(input_path)
    summary = {
        "input_len": input_path.stat().st_size - 8,
        "bal_bytes": len(payload.block_access_list),
        "bal_rows": len(bal),
        "over_bsr_bal_cap": 0,
        "readonly_rows": 0,
        "changed_rows": 0,
        "modeled_system_changed": 0,
        "withdrawal_request_changed": 0,
        "other_changed": 0,
        "storage_slots": 0,
        "storage_writes": 0,
        "storage_reads": 0,
        "balance_changes": 0,
        "nonce_changes": 0,
        "code_changes": 0,
        "state_nodes": len(stateless_input.witness.state),
        "state_witness_bytes": sum(4 + len(node) for node in stateless_input.witness.state),
        "state_max_bytes": max((len(node) for node in stateless_input.witness.state), default=0),
        "over_bsr_cap": 0,
        "codes": len(stateless_input.witness.codes),
        "code_witness_bytes": sum(4 + len(code) for code in stateless_input.witness.codes),
        "code_max_bytes": max((len(code) for code in stateless_input.witness.codes), default=0),
        "headers": len(stateless_input.witness.headers),
        "headers_witness_bytes": sum(4 + len(header) for header in stateless_input.witness.headers),
        "header_max_bytes": max((len(header) for header in stateless_input.witness.headers), default=0),
        "txs": len(payload.transactions),
    }
    summary["over_bsr_cap"] = int(summary["state_witness_bytes"] > bsr_cap)
    summary["over_bsr_bal_cap"] = int(summary["bal_rows"] > bsr_bal_cap)
    details: list[dict[str, str]] = []

    for row, account_changes in enumerate(bal):
        address = bytes(account_changes.address).hex()
        changed = is_changed(account_changes)
        if not changed:
            summary["readonly_rows"] += 1
            continue

        storage_slots = len(account_changes.storage_changes)
        storage_writes = count_storage_writes(account_changes)
        storage_reads = len(account_changes.storage_reads)
        balance_changes = len(account_changes.balance_changes)
        nonce_changes = len(account_changes.nonce_changes)
        code_changes = len(account_changes.code_changes)
        modeled_system = address in MODELED_SYSTEM_ADDRESSES
        withdrawal_request = address == WITHDRAWAL_REQUEST_ADDRESS

        summary["changed_rows"] += 1
        summary["storage_slots"] += storage_slots
        summary["storage_writes"] += storage_writes
        summary["storage_reads"] += storage_reads
        summary["balance_changes"] += balance_changes
        summary["nonce_changes"] += nonce_changes
        summary["code_changes"] += code_changes
        if modeled_system:
            summary["modeled_system_changed"] += 1
        elif withdrawal_request:
            summary["withdrawal_request_changed"] += 1
        else:
            summary["other_changed"] += 1

        details.append(
            {
                "row": str(row),
                "address": address,
                "modeled_system": str(int(modeled_system)),
                "withdrawal_request": str(int(withdrawal_request)),
                "storage_slots": str(storage_slots),
                "storage_writes": str(storage_writes),
                "storage_reads": str(storage_reads),
                "balance_changes": str(balance_changes),
                "nonce_changes": str(nonce_changes),
                "code_changes": str(code_changes),
            }
        )

    return summary, details


def result_is_failure(
    results_dir: Path,
    label: str,
    expected_hex: str,
) -> bool:
    result = results_dir / f"{label}.result.tsv"
    if not result.is_file():
        return False
    status, actual = result.read_text().rstrip("\n").split("\t", 1)
    if status != "OK":
        return True
    return actual[:210] != expected_hex[:210]


def main() -> int:
    root = repo_root()
    add_execution_specs_to_path(root)

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=root / "gen-out" / "eest-run" / "manifest.tsv",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=None,
        help="directory containing *.result.tsv (default: manifest parent)",
    )
    parser.add_argument(
        "--filter",
        default="",
        help="only include manifest rows whose label or fixture path contains this text",
    )
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument(
        "--details",
        action="store_true",
        help="print one extra row per changed BAL account",
    )
    parser.add_argument(
        "--failures-only",
        action="store_true",
        help="only include completed harness ERROR or non-full-match cases",
    )
    parser.add_argument(
        "--bsr-cap",
        type=int,
        default=BLOCK_STATE_ROOT_WITNESS_CAP,
        help="block_state_root witness cap used for over_bsr_cap",
    )
    parser.add_argument(
        "--bsr-bal-cap",
        type=int,
        default=BLOCK_STATE_ROOT_BAL_CAP,
        help="block_state_root BAL row cap used for over_bsr_bal_cap",
    )
    args = parser.parse_args()

    if args.limit < 0:
        parser.error("--limit must be nonnegative")
    if args.bsr_cap < 0:
        parser.error("--bsr-cap must be nonnegative")
    if args.bsr_bal_cap < 0:
        parser.error("--bsr-bal-cap must be nonnegative")
    if not args.manifest.is_file():
        raise SystemExit(f"manifest not found: {args.manifest}")
    results_dir = args.results_dir or args.manifest.parent

    summary_columns = [
        "input_len",
        "bal_bytes",
        "bal_rows",
        "over_bsr_bal_cap",
        "readonly_rows",
        "changed_rows",
        "modeled_system_changed",
        "withdrawal_request_changed",
        "other_changed",
        "storage_slots",
        "storage_writes",
        "storage_reads",
        "balance_changes",
        "nonce_changes",
        "code_changes",
        "state_nodes",
        "state_witness_bytes",
        "state_max_bytes",
        "over_bsr_cap",
        "codes",
        "code_witness_bytes",
        "code_max_bytes",
        "headers",
        "headers_witness_bytes",
        "header_max_bytes",
        "txs",
    ]
    detail_columns = [
        "row",
        "address",
        "modeled_system",
        "withdrawal_request",
        "storage_slots",
        "storage_writes",
        "storage_reads",
        "balance_changes",
        "nonce_changes",
        "code_changes",
    ]
    metric_columns = [
        "kind",
        "label",
        *summary_columns,
        "row",
        "address",
        "modeled_system",
        "withdrawal_request",
        "row_storage_slots",
        "row_storage_writes",
        "row_storage_reads",
        "row_balance_changes",
        "row_nonce_changes",
        "row_code_changes",
        "fixture",
    ]
    print("\t".join(metric_columns))

    printed = 0
    with args.manifest.open() as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) == 6:
                label, input_file, expected_hex, _succ_bit, _input_len, relpath = parts
            elif len(parts) == 7:
                label, input_file, expected_hex, _succ_bit, _input_len, _gas_limit, relpath = parts
            else:
                raise SystemExit(f"bad manifest row with {len(parts)} columns: {line!r}")
            if args.filter and args.filter not in label and args.filter not in relpath:
                continue
            if args.failures_only and not result_is_failure(
                results_dir, label, expected_hex
            ):
                continue

            summary, details = summarize(
                Path(input_file),
                bsr_cap=args.bsr_cap,
                bsr_bal_cap=args.bsr_bal_cap,
            )
            print(
                "\t".join(
                    [
                        "summary",
                        label,
                        *[str(summary[column]) for column in summary_columns],
                        *[""] * len(detail_columns),
                        relpath,
                    ]
                )
            )
            if args.details:
                for detail in details:
                    print(
                        "\t".join(
                            [
                                "detail",
                                label,
                                *[""] * len(summary_columns),
                                *[detail[column] for column in detail_columns],
                                relpath,
                            ]
                        )
                    )

            printed += 1
            if args.limit and printed >= args.limit:
                break
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
