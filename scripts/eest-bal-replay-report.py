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
BLOCK_STATE_ROOT_WITNESS_CAP = 524288
BLOCK_STATE_ROOT_BAL_CAP = 100000
MPT_WITNESS_INDEX_CAP = BLOCK_STATE_ROOT_WITNESS_CAP // 4
# Amsterdam's unconditional transaction floor is TX_BASE=12,000, so the
# 200M-gas full-tx bound is floor(200,000,000 / 12,000) = 16,666.  Keep the
# report constants in lockstep with BlockVerdictParams.lean; otherwise a
# capacity report silently describes the retired fixture-era limits.
BV_MTX_ARENA_TX_CAP = 16666
BMV_FULL_TX_CAPACITY = 16666
BV_MTX_COMMITTED_CANONICAL_CAPACITY = 16384
BV_RECEIPT_RECORD_CAPACITY = BMV_FULL_TX_CAPACITY
BV_RESOURCE_BLOCK_GAS_LIMIT = 200_000_000
BV_BLOCK_LOG_MIN_GAS = 375
BV_BLOCK_LOG_DATA_BYTE_GAS = 8
BV_BLOCK_LOG_DESC_FULL_TARGET = BV_RESOURCE_BLOCK_GAS_LIMIT // BV_BLOCK_LOG_MIN_GAS
BV_BLOCK_LOG_DATA_FULL_TARGET = BV_RESOURCE_BLOCK_GAS_LIMIT // BV_BLOCK_LOG_DATA_BYTE_GAS
BV_BLOCK_LOG_DESC_CAPACITY = 128
BV_BLOCK_LOG_DATA_BYTES = 65536
BV_LOGS_RLP_ARENA_BYTES = 65536
BV_RECEIPTS_RLP_BYTES = 65536
BV_RECEIPT_LIST_PAYLOAD_BYTES = 32768
BV_RECEIPT_CONSENSUS_DESC_CAPACITY = BMV_FULL_TX_CAPACITY
BV_SYSTEM_STORAGE_LOG_CAPACITY = 32768
BV_MTX_COMMITTED_FULL_KEY_CAP = BV_MTX_COMMITTED_CANONICAL_CAPACITY
C1_DEPOSIT_BODY_BYTES = 32768
C1_LOG_RECORDS_BYTES = 81920
C1_EXECUTION_REQUESTS_BYTES = 32768
SYSTEM_REQUEST_BODY_BYTES = 2048
ERH_BLOB_BYTES = 1572865


def byte_len(value) -> int:
    if value is None:
        return 0
    if isinstance(value, (bytes, bytearray, memoryview)):
        return len(value)
    try:
        return len(bytes(value))
    except Exception:
        return 0


def seq_count(value) -> int:
    if value is None:
        return 0
    if isinstance(value, (bytes, bytearray, memoryview)):
        return len(value)
    try:
        return len(value)
    except Exception:
        return 0


def fixed_item_count(value, item_size: int) -> int:
    if isinstance(value, (bytes, bytearray, memoryview)):
        return len(value) // item_size
    return seq_count(value)


def request_body_metrics(stateless_input) -> dict[str, int]:
    request = getattr(stateless_input, "new_payload_request", None)
    execution_requests = getattr(request, "execution_requests", None)
    if execution_requests is None:
        return {
            "request_deposits": 0,
            "request_deposit_bytes": 0,
            "request_withdrawals": 0,
            "request_withdrawal_bytes": 0,
            "request_consolidations": 0,
            "request_consolidation_bytes": 0,
            "request_section_bytes": 0,
        }

    deposits = getattr(execution_requests, "deposits", None)
    withdrawals = getattr(execution_requests, "withdrawals", None)
    consolidations = getattr(execution_requests, "consolidations", None)
    deposit_count = fixed_item_count(deposits, 192)
    withdrawal_count = fixed_item_count(withdrawals, 76)
    consolidation_count = fixed_item_count(consolidations, 116)
    deposit_bytes = byte_len(deposits) or deposit_count * 192
    withdrawal_bytes = byte_len(withdrawals) or withdrawal_count * 76
    consolidation_bytes = byte_len(consolidations) or consolidation_count * 116
    return {
        "request_deposits": deposit_count,
        "request_deposit_bytes": deposit_bytes,
        "request_withdrawals": withdrawal_count,
        "request_withdrawal_bytes": withdrawal_bytes,
        "request_consolidations": consolidation_count,
        "request_consolidation_bytes": consolidation_bytes,
        "request_section_bytes": 12 + deposit_bytes + withdrawal_bytes + consolidation_bytes,
    }


def summarize(
    input_path: Path,
    *,
    bsr_cap: int,
    bsr_bal_cap: int,
) -> tuple[dict[str, int], list[dict[str, str]]]:
    stateless_input, payload, bal = decode_bal(input_path)
    request_metrics = request_body_metrics(stateless_input)
    tx_count = len(payload.transactions)
    summary = {
        "input_len": input_path.stat().st_size - 8,
        "bal_bytes": len(payload.block_access_list),
        "bal_rows": len(bal),
        "bsr_bal_cap": bsr_bal_cap,
        "over_bsr_bal_cap": 0,
        "readonly_rows": 0,
        "changed_rows": 0,
        "modeled_system_changed": 0,
        "withdrawal_request_changed": 0,
        "other_changed": 0,
        "storage_slots": 0,
        "storage_writes": 0,
        # This is the block-wide BAL total, including read-only AccountChanges.
        # A read-only account is still a declared storage-read row and must not
        # disappear when this summary is compared with guest-side totals.
        "storage_reads": 0,
        "readonly_storage_reads": 0,
        "balance_changes": 0,
        "nonce_changes": 0,
        "code_changes": 0,
        "state_nodes": len(stateless_input.witness.state),
        "widx_cap": MPT_WITNESS_INDEX_CAP,
        "over_widx_cap": 0,
        "state_witness_bytes": sum(4 + len(node) for node in stateless_input.witness.state),
        "state_max_bytes": max((len(node) for node in stateless_input.witness.state), default=0),
        "bsr_witness_cap": bsr_cap,
        "over_bsr_cap": 0,
        "codes": len(stateless_input.witness.codes),
        "code_witness_bytes": sum(4 + len(code) for code in stateless_input.witness.codes),
        "code_max_bytes": max((len(code) for code in stateless_input.witness.codes), default=0),
        "headers": len(stateless_input.witness.headers),
        "headers_witness_bytes": sum(4 + len(header) for header in stateless_input.witness.headers),
        "header_max_bytes": max((len(header) for header in stateless_input.witness.headers), default=0),
        "txs": tx_count,
        "tx_arena_cap": BV_MTX_ARENA_TX_CAP,
        "tx_full_200m_cap": BMV_FULL_TX_CAPACITY,
        "receipt_records_required": tx_count,
        "receipt_record_cap": BV_RECEIPT_RECORD_CAPACITY,
        "block_log_desc_cap": BV_BLOCK_LOG_DESC_CAPACITY,
        "block_log_desc_full_target": BV_BLOCK_LOG_DESC_FULL_TARGET,
        "block_log_data_cap": BV_BLOCK_LOG_DATA_BYTES,
        "block_log_data_full_target": BV_BLOCK_LOG_DATA_FULL_TARGET,
        "logs_rlp_cap": BV_LOGS_RLP_ARENA_BYTES,
        "receipts_rlp_cap": BV_RECEIPTS_RLP_BYTES,
        "receipt_list_payload_cap": BV_RECEIPT_LIST_PAYLOAD_BYTES,
        "receipt_consensus_desc_cap": BV_RECEIPT_CONSENSUS_DESC_CAPACITY,
        "committed_storage_cap": BV_MTX_COMMITTED_CANONICAL_CAPACITY,
        "committed_storage_active_cap": BV_MTX_COMMITTED_CANONICAL_CAPACITY,
        "committed_storage_full_key_cap": BV_MTX_COMMITTED_FULL_KEY_CAP,
        "system_storage_cap": BV_SYSTEM_STORAGE_LOG_CAPACITY,
        "deposit_body_cap": C1_DEPOSIT_BODY_BYTES,
        "log_records_cap": C1_LOG_RECORDS_BYTES,
        "execution_requests_cap": C1_EXECUTION_REQUESTS_BYTES,
        "system_request_body_cap": SYSTEM_REQUEST_BODY_BYTES,
        "request_hash_blob_cap": ERH_BLOB_BYTES,
        **request_metrics,
    }
    summary["over_bsr_cap"] = int(summary["state_witness_bytes"] > bsr_cap)
    summary["over_widx_cap"] = int(summary["state_nodes"] > summary["widx_cap"])
    summary["over_bsr_bal_cap"] = int(summary["bal_rows"] > bsr_bal_cap)
    details: list[dict[str, str]] = []

    for row, account_changes in enumerate(bal):
        address = bytes(account_changes.address).hex()
        changed = is_changed(account_changes)
        storage_reads = len(account_changes.storage_reads)
        summary["storage_reads"] += storage_reads
        if not changed:
            summary["readonly_rows"] += 1
            summary["readonly_storage_reads"] += storage_reads
            continue

        storage_slots = len(account_changes.storage_changes)
        storage_writes = count_storage_writes(account_changes)
        balance_changes = len(account_changes.balance_changes)
        nonce_changes = len(account_changes.nonce_changes)
        code_changes = len(account_changes.code_changes)
        modeled_system = address in MODELED_SYSTEM_ADDRESSES
        withdrawal_request = address == WITHDRAWAL_REQUEST_ADDRESS

        summary["changed_rows"] += 1
        summary["storage_slots"] += storage_slots
        summary["storage_writes"] += storage_writes
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


def result_status(results_dir: Path, label: str) -> str:
    result = results_dir / f"{label}.result.tsv"
    if not result.is_file():
        return "MISSING"
    status, _actual = result.read_text().rstrip("\n").split("\t", 1)
    return status


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
        "--status-only",
        default="",
        help="only include rows whose result.tsv status equals this value (for example BUDGET)",
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
        "bsr_bal_cap",
        "over_bsr_bal_cap",
        "readonly_rows",
        "changed_rows",
        "modeled_system_changed",
        "withdrawal_request_changed",
        "other_changed",
        "storage_slots",
        "storage_writes",
        "storage_reads",
        "readonly_storage_reads",
        "balance_changes",
        "nonce_changes",
        "code_changes",
        "state_nodes",
        "widx_cap",
        "over_widx_cap",
        "state_witness_bytes",
        "state_max_bytes",
        "bsr_witness_cap",
        "over_bsr_cap",
        "codes",
        "code_witness_bytes",
        "code_max_bytes",
        "headers",
        "headers_witness_bytes",
        "header_max_bytes",
        "txs",
        "tx_arena_cap",
        "tx_full_200m_cap",
        "receipt_records_required",
        "receipt_record_cap",
        "block_log_desc_cap",
        "block_log_desc_full_target",
        "block_log_data_cap",
        "block_log_data_full_target",
        "logs_rlp_cap",
        "receipts_rlp_cap",
        "receipt_list_payload_cap",
        "receipt_consensus_desc_cap",
        "committed_storage_cap",
        "committed_storage_active_cap",
        "committed_storage_full_key_cap",
        "system_storage_cap",
        "deposit_body_cap",
        "log_records_cap",
        "execution_requests_cap",
        "system_request_body_cap",
        "request_hash_blob_cap",
        "request_deposits",
        "request_deposit_bytes",
        "request_withdrawals",
        "request_withdrawal_bytes",
        "request_consolidations",
        "request_consolidation_bytes",
        "request_section_bytes",
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
            elif len(parts) >= 7:
                label, input_file, expected_hex, _succ_bit, _input_len, _gas_limit, relpath = parts[:7]
            else:
                raise SystemExit(f"bad manifest row with {len(parts)} columns: {line!r}")
            if args.filter and args.filter not in label and args.filter not in relpath:
                continue
            if args.status_only and result_status(results_dir, label) != args.status_only:
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
