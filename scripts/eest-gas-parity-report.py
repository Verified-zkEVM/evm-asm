#!/usr/bin/env python3
"""Report gas-oriented parity between execution-specs and ziskemu EEST runs.

This script consumes the run directory produced by
``scripts/codegen-eest-stateless-check.sh``.  For each manifest row it:

* unpacks the exact guest-visible ``statelessInputBytes`` from the ziskemu input;
* decodes payload gas fields through the Amsterdam execution-specs;
* runs Python ``run_stateless_guest`` on the same bytes;
* compares the Python, fixture, and RISC-V/ziskemu 105-byte outputs.

Run via ``uv run --directory execution-specs --quiet python3`` so the local
execution-specs dependencies are on ``sys.path``.
"""
from __future__ import annotations

import argparse
import struct
from pathlib import Path
from typing import Iterable


DEBUG_LABELS = (
    "verdict",
    "bv_fail",
    "header",
    "state",
    "bal_count",
    "bsr_fail",
    "change_count",
    "witness_len",
    "baacd_fail",
    "bacv_fail",
    "baap_fail",
    "sri_index",
    "sri_mode",
    "sri_status",
    "block_rlp_len",
)


def unpack_ziskemu_input(path: Path) -> bytes:
    packed = path.read_bytes()
    if len(packed) < 8:
        raise ValueError(f"{path} is too short for ziskemu input")
    n = struct.unpack("<Q", packed[:8])[0]
    end = 8 + n
    if len(packed) < end:
        raise ValueError(f"{path} is truncated: wants {n} bytes, has {len(packed) - 8}")
    pad = packed[end:]
    if any(pad):
        raise ValueError(f"{path} has non-zero ziskemu input padding")
    return packed[8:end]


def succ_byte(hex_string: str) -> str:
    return hex_string[64:66] if len(hex_string) >= 66 else "??"


def region_bits(actual: str, expected: str) -> str:
    expected = expected[:210]
    root = "root" if actual[:64] == expected[:64] else "----"
    succ = "succ" if actual[64:66] == expected[64:66] else "----"
    tail = "tail" if actual[66:210] == expected[66:210] else "----"
    return f"{root}/{succ}/{tail}"


def read_result(run_dir: Path, label: str) -> tuple[str, str]:
    result_path = run_dir / f"{label}.result.tsv"
    if not result_path.exists():
        return "MISSING", ""
    line = result_path.read_text().splitlines()[0]
    fields = line.split("\t", 1)
    if len(fields) == 1:
        return fields[0], ""
    return fields[0], fields[1]


def read_verdict_debug(run_dir: Path, label: str) -> str:
    path = run_dir / f"{label}.verdict-debug.output"
    if not path.exists():
        return ""
    raw = path.read_bytes()[: 8 * len(DEBUG_LABELS)]
    words = [
        struct.unpack("<Q", raw[i : i + 8])[0]
        for i in range(0, len(raw) - (len(raw) % 8), 8)
    ]
    return " ".join(
        f"{name}={words[i] if i < len(words) else '?'}"
        for i, name in enumerate(DEBUG_LABELS)
    )


def iter_manifest(path: Path) -> Iterable[tuple[str, Path, str, str, int, int, str]]:
    for raw in path.read_text().splitlines():
        if not raw:
            continue
        label, input_file, expected_hex, succ_bit, input_len, gas_limit, relpath = raw.split(
            "\t", 6
        )
        yield (
            label,
            Path(input_file),
            expected_hex,
            succ_bit,
            int(input_len),
            int(gas_limit),
            relpath,
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", required=True, type=Path)
    parser.add_argument("--tsv", action="store_true", help="print tab-separated rows")
    args = parser.parse_args()

    from ethereum.forks.amsterdam.stateless_guest import (
        deserialize_stateless_input,
        run_stateless_guest,
    )
    from ethereum_types.bytes import Bytes

    manifest = args.run_dir / "manifest.tsv"
    if not manifest.exists():
        raise SystemExit(f"manifest not found: {manifest}")

    total = 0
    python_errors = 0
    fixture_python_mismatch = 0
    guest_python_succ_mismatch = 0
    guest_python_full_mismatch = 0

    if args.tsv:
        print(
            "\t".join(
                [
                    "status",
                    "relpath",
                    "fixture_succ",
                    "python_succ",
                    "guest_succ",
                    "payload_gas_limit",
                    "payload_gas_used",
                    "payload_gas_remaining",
                    "tx_count",
                    "guest_regions_vs_python",
                    "debug",
                ]
            )
        )

    for label, input_file, expected_hex, _succ_bit, _input_len, manifest_gas_limit, relpath in iter_manifest(
        manifest
    ):
        total += 1
        blob = unpack_ziskemu_input(input_file)
        try:
            stateless_input = deserialize_stateless_input(Bytes(blob))
            py_hex = bytes(run_stateless_guest(Bytes(blob))).hex()
        except Exception as exc:  # execution-specs exceptions are the signal here
            python_errors += 1
            payload_gas_limit = manifest_gas_limit
            payload_gas_used = -1
            payload_remaining = -1
            tx_count = -1
            py_succ = "ERR"
            py_hex = ""
            py_error = f"{type(exc).__name__}:{exc}"
        else:
            payload = stateless_input.new_payload_request.execution_payload
            payload_gas_limit = int(payload.gas_limit)
            payload_gas_used = int(payload.gas_used)
            payload_remaining = payload_gas_limit - payload_gas_used
            tx_count = len(payload.transactions)
            py_succ = succ_byte(py_hex)
            py_error = ""
            if py_hex[:210] != expected_hex[:210]:
                fixture_python_mismatch += 1

        guest_status, guest_value = read_result(args.run_dir, label)
        if guest_status == "OK":
            guest_succ = succ_byte(guest_value)
            regions = region_bits(guest_value, py_hex) if py_hex else "----/----/----"
            if py_hex and guest_succ != py_succ:
                guest_python_succ_mismatch += 1
            if py_hex and guest_value[:210] != py_hex[:210]:
                guest_python_full_mismatch += 1
        else:
            guest_succ = guest_status
            regions = "----/----/----"

        debug = read_verdict_debug(args.run_dir, label)
        if py_error:
            debug = f"{debug} python_error={py_error}".strip()

        row = [
            guest_status,
            relpath,
            succ_byte(expected_hex),
            py_succ,
            guest_succ,
            str(payload_gas_limit),
            str(payload_gas_used),
            str(payload_remaining),
            str(tx_count),
            regions,
            debug,
        ]
        if args.tsv:
            print("\t".join(row))
        else:
            mismatch = ""
            if py_error:
                mismatch = " python=ERROR"
            elif guest_status == "OK" and guest_succ != py_succ:
                mismatch = " succ-mismatch"
            elif guest_status != "OK":
                mismatch = f" guest={guest_status}"
            print(
                f"  {guest_status:<7} [{regions}] {relpath} "
                f"(succ fixture={succ_byte(expected_hex)} python={py_succ} guest={guest_succ}; "
                f"gas_used={payload_gas_used}/{payload_gas_limit} "
                f"remaining={payload_remaining} txs={tx_count}){mismatch}"
            )
            if debug:
                print(f"    dbg=[{debug}]")

    print("==> gas parity summary")
    print(f"  total:                     {total}")
    print(f"  python errors:             {python_errors}")
    print(f"  fixture/python mismatches: {fixture_python_mismatch}")
    print(f"  guest/python succ mismatches: {guest_python_succ_mismatch}")
    print(f"  guest/python full mismatches: {guest_python_full_mismatch}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
