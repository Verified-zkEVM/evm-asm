#!/usr/bin/env python3
"""Compare final guest BAL-builder rows with a pre-registered EEST fixture.

This is a tooling-only probe.  The guest is executed unchanged; SPIKE dumps
the nm-derived builder ranges after halt, and this script decodes those rows.
The reference side is the pinned execution-specs BAL carried by the fixture,
not guest output fed back into SpecRef.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import struct
import subprocess
import sys
from pathlib import Path
from typing import Any, NoReturn


MAGIC = b"SPKDMP01"
U64 = struct.Struct("<Q")
U32 = struct.Struct("<I")


def fail(message: str) -> NoReturn:
    raise SystemExit(f"FAIL: {message}")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_manifest(path: Path, label: str) -> dict[str, str]:
    for raw in path.read_text().splitlines():
        if not raw.strip():
            continue
        fields = raw.split("\t")
        if len(fields) not in (7, 8):
            fail(f"bad manifest row with {len(fields)} fields: {raw!r}")
        if fields[0] != label:
            continue
        return {
            "label": fields[0],
            "input": fields[1],
            "expected": fields[2],
            "fixture_relpath": fields[-2] if len(fields) == 8 else fields[-1],
            "case_id": fields[-1] if len(fields) == 8 else "",
        }
    fail(f"manifest label not found: {label}")


def input_path(manifest: Path, row: dict[str, str]) -> Path:
    path = Path(row["input"])
    return path if path.is_absolute() else manifest.parent / path


def load_spec(input_file: Path, specs_dir: Path) -> dict[str, Any]:
    src = specs_dir / "src"
    if not src.is_dir():
        fail(f"execution-specs source directory not found: {src}")
    sys.path.insert(0, str(src))
    try:
        from ethereum.forks.amsterdam.block_access_lists import BlockAccessList
        from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
        from ethereum_rlp import rlp
    except ImportError as exc:
        fail(f"pinned execution-specs dependencies are unavailable: {exc}")

    raw = input_file.read_bytes()
    if len(raw) < 8:
        fail(f"input shorter than zisk length prefix: {input_file}")
    length = int.from_bytes(raw[:8], "little")
    blob = raw[8 : 8 + length]
    if len(blob) != length:
        fail(f"truncated input: want {length} bytes, have {len(blob)}")
    stateless_input = deserialize_stateless_input(blob)
    payload = stateless_input.new_payload_request.execution_payload
    bal = rlp.decode_to(BlockAccessList, payload.block_access_list)

    rows: dict[str, list[Any]] = {
        "accounts": [],
        "storage": [],
        "balance": [],
        "nonce": [],
        "code": [],
    }
    for account in bal:
        address = bytes(account.address).hex()
        rows["accounts"].append(address)
        for group in account.storage_changes:
            for change in group.changes:
                rows["storage"].append(
                    {
                        "address": address,
                        "bai": int(change.block_access_index),
                        "slot": int(group.slot),
                        "value": int(change.new_value),
                    }
                )
        for change in account.balance_changes:
            rows["balance"].append(
                {
                    "address": address,
                    "bai": int(change.block_access_index),
                    "post": int(change.post_balance),
                }
            )
        for change in account.nonce_changes:
            rows["nonce"].append(
                {
                    "address": address,
                    "bai": int(change.block_access_index),
                    "nonce": int(change.new_nonce),
                }
            )
        for change in account.code_changes:
            rows["code"].append(
                {
                    "address": address,
                    "bai": int(change.block_access_index),
                    "code": bytes(change.new_code).hex(),
                }
            )

    # Make the reference canonical independently of the order in which the
    # decoder happens to expose each list.
    rows["accounts"].sort()
    rows["storage"].sort(key=lambda row: (row["address"], row["slot"], row["bai"]))
    for name in ("balance", "nonce", "code"):
        rows[name].sort(key=lambda row: (row["address"], row["bai"]))
    return {
        "rows": rows,
        "input_len": length,
        "payload_bal_sha256": hashlib.sha256(payload.block_access_list).hexdigest(),
    }


def write_expectation(path: Path, manifest: Path, row: dict[str, str], spec: dict[str, Any], specs_dir: Path) -> None:
    pin = subprocess.run(
        ["git", "-C", str(specs_dir), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    value = {
        "schema": 1,
        "fixture_label": row["label"],
        "fixture_relpath": row["fixture_relpath"],
        "manifest_sha256": sha256(manifest),
        "input_sha256": sha256(input_path(manifest, row)),
        "execution_specs_commit": pin,
        "reference": "execution-specs Amsterdam BlockAccessList decoded from fixture payload",
        "payload_bal_sha256": spec["payload_bal_sha256"],
        "rows": spec["rows"],
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")
    print(f"pre-registered expectation: {path}")


def nm_symbols(elf: Path) -> dict[str, int]:
    try:
        proc = subprocess.run(
            ["riscv64-unknown-elf-nm", "-n", str(elf)],
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        fail(f"nm failed for {elf}: {exc}")
    result: dict[str, int] = {}
    for raw in proc.stdout.splitlines():
        fields = raw.split()
        if len(fields) == 3:
            try:
                result[fields[2]] = int(fields[0], 16)
            except ValueError:
                pass
    return result


def lean_nat(source: Path, name: str) -> int:
    text = source.read_text()
    match = re.search(rf"def {re.escape(name)} : Nat := (\d+)", text)
    if not match:
        # Some capacity definitions are intentionally expressed as a formula;
        # their kernel-checked #guard still records the concrete value.
        match = re.search(rf"#guard {re.escape(name)} = (\d+)", text)
    if not match:
        fail(f"cannot find {name} in {source}")
    return int(match.group(1))


def dump_ranges(
    elf: Path, program_source: Path, code_source: Path, params_source: Path
) -> tuple[str, dict[str, int], dict[str, int]]:
    symbols = nm_symbols(elf)
    required = [
        "bal_builder_current_bai",
        "bal_builder_account_count",
        "bal_builder_storage_change_count",
        "bal_builder_balance_count",
        "bal_builder_nonce_count",
        "bal_builder_code_count",
        "bal_builder_overflow",
        "bal_builder_storage_change_overflow",
        "bal_builder_balance_overflow",
        "bal_builder_nonce_overflow",
        "bal_builder_code_overflow",
        "bal_builder_accounts",
        "bal_builder_storage_changes",
        "bal_builder_balance_changes",
        "bal_builder_nonce_changes",
        "bal_builder_code_changes",
        "exec_code_effect_log",
        "eip7702_auth_code_slots",
        "bal_serializer_surviving_read_count",
        "bal_serializer_sort_status",
        "bal_serializer_rebuilt_hash",
        "bal_serializer_supplied_hash",
    ]
    missing = [name for name in required if name not in symbols]
    if missing:
        fail(f"guest ELF is missing required BAL symbols: {', '.join(missing)}")

    capacities = {
        "accounts": lean_nat(program_source, "balBuilderAccountCapacity"),
        "storage": lean_nat(program_source, "balBuilderStorageChangeCapacity"),
        "balance": lean_nat(program_source, "balBuilderBalanceCapacity"),
        "nonce": lean_nat(program_source, "balBuilderNonceCapacity"),
        "code": lean_nat(program_source, "balBuilderCodeCapacity"),
    }
    strides = {
        "accounts": lean_nat(program_source, "balBuilderAccountRowBytes"),
        "storage": lean_nat(program_source, "balBuilderStorageChangeRowBytes"),
        "balance": lean_nat(program_source, "balBuilderBalanceRowBytes"),
        "nonce": lean_nat(program_source, "balBuilderNonceRowBytes"),
        "code": lean_nat(program_source, "balBuilderCodeRowBytes"),
    }
    code_effect_log_bytes = lean_nat(code_source, "execCodeEffectLogCap")
    eip7702_auth_code_bytes = (
        lean_nat(params_source, "bvEip7702AuthEntryCapacity") * 24
    )
    arrays = {
        "accounts": "bal_builder_accounts",
        "storage": "bal_builder_storage_changes",
        "balance": "bal_builder_balance_changes",
        "nonce": "bal_builder_nonce_changes",
        "code": "bal_builder_code_changes",
    }
    current = symbols["bal_builder_current_bai"]
    overflow_end = symbols["bal_builder_code_overflow"] + 8
    ranges: list[tuple[int, int]] = [(current, overflow_end - current)]
    for name in ("accounts", "storage", "balance", "nonce", "code"):
        ranges.append((symbols[arrays[name]], capacities[name] * strides[name]))
    ranges += [
        (symbols["exec_code_effect_log"], code_effect_log_bytes),
        (symbols["eip7702_auth_code_slots"], eip7702_auth_code_bytes),
        (symbols["bal_serializer_surviving_read_count"], 8),
        (symbols["bal_serializer_sort_status"], 8),
        (symbols["bal_serializer_rebuilt_hash"], 32),
        (symbols["bal_serializer_supplied_hash"], 32),
    ]
    dump = ",".join(f"0x{address:x}:{length}" for address, length in ranges)
    return dump, symbols, {
        **capacities,
        **{f"{name}_stride": value for name, value in strides.items()},
        "code_effect_log_bytes": code_effect_log_bytes,
        "eip7702_auth_code_bytes": eip7702_auth_code_bytes,
    }


def read_dump(path: Path) -> dict[int, bytes]:
    data = path.read_bytes()
    if len(data) < 16 or data[:8] != MAGIC:
        fail(f"bad SPIKE dump header: {path}")
    version = U32.unpack_from(data, 8)[0]
    count = U32.unpack_from(data, 12)[0]
    if version != 1:
        fail(f"unsupported SPIKE dump version {version}")
    pos = 16
    result: dict[int, bytes] = {}
    for _ in range(count):
        if pos + 16 > len(data):
            fail("truncated SPIKE dump record header")
        address = U64.unpack_from(data, pos)[0]
        length = U64.unpack_from(data, pos + 8)[0]
        pos += 16
        if length > len(data) - pos:
            fail("truncated SPIKE dump record payload")
        result[address] = data[pos : pos + length]
        pos += length
    if pos != len(data):
        fail("trailing bytes in SPIKE dump")
    return result


def read_at(ranges: dict[int, bytes], address: int, length: int) -> bytes:
    for base, data in ranges.items():
        if base <= address and address + length <= base + len(data):
            offset = address - base
            return data[offset : offset + length]
    fail(f"dump does not cover 0x{address:x}+{length}")


def maybe_read_at(ranges: dict[int, bytes], address: int, length: int) -> bytes | None:
    for base, data in ranges.items():
        if base <= address and address + length <= base + len(data):
            offset = address - base
            return data[offset : offset + length]
    return None


def u64_at(ranges: dict[int, bytes], address: int) -> int:
    return int.from_bytes(read_at(ranges, address, 8), "little")


def decode_rows(
    ranges: dict[int, bytes], symbols: dict[str, int], layout: dict[str, int]
) -> tuple[dict[str, list[Any]], dict[str, int], dict[str, Any]]:
    global_base = symbols["bal_builder_current_bai"]
    global_len = symbols["bal_builder_code_overflow"] + 8 - global_base
    read_at(ranges, global_base, global_len)
    count_symbols = {
        "accounts": "bal_builder_account_count",
        "storage": "bal_builder_storage_change_count",
        "balance": "bal_builder_balance_count",
        "nonce": "bal_builder_nonce_count",
        "code": "bal_builder_code_count",
    }
    counts = {name: u64_at(ranges, symbols[symbol]) for name, symbol in count_symbols.items()}
    overflows = {
        name: u64_at(ranges, symbols[symbol])
        for name, symbol in {
            "shared": "bal_builder_overflow",
            "storage": "bal_builder_storage_change_overflow",
            "balance": "bal_builder_balance_overflow",
            "nonce": "bal_builder_nonce_overflow",
            "code": "bal_builder_code_overflow",
        }.items()
    }
    rows: dict[str, list[Any]] = {name: [] for name in count_symbols}
    undecodable = 0
    bases = {
        "accounts": "bal_builder_accounts",
        "storage": "bal_builder_storage_changes",
        "balance": "bal_builder_balance_changes",
        "nonce": "bal_builder_nonce_changes",
        "code": "bal_builder_code_changes",
    }
    for name, base_symbol in bases.items():
        if counts[name] > layout[name]:
            fail(f"{name} count {counts[name]} exceeds capacity {layout[name]}")
        base = symbols[base_symbol]
        stride = layout[f"{name}_stride"]
        for index in range(counts[name]):
            row = read_at(ranges, base + index * stride, stride)
            address = row[:20].hex()
            bai = int.from_bytes(row[24:32], "little")
            if name == "accounts":
                rows[name].append(address)
            elif name == "storage":
                rows[name].append(
                    {
                        "address": address,
                        "bai": bai,
                        "slot": int.from_bytes(row[32:64], "big"),
                        "value": int.from_bytes(row[64:96], "little"),
                    }
                )
            elif name == "balance":
                rows[name].append(
                    {"address": address, "bai": bai, "post": int.from_bytes(row[32:64], "big")}
                )
            elif name == "nonce":
                rows[name].append(
                    {"address": address, "bai": bai, "nonce": int.from_bytes(row[32:40], "little")}
                )
            else:
                code_ptr = int.from_bytes(row[32:40], "little")
                code_len = int.from_bytes(row[40:48], "little")
                code = maybe_read_at(ranges, code_ptr, code_len)
                if code is None:
                    undecodable += 1
                    code_hex = None
                else:
                    code_hex = code.hex()
                rows[name].append(
                    {
                        "address": address,
                        "bai": bai,
                        "code": code_hex,
                    }
                )
    hashes = {
        "rebuilt": read_at(ranges, symbols["bal_serializer_rebuilt_hash"], 32).hex(),
        "supplied": read_at(ranges, symbols["bal_serializer_supplied_hash"], 32).hex(),
        "equal": read_at(ranges, symbols["bal_serializer_rebuilt_hash"], 32)
        == read_at(ranges, symbols["bal_serializer_supplied_hash"], 32),
        "sort_status": u64_at(ranges, symbols["bal_serializer_sort_status"]),
        "surviving_reads": u64_at(ranges, symbols["bal_serializer_surviving_read_count"]),
    }
    return rows, counts, {"overflows": overflows, "hashes": hashes, "undecodable": undecodable}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spike", type=Path, required=True)
    parser.add_argument("--guest-elf", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--expectation", type=Path, required=True)
    parser.add_argument("--execution-specs", type=Path, default=None)
    parser.add_argument(
        "--program-source",
        type=Path,
        default=None,
        help="BlockAccessListBuilder.lean (defaults to the checkout source)",
    )
    parser.add_argument(
        "--code-source",
        type=Path,
        default=None,
        help="CreateCodeEffectLog.lean (defaults to the checkout source)",
    )
    parser.add_argument(
        "--params-source",
        type=Path,
        default=None,
        help="BlockVerdictParams.lean (defaults to the checkout source)",
    )
    parser.add_argument(
        "--register-expectation",
        action="store_true",
        help="derive and write the expectation before executing the guest",
    )
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[2]
    specs_dir = args.execution_specs or root / "execution-specs"
    source = args.program_source or root / "EvmAsm/Codegen/Programs/BlockAccessListBuilder.lean"
    code_source = args.code_source or root / "EvmAsm/Codegen/Programs/CreateCodeEffectLog.lean"
    params_source = args.params_source or root / "EvmAsm/Codegen/Programs/BlockVerdictParams.lean"
    row = load_manifest(args.manifest, args.label)
    input_file = input_path(args.manifest, row)
    if not input_file.is_file():
        fail(f"fixture input not found: {input_file}")

    if args.register_expectation:
        spec = load_spec(input_file, specs_dir)
        write_expectation(args.expectation, args.manifest, row, spec, specs_dir)
    if not args.expectation.is_file():
        fail(f"pre-registered expectation not found: {args.expectation}")
    expectation = json.loads(args.expectation.read_text())
    if expectation.get("fixture_label") != args.label:
        fail("expectation fixture label does not match --label")
    actual_input_sha = sha256(input_file)
    if expectation.get("input_sha256") != actual_input_sha:
        fail("expectation input sha256 does not match the manifest fixture")
    actual_manifest_sha = sha256(args.manifest)
    if expectation.get("manifest_sha256") != actual_manifest_sha:
        fail("expectation manifest sha256 does not match --manifest")
    spec = load_spec(input_file, specs_dir)
    if expectation.get("payload_bal_sha256") != spec["payload_bal_sha256"]:
        fail("expectation payload BAL sha256 does not match the fixture")
    if expectation.get("rows") != spec["rows"]:
        fail("pre-registered rows differ from the pinned execution-specs reference")
    expected_rows = expectation["rows"]

    dump, symbols, layout = dump_ranges(args.guest_elf, source, code_source, params_source)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    dump_file = args.out_dir / "bal-final-memory.bin"
    output_file = args.out_dir / "guest-output.bin"
    env = os.environ.copy()
    env["SPIKE_DUMP_RANGES"] = dump
    env["SPIKE_DUMP_FILE"] = str(dump_file)
    proc = subprocess.run(
        [str(args.spike), str(args.guest_elf), str(input_file), str(output_file)],
        env=env,
        check=False,
    )
    if proc.returncode != 0:
        fail(f"guest execution returned {proc.returncode}")
    if not dump_file.is_file():
        fail("guest succeeded without a final-memory dump")

    actual_rows, counts, diagnostics = decode_rows(read_dump(dump_file), symbols, layout)
    attempted = sum(counts.values())
    skipped = 0
    undecodable = diagnostics["undecodable"]
    decoded = attempted - skipped
    mismatches = [name for name in actual_rows if actual_rows[name] != expected_rows.get(name, [])]
    overflowed = {name: value for name, value in diagnostics["overflows"].items() if value}
    if mismatches:
        fail(f"row mismatch in {', '.join(mismatches)}")
    if skipped or undecodable:
        fail(f"rows silently skipped or undecodable: skipped={skipped} undecodable={undecodable}")
    if overflowed:
        fail(f"builder overflow flags set: {overflowed}")
    if diagnostics["hashes"]["sort_status"]:
        fail(f"BAL serializer sort status is {diagnostics['hashes']['sort_status']}")
    if not diagnostics["hashes"]["equal"]:
        fail("rebuilt BAL hash differs from supplied BAL hash")

    report = {
        "fixture": args.label,
        "input_sha256": actual_input_sha,
        "guest_elf_sha256": sha256(args.guest_elf),
        "attempted": attempted,
        "decoded": decoded,
        "skipped": skipped,
        "undecodable": undecodable,
        "overflow": overflowed,
        "final_counts": counts,
        "serializer_hash": diagnostics["hashes"],
        "dump_file": str(dump_file),
    }
    print(json.dumps(report, sort_keys=True))
    print("PASS: final BAL-builder rows and serialized BAL hash match the pre-registered fixture")
    return 0


if __name__ == "__main__":
    main()
