#!/usr/bin/env python3
"""Run the standing verdict and control sweep.

The account-agreement probe was retired in 11638; this script no longer performs
map-versus-live comparison.  It retains the runtime mutation observation and
optional candidate/base output comparison, and always runs ``STANDING_NAMED_CONTROLS``.
That list carries known-flippable negative rows from 11508 so they remain named
controls rather than disappearing into a random sample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import struct
import subprocess
import sys
import tempfile
from pathlib import Path


MAGIC = b"SPKDMP01"
MUTATION_EVENT_SIZE = 96
MUTATION_EVENT_CAPACITY = 1024
MUTATION_ID_NAMES = {
    1: "root_recipient_credit",
    2: "call_child_credit",
    3: "precompile_caller_debit",
    4: "create_child_credit",
    5: "call_caller_debit",
    6: "create_creator_debit",
    7: "call_failed_child_rollback_recredit",
}
STANDING_NAMED_CONTROLS = [
    "18529_test_call_sha256_1_nonzero_value_fork_Amsterdam-blockchain_test_from_state_test__b0",
    "15904_test_callcall_00_ooge_value_transfer_fork_Amsterdam-blockchain_test_from_state_test__b0",
    "00349_test_bal_gas_limit_boundary_fork_Amsterdam-blockchain_test-below_boundary-no_tx-no_cl_withdrawal",
    "00350_test_bal_gas_limit_boundary_fork_Amsterdam-blockchain_test-below_boundary-no_tx-with_cl_withdraw",
    "26003_test_fork_transition_bal_size_constraint_fork_BPO2ToAmsterdamAtTime15k-blockchain_test-at_fork_o",
    "02965_test_validation_codes_missing_delegated_code_on_insufficient_balance_call_fork_Amsterdam-blockch",
    "02967_test_validation_codes_missing_implicit_system_contract_code_fork_Amsterdam-blockchain_test__b0",
    "02970_test_validation_codes_missing_sender_delegation_marker_fork_Amsterdam-blockchain_test__b0",
    "02998_test_validation_state_missing_failed_call_target_account_proof_node_fork_Amsterdam-blockchain_te",
]
STANDING_NAMED_EXPECTED = {
    "00349_test_bal_gas_limit_boundary_fork_Amsterdam-blockchain_test-below_boundary-no_tx-no_cl_withdrawal": 0,
    "00350_test_bal_gas_limit_boundary_fork_Amsterdam-blockchain_test-below_boundary-no_tx-with_cl_withdraw": 0,
    "26003_test_fork_transition_bal_size_constraint_fork_BPO2ToAmsterdamAtTime15k-blockchain_test-at_fork_o": 0,
    "02965_test_validation_codes_missing_delegated_code_on_insufficient_balance_call_fork_Amsterdam-blockch": 0,
    "02967_test_validation_codes_missing_implicit_system_contract_code_fork_Amsterdam-blockchain_test__b0": 0,
    "02970_test_validation_codes_missing_sender_delegation_marker_fork_Amsterdam-blockchain_test__b0": 0,
    "02998_test_validation_state_missing_failed_call_target_account_proof_node_fork_Amsterdam-blockchain_te": 0,
}
U64 = struct.Struct("<Q")


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def symbols(elf: Path, nm: str) -> dict[str, int]:
    result = subprocess.run(
        [nm, "-n", str(elf)],
        check=True,
        capture_output=True,
        text=True,
    )
    found: dict[str, int] = {}
    wanted = {
        "account_agreement_enabled",
        "account_agreement_mutation_event_count",
        "account_agreement_mutation_event_overflow",
        "account_agreement_mutation_events",
    }
    for line in result.stdout.splitlines():
        fields = line.split()
        if len(fields) >= 3 and fields[-1] in wanted:
            found[fields[-1]] = int(fields[0], 16)
    missing = wanted - found.keys()
    if missing:
        fail(f"ELF is missing agreement symbols: {', '.join(sorted(missing))}")
    return found


def dump_payload(path: Path, start: int, length: int) -> bytes:
    data = path.read_bytes()
    if data[:8] != MAGIC:
        fail(f"bad dump magic in {path}")
    version, count = struct.unpack_from("<II", data, 8)
    if version != 1 or count != 1:
        fail(f"expected one version-1 dump range, got version={version} count={count}")
    address, dumped_length = struct.unpack_from("<QQ", data, 16)
    if address != start or dumped_length != length:
        fail(
            f"dump range mismatch: got {address:#x}:{dumped_length:#x}, "
            f"expected {start:#x}:{length:#x}"
        )
    payload = data[32:]
    if len(payload) != length:
        fail(f"truncated dump: got {len(payload)} bytes, expected {length}")
    return payload


def read_u64(payload: bytes, start: int, address: int) -> int:
    return U64.unpack_from(payload, address - start)[0]


def read_manifest(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for raw in path.read_text().splitlines():
        if not raw.strip():
            continue
        fields = raw.split("\t")
        if len(fields) < 4:
            fail(f"bad manifest row: {raw!r}")
        try:
            oracle_succ = int(fields[3])
        except (IndexError, ValueError) as exc:
            fail(f"bad oracle succ_bit in manifest row: {raw!r}")
            raise AssertionError from exc
        if oracle_succ not in (0, 1):
            fail(f"manifest oracle succ_bit must be 0 or 1: {raw!r}")
        rows.append({"label": fields[0], "input": fields[1], "oracle_succ": oracle_succ})
    if not rows:
        fail(f"manifest is empty: {path}")
    return rows


def resolve_input(manifest: Path, value: str) -> Path:
    path = Path(value)
    if path.is_absolute() and path.exists():
        return path
    if not path.is_absolute():
        candidate = manifest.parent / path
        if candidate.exists():
            return candidate
    # The pinned manifest commonly names /var/tmp while this checkout keeps
    # the same fixture tree under /tmp.
    if str(path).startswith("/var/tmp/"):
        alternate = Path("/tmp") / path.relative_to("/var/tmp")
        if alternate.exists():
            return alternate
    fail(f"input does not exist: {path}")


def select_cases(
    rows: list[dict[str, object]], labels: list[str], random_count: int, seed: int
) -> list[dict[str, object]]:
    by_label = {row["label"]: row for row in rows}
    selected: list[dict[str, object]] = []
    selected_labels: set[str] = set()
    for label in labels:
        if label in selected_labels:
            continue
        if label not in by_label:
            fail(f"named label not found: {label}")
        expected = STANDING_NAMED_EXPECTED.get(label)
        if expected is not None and by_label[label]["oracle_succ"] != expected:
            fail(
                f"named control {label} has oracle succ={by_label[label]['oracle_succ']}, "
                f"expected {expected}"
            )
        selected.append(by_label[label])
        selected_labels.add(label)
    candidates = [row for row in rows if row["label"] not in selected_labels]
    if random_count > len(candidates):
        fail(f"requested {random_count} random cases, only {len(candidates)} available")
    selected.extend(random.Random(seed).sample(candidates, random_count))
    return selected


def decode(payload: bytes, start: int, syms: dict[str, int]) -> dict[str, object]:
    names = [
        "account_agreement_mutation_event_count",
        "account_agreement_mutation_event_overflow",
    ]
    counters = {name: read_u64(payload, start, syms[name]) for name in names}
    mutation_events: list[dict[str, int | str]] = []
    mutation_count = min(
        counters["account_agreement_mutation_event_count"],
        MUTATION_EVENT_CAPACITY,
    )
    mutation_base = syms["account_agreement_mutation_events"]
    for index in range(mutation_count):
        offset = mutation_base - start + index * MUTATION_EVENT_SIZE
        metadata = read_u64(payload, start, mutation_base + index * MUTATION_EVENT_SIZE + 64)
        mutation_events.append(
            {
                "index": index,
                "address": payload[offset : offset + 20].hex(),
                "post_balance_le": payload[offset + 32 : offset + 64].hex(),
                "mutation_id": metadata & 0xFF,
                "depth": (metadata >> 8) & 0xFF,
                "sequence": read_u64(
                    payload,
                    start,
                    mutation_base + index * MUTATION_EVENT_SIZE + 72,
                ),
            }
        )
    counters["mutation_events"] = mutation_events
    return counters


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--elf", type=Path, required=True)
    parser.add_argument("--base-elf", type=Path)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--runner", type=Path, default=Path("scripts/spike/spike_run"))
    parser.add_argument("--nm", default="riscv64-unknown-elf-nm")
    parser.add_argument("--random-count", type=int, default=200)
    parser.add_argument("--seed", type=int, default=11586)
    parser.add_argument(
        "--label",
        action="append",
        default=list(STANDING_NAMED_CONTROLS),
        help="add a named control; standing controls are always included",
    )
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument(
        "--enable",
        action="store_true",
        help="arm mutation observation through SPIKE_INIT_WRITES",
    )
    args = parser.parse_args()

    if args.random_count < 0:
        fail("--random-count must be nonnegative")
    required_paths = [args.elf, args.manifest, args.runner]
    if args.base_elf:
        required_paths.append(args.base_elf)
    for path in required_paths:
        if not path.exists():
            fail(f"missing path: {path}")

    rows = read_manifest(args.manifest)
    cases = select_cases(rows, args.label, args.random_count, args.seed)
    syms = symbols(args.elf, args.nm)
    start = syms["account_agreement_mutation_event_count"]
    end = syms["account_agreement_mutation_events"] + MUTATION_EVENT_CAPACITY * MUTATION_EVENT_SIZE
    length = end - start
    if length <= 0:
        fail("mutation symbols are out of order")
    elf_sha = sha256(args.elf)
    base_elf_sha = sha256(args.base_elf) if args.base_elf else None
    root = args.work_dir or Path(tempfile.mkdtemp(prefix="account-agreement-"))
    root.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, object]] = []
    verdict_mismatches: list[dict[str, object]] = []

    for index, case in enumerate(cases):
        input_path = resolve_input(args.manifest, case["input"])
        dump_path = root / f"{index:04d}.dump"
        output_path = root / f"{index:04d}.out"
        env = os.environ.copy()
        env["SPIKE_DUMP_RANGES"] = f"{start:#x}:{length:#x}"
        env["SPIKE_DUMP_FILE"] = str(dump_path)
        if args.enable:
            # The production guest carries mutation observation hooks but
            # leaves them inert. Arm the runtime flag only for this process;
            # the address comes from the candidate ELF rather than a
            # hand-pinned layout constant.
            env["SPIKE_INIT_WRITES"] = f"{syms['account_agreement_enabled']:#x}:1"
        process = subprocess.run(
            [str(args.runner), str(args.elf), str(input_path), str(output_path)],
            env=env,
            capture_output=True,
            text=True,
            timeout=180,
        )
        if process.returncode != 0:
            fail(
                f"runner failed for {case['label']} (exit {process.returncode}):\n"
                f"{process.stderr[-2000:]}"
            )
        output_equal = None
        if args.base_elf:
            base_output_path = root / f"{index:04d}.base.out"
            base_process = subprocess.run(
                [str(args.runner), str(args.base_elf), str(input_path), str(base_output_path)],
                capture_output=True,
                text=True,
                timeout=180,
            )
            if base_process.returncode != 0:
                fail(
                    f"base runner failed for {case['label']} (exit {base_process.returncode}):\n"
                    f"{base_process.stderr[-2000:]}"
                )
            output_equal = output_path.read_bytes() == base_output_path.read_bytes()
        output_bytes = output_path.read_bytes()
        guest_succ = output_bytes[32] if len(output_bytes) > 32 else None
        expected_succ = STANDING_NAMED_EXPECTED.get(str(case["label"]))
        if expected_succ is not None and guest_succ != expected_succ:
            verdict_mismatches.append(
                {
                    "label": case["label"],
                    "oracle_succ": case["oracle_succ"],
                    "expected_succ": expected_succ,
                    "guest_succ": guest_succ,
                }
            )
        payload = dump_payload(dump_path, start, length)
        counters = decode(payload, start, syms)
        records.append(
            {
                "label": case["label"],
                "input": str(input_path),
                "oracle_succ": case["oracle_succ"],
                "expected_succ": expected_succ,
                "guest_succ": guest_succ,
                "counters": counters,
                "output_sha256": sha256(output_path),
                "base_output_equal": output_equal,
            }
        )
        if (index + 1) % 10 == 0 or index + 1 == len(cases):
            print(f"checked {index + 1}/{len(cases)}: {case['label']}", flush=True)

    mutation_observations = sum(
        int(record["counters"]["account_agreement_mutation_event_count"])
        for record in records
    )
    mutation_ids = sorted(
        {
            int(event["mutation_id"])
            for record in records
            for event in record["counters"]["mutation_events"]
        }
    )
    mutation_id_counts = {
        str(mutation_id): {
            "name": MUTATION_ID_NAMES.get(mutation_id, "unknown"),
            "count": sum(
                1
                for record in records
                for event in record["counters"]["mutation_events"]
                if int(event["mutation_id"]) == mutation_id
            ),
        }
        for mutation_id in sorted(MUTATION_ID_NAMES)
    }
    flip_set = [
        str(record["label"])
        for record in records
        if record["base_output_equal"] is False
    ]

    summary = {
        "elf": str(args.elf),
        "elf_sha256": elf_sha,
        "base_elf": str(args.base_elf) if args.base_elf else None,
        "base_elf_sha256": base_elf_sha,
        "manifest": str(args.manifest),
        "seed": args.seed,
        "random_count": args.random_count,
        "named_count": len(dict.fromkeys(args.label)),
        "named_controls": list(dict.fromkeys(args.label)),
        "dump_range": f"{start:#x}:{length:#x}",
        "cases": len(records),
        "flip_set": flip_set,
        "mutation_observations": mutation_observations,
        "mutation_ids": mutation_ids,
        "mutation_id_counts": mutation_id_counts,
        "output_differences": sum(
            1 for record in records if record["base_output_equal"] is False
        ),
        "verdict_mismatches": verdict_mismatches,
        "records": records,
    }
    report = args.report or root / "report.json"
    report.write_text(json.dumps(summary, indent=2) + "\n")
    print(
        f"agreement sweep: cases={len(records)} "
        f"mutation_observations={mutation_observations} "
        f"flip_set={summary['flip_set']} "
        f"output_differences={summary['output_differences']} "
        f"elf_sha256={elf_sha} report={report}"
    )
    if summary["output_differences"]:
        print("candidate/base output mismatch detected", file=sys.stderr)
        return 1
    if verdict_mismatches:
        print(
            "named control verdict mismatch detected: "
            + json.dumps(verdict_mismatches, sort_keys=True),
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
