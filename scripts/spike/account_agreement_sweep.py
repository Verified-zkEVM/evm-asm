#!/usr/bin/env python3
"""Run the runtime AccountWriteMap/AccountState agreement harness.

The guest writes counters plus 64-byte mismatch records into the diagnostic
arena.  The dump is deliberately one contiguous range: the spike dump driver
has unstable readback when adjacent ranges are requested separately.
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
EVENT_SIZE = 64
EVENT_CAPACITY = 4096
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
        "account_agreement_probe_count",
        "account_agreement_balance_probe_count",
        "account_agreement_nonce_probe_count",
        "account_agreement_no_row",
        "account_agreement_row_no_field",
        "account_agreement_live_field_absent",
        "account_agreement_present_agree",
        "account_agreement_mismatch_count",
        "agreement_event_count",
        "agreement_event_overflow",
        "agreement_events",
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


def read_manifest(path: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for raw in path.read_text().splitlines():
        if not raw.strip():
            continue
        fields = raw.split("\t")
        if len(fields) < 3:
            fail(f"bad manifest row: {raw!r}")
        rows.append({"label": fields[0], "input": fields[1]})
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
    rows: list[dict[str, str]], labels: list[str], random_count: int, seed: int
) -> list[dict[str, str]]:
    by_label = {row["label"]: row for row in rows}
    selected: list[dict[str, str]] = []
    selected_labels: set[str] = set()
    for label in labels:
        if label not in by_label:
            fail(f"named label not found: {label}")
        selected.append(by_label[label])
        selected_labels.add(label)
    candidates = [row for row in rows if row["label"] not in selected_labels]
    if random_count > len(candidates):
        fail(f"requested {random_count} random cases, only {len(candidates)} available")
    selected.extend(random.Random(seed).sample(candidates, random_count))
    return selected


def decode(
    payload: bytes, start: int, syms: dict[str, int]
) -> tuple[dict[str, int], list[dict[str, int | str]]]:
    names = [
        "account_agreement_probe_count",
        "account_agreement_balance_probe_count",
        "account_agreement_nonce_probe_count",
        "account_agreement_no_row",
        "account_agreement_row_no_field",
        "account_agreement_live_field_absent",
        "account_agreement_present_agree",
        "account_agreement_mismatch_count",
        "agreement_event_count",
        "agreement_event_overflow",
    ]
    counters = {name: read_u64(payload, start, syms[name]) for name in names}
    events: list[dict[str, int | str]] = []
    count = min(counters["agreement_event_count"], EVENT_CAPACITY)
    event_base = syms["agreement_events"]
    for index in range(count):
        offset = event_base - start + index * EVENT_SIZE
        address = payload[offset : offset + 32].hex()
        status = read_u64(payload, start, event_base + index * EVENT_SIZE + 32)
        events.append(
            {
                "index": index,
                "address": address,
                "verdict": status & 0xFF,
                "field": (status >> 8) & 0xFF,
                "reader": (status >> 16) & 0xFFFF,
                "tier": (status >> 32) & 0xFF,
                "limb": (status >> 40) & 0x7,
                "map_limb": read_u64(payload, start, event_base + index * EVENT_SIZE + 40),
                "live_limb": read_u64(payload, start, event_base + index * EVENT_SIZE + 48),
            }
        )
    return counters, events


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--elf", type=Path, required=True)
    parser.add_argument("--base-elf", type=Path)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--runner", type=Path, default=Path("scripts/spike/spike_run"))
    parser.add_argument("--nm", default="riscv64-unknown-elf-nm")
    parser.add_argument("--random-count", type=int, default=200)
    parser.add_argument("--seed", type=int, default=11586)
    parser.add_argument("--label", action="append", default=[])
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--allow-mismatch", action="store_true")
    parser.add_argument(
        "--enable",
        action="store_true",
        help="arm the agreement harness through SPIKE_INIT_WRITES",
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
    start = syms["account_agreement_probe_count"]
    end = syms["agreement_events"] + EVENT_CAPACITY * EVENT_SIZE
    length = end - start
    if length <= 0:
        fail("agreement symbols are out of order")
    elf_sha = sha256(args.elf)
    base_elf_sha = sha256(args.base_elf) if args.base_elf else None
    root = args.work_dir or Path(tempfile.mkdtemp(prefix="account-agreement-"))
    root.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, object]] = []

    for index, case in enumerate(cases):
        input_path = resolve_input(args.manifest, case["input"])
        dump_path = root / f"{index:04d}.dump"
        output_path = root / f"{index:04d}.out"
        env = os.environ.copy()
        env["SPIKE_DUMP_RANGES"] = f"{start:#x}:{length:#x}"
        env["SPIKE_DUMP_FILE"] = str(dump_path)
        if args.enable:
            # The production guest carries the harness but leaves it inert.
            # The sweep is the explicit debug consumer, so arm the runtime
            # flag only for this process.  The address comes from the
            # candidate ELF rather than from a hand-pinned layout constant.
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
        payload = dump_payload(dump_path, start, length)
        counters, events = decode(payload, start, syms)
        records.append(
            {
                "label": case["label"],
                "input": str(input_path),
                "counters": counters,
                "events": events,
                "output_sha256": sha256(output_path),
                "base_output_equal": output_equal,
            }
        )
        if (index + 1) % 10 == 0 or index + 1 == len(cases):
            print(f"checked {index + 1}/{len(cases)}: {case['label']}", flush=True)

    mismatches = [
        {"label": record["label"], "event": event}
        for record in records
        for event in record["events"]
        if event["verdict"] == 2
    ]
    summary = {
        "elf": str(args.elf),
        "elf_sha256": elf_sha,
        "base_elf": str(args.base_elf) if args.base_elf else None,
        "base_elf_sha256": base_elf_sha,
        "manifest": str(args.manifest),
        "seed": args.seed,
        "random_count": args.random_count,
        "named_count": len(args.label),
        "dump_range": f"{start:#x}:{length:#x}",
        "cases": len(records),
        "mismatch_events": len(mismatches),
        "balance_probe_invocations": sum(
            int(record["counters"]["account_agreement_balance_probe_count"])
            for record in records
        ),
        "nonce_probe_invocations": sum(
            int(record["counters"]["account_agreement_nonce_probe_count"])
            for record in records
        ),
        "output_differences": sum(
            1 for record in records if record["base_output_equal"] is False
        ),
        "mismatch_readers": sorted(
            {int(item["event"]["reader"]) for item in mismatches}
        ),
        "records": records,
    }
    report = args.report or root / "report.json"
    report.write_text(json.dumps(summary, indent=2) + "\n")
    print(
        f"agreement sweep: cases={len(records)} mismatches={len(mismatches)} "
        f"output_differences={summary['output_differences']} "
        f"elf_sha256={elf_sha} report={report}"
    )
    if summary["output_differences"]:
        print("candidate/base output mismatch detected", file=sys.stderr)
        return 1
    if mismatches and not args.allow_mismatch:
        print(json.dumps(mismatches[:20], indent=2), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
