#!/usr/bin/env python3
"""Host-only EIP-8037 gas-dimension differential (#11808 tooling).

Compares guest BSS per-tx arrays against SpecRef BlockOutput accumulators:

  guest regular = sum(bvgr_block_gas_increments[0..n))
  guest state   = sum(bvgr_tx_total_state_gas[0..n))
  specref       = BlockOutput.blockGasUsed / blockStateGasUsed after apply_body

NO guest edits. SPIKE_DUMP_RANGES peeks existing BSS; SpecRef --gas-dims reads
the same apply_body fields the oracle max-compares (not a side recomputation).

Limits (printed every run):
  - Agreement on summands does NOT certify eip8037_block_gas_used's max/compare
    against header.gas_used (that path is not re-proven here).
  - Optional guest bv_exact_expected_gas_used is reported for local consistency
    with max(guest_regular, guest_state) only.
  - Rows where SpecRef apply_body never finishes have no specref dims.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import struct
import subprocess
import sys
from pathlib import Path
from typing import Any, NoReturn

MAGIC = b"SPKDMP01"
U64 = struct.Struct("<Q")
U32 = struct.Struct("<I")

# Full per-tx u64 arena (bvMtxFullTxCap * 8). Dump whole arena; sum uses count.
ARENA_BYTES_DEFAULT = 16666 * 8

CANNOT_SEE = [
    "eip8037 max/equality vs header.gas_used (only summands compared)",
    "per-tx regular recomputation inside ExactGas from settle meters",
    "rows where apply_body never finishes (no SpecRef dims)",
]


def fail(message: str) -> NoReturn:
    raise SystemExit(f"FAIL: {message}")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def nm_symbols(elf: Path) -> dict[str, int]:
    for nm in ("riscv64-unknown-elf-nm", "riscv64-elf-nm", "nm"):
        try:
            proc = subprocess.run(
                [nm, "-n", str(elf)],
                check=True,
                capture_output=True,
                text=True,
            )
            break
        except (OSError, subprocess.CalledProcessError):
            proc = None  # type: ignore[assignment]
    if proc is None:
        fail(f"nm failed for {elf}")
    result: dict[str, int] = {}
    for raw in proc.stdout.splitlines():
        fields = raw.split()
        if len(fields) == 3:
            try:
                result[fields[2]] = int(fields[0], 16)
            except ValueError:
                pass
    return result


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
    return result


def read_at(ranges: dict[int, bytes], address: int, length: int) -> bytes:
    for base, data in ranges.items():
        if base <= address and address + length <= base + len(data):
            offset = address - base
            return data[offset : offset + length]
    fail(f"dump does not cover 0x{address:x}+{length}")


def u64_at(ranges: dict[int, bytes], address: int) -> int:
    return U64.unpack(read_at(ranges, address, 8))[0]


def sum_u64_array(ranges: dict[int, bytes], base: int, count: int) -> int:
    total = 0
    raw = read_at(ranges, base, count * 8)
    for i in range(count):
        total += U64.unpack_from(raw, i * 8)[0]
    return total


def run_guest_dims(
    spike: Path,
    elf: Path,
    input_path: Path,
    out_dir: Path,
    symbols: dict[str, int],
    arena_bytes: int,
) -> dict[str, Any]:
    required = [
        "bvgr_arena_tx_count",
        "bvgr_block_gas_increments",
        "bvgr_tx_total_state_gas",
    ]
    missing = [n for n in required if n not in symbols]
    if missing:
        fail(f"guest ELF missing symbols: {', '.join(missing)}")

    ranges_spec = [
        (symbols["bvgr_arena_tx_count"], 8),
        (symbols["bvgr_block_gas_increments"], arena_bytes),
        (symbols["bvgr_tx_total_state_gas"], arena_bytes),
    ]
    for opt in ("bv_exact_expected_gas_used", "bv_exact_header_gas_used"):
        if opt in symbols:
            ranges_spec.append((symbols[opt], 8))

    dump_env = ",".join(f"0x{a:x}:{n}" for a, n in ranges_spec)
    out_dir.mkdir(parents=True, exist_ok=True)
    dump_file = out_dir / "gas-dims.dump"
    output_file = out_dir / "guest.output"
    env = os.environ.copy()
    env["SPIKE_DUMP_RANGES"] = dump_env
    env["SPIKE_DUMP_FILE"] = str(dump_file)
    proc = subprocess.run(
        [str(spike), str(elf), str(input_path), str(output_file)],
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return {
            "ok": False,
            "error": f"spike_run exit {proc.returncode}",
            "stderr": (proc.stderr or "")[-500:],
        }
    if not dump_file.is_file():
        return {"ok": False, "error": "no SPIKE dump produced"}

    dumped = read_dump(dump_file)
    tx_count = u64_at(dumped, symbols["bvgr_arena_tx_count"])
    if tx_count * 8 > arena_bytes:
        return {
            "ok": False,
            "error": f"tx_count {tx_count} exceeds arena {arena_bytes // 8}",
        }
    regular = sum_u64_array(dumped, symbols["bvgr_block_gas_increments"], tx_count)
    state = sum_u64_array(dumped, symbols["bvgr_tx_total_state_gas"], tx_count)
    guest_succ = None
    if output_file.is_file() and output_file.stat().st_size >= 33:
        guest_succ = output_file.read_bytes()[32]
    result: dict[str, Any] = {
        "ok": True,
        "tx_count": tx_count,
        "regular": regular,
        "state": state,
        "max": max(regular, state),
        "guest_succ": guest_succ,
    }
    if "bv_exact_expected_gas_used" in symbols:
        result["exact_expected"] = u64_at(dumped, symbols["bv_exact_expected_gas_used"])
        result["exact_matches_max"] = result["exact_expected"] == result["max"]
    if "bv_exact_header_gas_used" in symbols:
        result["header_gas_used"] = u64_at(dumped, symbols["bv_exact_header_gas_used"])
    return result


def run_specref_dims(specref: Path, input_path: Path) -> dict[str, Any]:
    proc = subprocess.run(
        [str(specref), "--gas-dims", str(input_path)],
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return {
            "ok": False,
            "error": f"specref exit {proc.returncode}",
            "stderr": (proc.stderr or "").strip()[-500:],
        }
    line = (proc.stdout or "").strip().splitlines()[-1]
    try:
        data = json.loads(line)
    except json.JSONDecodeError as exc:
        return {"ok": False, "error": f"bad specref json: {exc}", "stdout": line[:200]}
    data["ok"] = True
    return data


def compare_one(
    spike: Path,
    elf: Path,
    specref: Path,
    input_path: Path,
    out_dir: Path,
    symbols: dict[str, int],
    arena_bytes: int,
    label: str,
) -> dict[str, Any]:
    guest = run_guest_dims(spike, elf, input_path, out_dir, symbols, arena_bytes)
    specref_d = run_specref_dims(specref, input_path)
    row: dict[str, Any] = {
        "label": label,
        "input": str(input_path),
        "input_sha256": sha256(input_path),
        "guest": guest,
        "specref": specref_d,
    }
    if not specref_d.get("ok"):
        # SpecRef apply_body never finished — no dims to compare. Guest early
        # reject with empty arena is expected-invalid, not a dimension mismatch.
        if (
            guest.get("ok")
            and guest.get("tx_count") == 0
            and guest.get("guest_succ") in (0, None)
        ):
            row["status"] = "SKIP_NO_SPECREF_DIMS"
            row["diverge"] = False
            return row
        row["status"] = "ERROR"
        row["diverge"] = False
        return row
    if not guest.get("ok"):
        row["status"] = "ERROR"
        row["diverge"] = False
        return row
    reg_eq = guest["regular"] == specref_d["regular"]
    st_eq = guest["state"] == specref_d["state"]
    row["regular_eq"] = reg_eq
    row["state_eq"] = st_eq
    row["diverge"] = not (reg_eq and st_eq)
    row["status"] = "DIVERGE" if row["diverge"] else "AGREE"
    return row


def discover_inputs(path: Path) -> list[tuple[str, Path]]:
    if path.is_file() and path.suffix == ".input":
        return [(path.stem, path)]
    if path.is_file() and path.name == "manifest.tsv":
        rows: list[tuple[str, Path]] = []
        for raw in path.read_text().splitlines():
            if not raw.strip():
                continue
            fields = raw.split("\t")
            label = fields[0]
            inp = Path(fields[1])
            if not inp.is_absolute():
                inp = path.parent / inp
            rows.append((label, inp))
        return rows
    if path.is_dir():
        return sorted((p.stem, p) for p in path.glob("*.input"))
    fail(f"not an input, manifest.tsv, or directory: {path}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--guest-elf", type=Path, required=True)
    ap.add_argument("--spike", type=Path, default=Path("scripts/spike/spike_run"))
    ap.add_argument(
        "--specref",
        type=Path,
        default=Path(".lake/build/bin/specref-eest-check"),
    )
    ap.add_argument(
        "--inputs",
        type=Path,
        required=True,
        help="single .input, manifest.tsv, or directory of *.input",
    )
    ap.add_argument("--out-dir", type=Path, default=Path("/tmp/grok-11808-gas-dims"))
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--arena-bytes", type=int, default=ARENA_BYTES_DEFAULT)
    ap.add_argument(
        "--stop-on-diverge",
        action="store_true",
        help="exit 2 on first divergence (still writes partial report)",
    )
    args = ap.parse_args()

    if not args.guest_elf.is_file():
        fail(f"guest elf missing: {args.guest_elf}")
    if not args.spike.is_file():
        fail(f"spike_run missing: {args.spike}")
    if not args.specref.is_file():
        fail(f"specref-eest-check missing: {args.specref} (lake build specref-eest-check)")

    symbols = nm_symbols(args.guest_elf)
    cases = discover_inputs(args.inputs)
    if not cases:
        fail("no inputs discovered")

    args.out_dir.mkdir(parents=True, exist_ok=True)
    report_path = args.out_dir / "report.jsonl"
    summary_path = args.out_dir / "summary.json"

    results: list[dict[str, Any]] = []
    diverge: list[dict[str, Any]] = []
    errors: list[dict[str, Any]] = []
    skips: list[dict[str, Any]] = []

    def work(item: tuple[str, Path]) -> dict[str, Any]:
        label, inp = item
        case_dir = args.out_dir / "cases" / label
        return compare_one(
            args.spike,
            args.guest_elf,
            args.specref,
            inp,
            case_dir,
            symbols,
            args.arena_bytes,
            label,
        )

    with report_path.open("w") as report_f:
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            futs = {pool.submit(work, c): c[0] for c in cases}
            for fut in concurrent.futures.as_completed(futs):
                row = fut.result()
                results.append(row)
                report_f.write(json.dumps(row, sort_keys=True) + "\n")
                report_f.flush()
                status = row.get("status")
                if status == "DIVERGE":
                    diverge.append(row)
                    print(
                        f"DIVERGE {row['label']}: "
                        f"guest reg/st={row['guest'].get('regular')}/{row['guest'].get('state')} "
                        f"specref reg/st={row['specref'].get('regular')}/{row['specref'].get('state')}",
                        flush=True,
                    )
                    if args.stop_on_diverge:
                        pool.shutdown(wait=False, cancel_futures=True)
                        break
                elif status == "SKIP_NO_SPECREF_DIMS":
                    skips.append(row)
                    print(f"SKIP_NO_SPECREF_DIMS {row['label']}", flush=True)
                elif status == "ERROR":
                    errors.append(row)
                    print(
                        f"ERROR {row['label']}: guest={row['guest'].get('error')} "
                        f"specref={row['specref'].get('error')}",
                        flush=True,
                    )
                else:
                    print(f"AGREE {row['label']}", flush=True)

    summary = {
        "tool": "gas_dims_diff",
        "issue": 11808,
        "guest_elf": str(args.guest_elf),
        "guest_elf_sha256": sha256(args.guest_elf),
        "n_cases": len(cases),
        "n_scored": len(results),
        "n_agree": sum(1 for r in results if r.get("status") == "AGREE"),
        "n_diverge": len(diverge),
        "n_skip_no_specref_dims": len(skips),
        "n_error": len(errors),
        "divergence_set": [
            {
                "label": r["label"],
                "input_sha256": r["input_sha256"],
                "guest_regular": r["guest"].get("regular"),
                "guest_state": r["guest"].get("state"),
                "specref_regular": r["specref"].get("regular"),
                "specref_state": r["specref"].get("state"),
            }
            for r in diverge
        ],
        "skip_labels": [r["label"] for r in skips],
        "error_labels": [r["label"] for r in errors],
        "cannot_see": CANNOT_SEE,
        "specref_source": "BlockOutput.apply_body_fields (same max inputs as oracle)",
        "guest_source": "sum BSS bvgr_block_gas_increments / bvgr_tx_total_state_gas",
        "zero_bar": "divergence set must be empty",
    }
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))

    if diverge:
        print(
            "STOP: nonempty divergence set — message coord before write-up "
            f"({len(diverge)} rows). summary={summary_path}",
            file=sys.stderr,
        )
        return 2
    if errors and len(errors) == len(results):
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
