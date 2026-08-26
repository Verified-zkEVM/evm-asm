#!/usr/bin/env python3
"""Run a bounded Spike reachability pilot against a row split.

The pilot is deliberately a positive-control check: ``SPIKE_BREAK_PC`` proves
that the fresh linked image reaches the selected routine, while a second run
uses ``SPIKE_DEBUG_CMD`` to match the entry's saved return address.  This keeps
the corpus denominator separate from target reachability; rows which halt
before the routine are recorded as not reached, never as a failed predicate.

No Lean or generated guest files are touched.  The output is the
``reachability-observation-v1`` TSV consumed by ``reachability_report.py``.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import os
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


ROW_FIELDS = (
    "case_id",
    "label",
    "fixture_relpath",
    "input_file",
    "expected_success",
    "row_class",
    "input_len",
    "gas_limit",
    "fixture_family",
    "target_reached",
)
OBS_FIELDS = (
    "case_id",
    "invocation_id",
    "backend",
    "routine",
    "grade",
    "arm",
    "phase",
    "condition_id",
    "target_reached",
    "predicate_holds",
    "row_complete",
    "entry_pc",
    "exit_pc",
    "call_depth",
    "detail",
)

HIT_RE = re.compile(r"SPIKE_BREAK_PC hit pc=0x([0-9a-fA-F]+)")
REG_RE = re.compile(r"\s+ra:\s+0x([0-9a-fA-F]+).*?sp:\s+0x([0-9a-fA-F]+)")
STOP_RE = re.compile(r"stopped pc=0x([0-9a-fA-F]+)")


def read_rows(path: Path) -> list[dict[str, str]]:
    lines = [line for line in path.read_text().splitlines() if line and not line.startswith("#")]
    if not lines or lines[0].split("\t") != list(ROW_FIELDS):
        raise SystemExit(f"{path}: expected reachability-row-v1 header")
    reader = csv.DictReader(lines[1:], fieldnames=ROW_FIELDS, delimiter="\t")
    rows = list(reader)
    if not rows:
        raise SystemExit(f"{path}: empty sample")
    return rows


def run_one(row: dict[str, str], args: argparse.Namespace) -> dict[str, str]:
    case = row["case_id"]
    stem = f"{case}.0"
    out_path = args.work_dir / f"{stem}.out"
    env = os.environ.copy()
    env["SPIKE_BREAK_PC"] = args.entry_pc
    env.pop("SPIKE_DEBUG_CMD", None)
    first = subprocess.run(
        [str(args.runner), str(args.elf), row["input_file"], str(out_path)],
        env=env,
        text=True,
        capture_output=True,
        timeout=args.timeout,
        check=False,
    )
    hit = HIT_RE.search(first.stderr)
    entry_pc = f"0x{int(hit.group(1), 16):x}" if hit else "-"
    ra = "-"
    sp = "-"
    # print_regs emits one line containing both RA and SP.
    for match in REG_RE.finditer(first.stderr):
        ra = f"0x{int(match.group(1), 16):x}"
        sp = f"0x{int(match.group(2), 16):x}"
        break
    exit_pc = "-"
    exit_sp = "-"
    exit_ok = False
    debug_rc = None
    debug_detail = ""
    if hit:
        # The runner's debug language is intentionally static.  Substituting
        # the observed RA makes the second run check the actual callsite, not
        # a guessed global return address.
        debug_path = args.work_dir / f"{stem}.cmd"
        debug_path.write_text(
            "\n".join(
                (
                    f"until pc {args.entry_pc}",
                    "reg",
                    f"until pc {ra}",
                    "pc",
                    "reg",
                    "until halt",
                )
            )
            + "\n"
        )
        debug_env = os.environ.copy()
        debug_env["SPIKE_DEBUG_CMD"] = str(debug_path)
        debug_env.pop("SPIKE_BREAK_PC", None)
        debug_out = args.work_dir / f"{stem}.debug.out"
        debug = subprocess.run(
            [str(args.runner), str(args.elf), row["input_file"], str(debug_out)],
            env=debug_env,
            text=True,
            capture_output=True,
            timeout=args.timeout,
            check=False,
        )
        debug_rc = debug.returncode
        stops = [int(value, 16) for value in STOP_RE.findall(debug.stderr)]
        # First stop is the entry; second is the literal RA return target.
        if len(stops) >= 2 and stops[0] == int(args.entry_pc, 0) and stops[1] == int(ra, 0):
            exit_pc = f"0x{stops[1]:x}"
            exit_ok = True
        # A second ``reg sp`` is the post-return stack pointer.  Keeping it in
        # detail lets the report establish that this leaf did not change depth.
        regs = list(REG_RE.finditer(debug.stderr))
        if len(regs) >= 2:
            exit_sp = f"0x{int(regs[1].group(2), 16):x}"
        debug_detail = f"debug_rc={debug_rc};stops={','.join(f'0x{x:x}' for x in stops)}"
    complete = first.returncode == 0 and (not hit or exit_ok and debug_rc == 0)
    predicate = (not hit) or (complete and exit_ok)
    digest = "-"
    if out_path.exists():
        digest = hashlib.sha256(out_path.read_bytes()).hexdigest()
    detail = (
        f"runner_rc={first.returncode};ra={ra};entry_sp={sp};exit_sp={exit_sp};"
        f"output_sha256={digest};{debug_detail}"
    )
    return {
        "case_id": case,
        "invocation_id": stem,
        "backend": "spike",
        "routine": args.routine,
        "grade": args.grade,
        "arm": "positive-control",
        "phase": "entry-exit",
        "condition_id": "entry-pc-and-return-address",
        "target_reached": "1" if hit else "0",
        "predicate_holds": "1" if predicate else "0",
        "row_complete": "1" if complete else "0",
        "entry_pc": entry_pc,
        "exit_pc": exit_pc,
        "call_depth": "leaf-sp-unchanged" if hit and exit_sp == sp else ("not-reached" if not hit else "unknown"),
        "detail": detail,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sample", required=True, type=Path)
    parser.add_argument("--elf", required=True, type=Path)
    parser.add_argument("--runner", required=True, type=Path)
    parser.add_argument("--work-dir", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--entry-pc", required=True)
    parser.add_argument("--routine", default="rlp_walk_init")
    parser.add_argument("--grade", default="proven")
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    args.work_dir.mkdir(parents=True, exist_ok=True)
    rows = read_rows(args.sample)
    results: list[dict[str, str]] = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = [pool.submit(run_one, row, args) for row in rows]
        for future in as_completed(futures):
            results.append(future.result())
    results.sort(key=lambda row: row["case_id"])
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as handle:
        handle.write("# schema=reachability-observation-v1\n")
        handle.write(f"# sample={args.sample}\n")
        handle.write(f"# elf_sha256={hashlib.sha256(args.elf.read_bytes()).hexdigest()}\n")
        writer = csv.DictWriter(handle, fieldnames=OBS_FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(results)
    reached = sum(row["target_reached"] == "1" for row in results)
    matched = sum(row["predicate_holds"] == "1" for row in results if row["target_reached"] == "1")
    print(f"rows={len(results)} reached={reached} entry_exit_matched={matched} out={args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
