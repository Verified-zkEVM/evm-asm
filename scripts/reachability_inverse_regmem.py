#!/usr/bin/env python3
"""Measure a bytesRegion-zero premise whose address is supplied in a register.

This is the dynamic-address companion to ``reachability_inverse.py``.  It is
for caller-visible preconditions such as
``bytesRegion outputBase (List.replicate 32 0)`` where ``outputBase`` is not a
fixed guest global.  The first debug pass records the register at each target
entry.  A second pass reads the four dwords at those recorded addresses at the
same entries, so the predicate is measured at the call boundary rather than
after the callee has written its output.
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
    "case_id", "label", "fixture_relpath", "input_file", "expected_success",
    "row_class", "input_len", "gas_limit", "fixture_family", "target_reached",
)
OBS_FIELDS = (
    "case_id", "target_reached", "first_output_base", "second_entry",
    "second_output_base", "first_zero", "second_zero", "first_words",
    "second_words", "debug_rc", "detail",
)

STOP_RE = re.compile(r"stopped pc=0x([0-9a-fA-F]+)")
HEX_RE = re.compile(r"^0x([0-9a-fA-F]{16})$")
RA_RE = re.compile(r"(?:^|;)ra=0x([0-9a-fA-F]+)(?:;|$)")


def read_tsv(path: Path, fields: tuple[str, ...]) -> list[dict[str, str]]:
    lines = [line for line in path.read_text().splitlines()
             if line and not line.startswith("#")]
    if lines and lines[0].split("\t") == list(fields):
        lines = lines[1:]
    return list(csv.DictReader(lines, fieldnames=fields, delimiter="\t"))


def parse_ra(detail: str) -> str | None:
    match = RA_RE.search(detail)
    return f"0x{int(match.group(1), 16):x}" if match else None


def run_debug(row: dict[str, str], commands: list[str], args: argparse.Namespace,
              suffix: str) -> subprocess.CompletedProcess[str]:
    stem = args.work_dir / f"{row['case_id']}.{suffix}"
    stem.parent.mkdir(parents=True, exist_ok=True)
    command = stem.with_suffix(".cmd")
    command.write_text("\n".join(commands) + "\n")
    env = os.environ.copy()
    env["SPIKE_DEBUG_CMD"] = str(command)
    env.pop("SPIKE_BREAK_PC", None)
    output = stem.with_suffix(".out")
    return subprocess.run(
        [str(args.runner), str(args.elf), row["input_file"], str(output)],
        env=env,
        text=True,
        capture_output=True,
        timeout=args.timeout,
        check=False,
    )


def parse_entry_regs(stderr: str, entry: int) -> list[int]:
    lines = stderr.splitlines()
    values: list[int] = []
    for index, line in enumerate(lines):
        match = STOP_RE.search(line)
        if not match or int(match.group(1), 16) != entry:
            continue
        # The generated command puts `reg <entry-reg>` immediately after each
        # entry stop.  The debugger prints one bare 64-bit hex line for it.
        for following in lines[index + 1:index + 4]:
            value = HEX_RE.match(following.strip())
            if value:
                values.append(int(value.group(1), 16))
                break
    return values


def parse_entry_words(stderr: str, entry: int) -> list[list[int]]:
    lines = stderr.splitlines()
    result: list[list[int]] = []
    for index, line in enumerate(lines):
        match = STOP_RE.search(line)
        if not match or int(match.group(1), 16) != entry:
            continue
        words: list[int] = []
        for following in lines[index + 1:index + 8]:
            value = HEX_RE.match(following.strip())
            if value:
                words.append(int(value.group(1), 16))
                if len(words) == 4:
                    break
        if len(words) == 4:
            result.append(words)
    return result


def run_one(row: dict[str, str], ra: str | None,
            args: argparse.Namespace) -> dict[str, str]:
    case = row["case_id"]
    entry = int(args.entry_pc, 0)
    if not ra:
        return {
            "case_id": case, "target_reached": "0", "first_output_base": "-",
            "second_entry": "0", "second_output_base": "-", "first_zero": "-",
            "second_zero": "-", "first_words": "-", "second_words": "-",
            "debug_rc": "-", "detail": "positive-pilot-did-not-reach-entry",
        }

    # Pass 1: record x12 (a2, the KSS output pointer) at each entry.  The
    # first return PC is known from the positive pilot; after the second entry
    # we can stop at halt even if a later callsite has a different return PC.
    reg_cmd = [f"until pc {args.entry_pc}", f"reg {args.entry_reg}",
               f"until pc {ra}", f"until pc {args.entry_pc}",
               f"reg {args.entry_reg}", "until halt"]
    regs_run = run_debug(row, reg_cmd, args, "reg")
    bases = parse_entry_regs(regs_run.stderr, entry)
    if not bases:
        return {
            "case_id": case, "target_reached": "1", "first_output_base": "-",
            "second_entry": "0", "second_output_base": "-", "first_zero": "-",
            "second_zero": "-", "first_words": "-", "second_words": "-",
            "debug_rc": str(regs_run.returncode), "detail": "entry-reg-not-observed",
        }

    # Pass 2: read the addresses discovered above at the corresponding entry.
    # A single invocation is enough for the first and second entry.  If a row
    # has only one call, the final `until halt` is reached from that call.
    addr0 = bases[0]
    mem_cmd = [f"until pc {args.entry_pc}"]
    for offset in range(0, 32, 8):
        mem_cmd.append(f"mem 0x{addr0 + offset:x}")
    if len(bases) >= 2:
        addr1 = bases[1]
        mem_cmd.extend([f"until pc {ra}", f"until pc {args.entry_pc}"])
        for offset in range(0, 32, 8):
            mem_cmd.append(f"mem 0x{addr1 + offset:x}")
    mem_cmd.append("until halt")
    mem_run = run_debug(row, mem_cmd, args, "mem")
    words = parse_entry_words(mem_run.stderr, entry)
    first_words = words[0] if words else []
    second_words = words[1] if len(words) >= 2 else []
    first_zero = len(first_words) == 4 and all(value == 0 for value in first_words)
    second_zero = len(second_words) == 4 and all(value == 0 for value in second_words)
    return {
        "case_id": case,
        "target_reached": "1",
        "first_output_base": f"0x{addr0:016x}",
        "second_entry": "1" if len(bases) >= 2 else "0",
        "second_output_base": (f"0x{bases[1]:016x}" if len(bases) >= 2 else "-"),
        "first_zero": "1" if first_zero else ("0" if first_words else "-"),
        "second_zero": "1" if second_zero else ("0" if second_words else "-"),
        "first_words": ",".join(f"0x{x:016x}" for x in first_words) or "-",
        "second_words": ",".join(f"0x{x:016x}" for x in second_words) or "-",
        "debug_rc": f"reg={regs_run.returncode};mem={mem_run.returncode}",
        "detail": f"entry_count={len(bases)};reg_stderr={regs_run.stderr.count('stopped pc=')};mem_stderr={mem_run.stderr.count('stopped pc=')}",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sample", required=True, type=Path)
    parser.add_argument("--observations", required=True, type=Path)
    parser.add_argument("--elf", required=True, type=Path)
    parser.add_argument("--runner", required=True, type=Path)
    parser.add_argument("--work-dir", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--entry-pc", required=True)
    parser.add_argument("--entry-reg", default="x12")
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()

    rows = {row["case_id"]: row for row in read_tsv(args.sample, ROW_FIELDS)}
    observations = read_tsv(args.observations, (
        "case_id", "invocation_id", "backend", "routine", "grade", "arm",
        "phase", "condition_id", "target_reached", "predicate_holds",
        "row_complete", "entry_pc", "exit_pc", "call_depth", "detail",
    ))
    jobs: list[tuple[dict[str, str], str | None]] = []
    for observation in observations:
        row = rows[observation["case_id"]]
        ra = parse_ra(observation["detail"]) if observation["target_reached"] == "1" else None
        jobs.append((row, ra))

    results: list[dict[str, str]] = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = [pool.submit(run_one, row, ra, args) for row, ra in jobs]
        for future in as_completed(futures):
            results.append(future.result())
    results.sort(key=lambda row: row["case_id"])
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as handle:
        handle.write("# schema=reachability-inverse-regmem-v1\n")
        handle.write(f"# sample={args.sample}\n")
        handle.write(f"# observations={args.observations}\n")
        handle.write(f"# elf_sha256={hashlib.sha256(args.elf.read_bytes()).hexdigest()}\n")
        writer = csv.DictWriter(handle, fieldnames=OBS_FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(results)

    reached = [row for row in results if row["target_reached"] == "1"]
    second = [row for row in reached if row["second_entry"] == "1"]
    first_zero = [row for row in reached if row["first_zero"] == "1"]
    second_zero = [row for row in second if row["second_zero"] == "1"]
    print(
        f"rows={len(results)} reached={len(reached)} second_entry={len(second)} "
        f"first_zero={len(first_zero)} second_zero={len(second_zero)} out={args.out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
