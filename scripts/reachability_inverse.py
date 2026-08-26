#!/usr/bin/env python3
"""Measure a narrow entry precondition on a reachable routine.

This is the inverse companion to ``reachability_pilot.py``.  The positive
pilot records one exact entry/return event per row.  This probe reuses the
observed first return address, then asks whether the same routine is entered a
second time and reads one precondition cell at both entries.  It deliberately
does not call a second entry "matched" unless the first entry's return PC was
already observed by the positive pilot.

The probe is generic over a routine entry and one eight-byte memory cell.  It
is intended for stateful preconditions such as a scratch buffer that is zero
only on the first call.  A second entry with a nonzero cell is a measured
counterexample to treating that precondition as a property of every caller.
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


SAMPLE_FIELDS = (
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
    "target_reached",
    "first_return_pc",
    "first_cell",
    "second_entry",
    "second_cell",
    "first_zero",
    "second_zero",
    "debug_rc",
    "detail",
)

STOP_RE = re.compile(r"stopped pc=0x([0-9a-fA-F]+)")
RAW_HEX_RE = re.compile(r"^0x([0-9a-fA-F]{16})$")
RA_RE = re.compile(r"(?:^|;)ra=0x([0-9a-fA-F]+)(?:;|$)")


def _read_tsv(path: Path, fields: tuple[str, ...]) -> list[dict[str, str]]:
    lines = [line for line in path.read_text().splitlines() if line and not line.startswith("#")]
    if lines and lines[0].split("\t") == list(fields):
        lines = lines[1:]
    return list(csv.DictReader(lines, fieldnames=fields, delimiter="\t"))


def _observed_ra(detail: str) -> str | None:
    match = RA_RE.search(detail)
    return f"0x{int(match.group(1), 16):x}" if match else None


def _run(row: dict[str, str], ra: str | None, args: argparse.Namespace) -> dict[str, str]:
    case = row["case_id"]
    base = args.work_dir / case
    base.parent.mkdir(parents=True, exist_ok=True)
    if not ra:
        return {
            "case_id": case,
            "target_reached": "0",
            "first_return_pc": "-",
            "first_cell": "-",
            "second_entry": "0",
            "second_cell": "-",
            "first_zero": "-",
            "second_zero": "-",
            "debug_rc": "-",
            "detail": "positive-pilot-did-not-reach-entry",
        }

    command = base.with_suffix(".cmd")
    command.write_text(
        "\n".join(
            (
                f"until pc {args.entry_pc}",
                f"mem {args.cell_addr}",
                f"until pc {ra}",
                f"mem {args.cell_addr}",
                f"until pc {args.entry_pc}",
                f"mem {args.cell_addr}",
                "until halt",
            )
        )
        + "\n"
    )
    env = os.environ.copy()
    env["SPIKE_DEBUG_CMD"] = str(command)
    env.pop("SPIKE_BREAK_PC", None)
    output = base.with_suffix(".out")
    run = subprocess.run(
        [str(args.runner), str(args.elf), row["input_file"], str(output)],
        env=env,
        text=True,
        capture_output=True,
        timeout=args.timeout,
        check=False,
    )
    stops: list[int] = []
    cell_after_stop: list[int] = []
    lines = run.stderr.splitlines()
    for index, line in enumerate(lines):
        match = STOP_RE.search(line)
        if not match:
            continue
        stops.append(int(match.group(1), 16))
        # Every `mem` immediately follows a stop in this generated command.
        if index + 1 < len(lines):
            value = RAW_HEX_RE.match(lines[index + 1].strip())
            if value:
                cell_after_stop.append(int(value.group(1), 16))
            else:
                cell_after_stop.append(-1)
        else:
            cell_after_stop.append(-1)
    entry = int(args.entry_pc, 0)
    entry_cells = [value for pc, value in zip(stops, cell_after_stop) if pc == entry]
    first_cell = entry_cells[0] if entry_cells else -1
    second_cell = entry_cells[1] if len(entry_cells) > 1 else -1
    return {
        "case_id": case,
        "target_reached": "1",
        "first_return_pc": ra,
        "first_cell": f"0x{first_cell:016x}" if first_cell >= 0 else "-",
        "second_entry": "1" if len(entry_cells) >= 2 else "0",
        "second_cell": f"0x{second_cell:016x}" if second_cell >= 0 else "-",
        "first_zero": "1" if first_cell == 0 else ("0" if first_cell >= 0 else "-"),
        "second_zero": "1" if second_cell == 0 else ("0" if second_cell >= 0 else "-"),
        "debug_rc": str(run.returncode),
        "detail": "stops=" + ",".join(f"0x{pc:x}" for pc in stops),
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
    parser.add_argument("--cell-addr", required=True)
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()

    rows = {row["case_id"]: row for row in _read_tsv(args.sample, SAMPLE_FIELDS)}
    observations = _read_tsv(args.observations, (
        "case_id", "invocation_id", "backend", "routine", "grade", "arm",
        "phase", "condition_id", "target_reached", "predicate_holds",
        "row_complete", "entry_pc", "exit_pc", "call_depth", "detail",
    ))
    jobs: list[tuple[dict[str, str], str | None]] = []
    for observation in observations:
        row = rows[observation["case_id"]]
        jobs.append((row, _observed_ra(observation["detail"]) if observation["target_reached"] == "1" else None))

    results: list[dict[str, str]] = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = [pool.submit(_run, row, ra, args) for row, ra in jobs]
        for future in as_completed(futures):
            results.append(future.result())
    results.sort(key=lambda row: row["case_id"])
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as handle:
        handle.write("# schema=reachability-inverse-v1\n")
        handle.write(f"# sample={args.sample}\n")
        handle.write(f"# observations={args.observations}\n")
        handle.write(f"# elf_sha256={hashlib.sha256(args.elf.read_bytes()).hexdigest()}\n")
        writer = csv.DictWriter(handle, fieldnames=OBS_FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(results)

    reached = [row for row in results if row["target_reached"] == "1"]
    second = [row for row in reached if row["second_entry"] == "1"]
    second_nonzero = [row for row in second if row["second_zero"] == "0"]
    print(
        f"rows={len(results)} reached={len(reached)} second_entry={len(second)} "
        f"second_nonzero={len(second_nonzero)} out={args.out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
