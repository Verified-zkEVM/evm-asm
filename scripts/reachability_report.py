#!/usr/bin/env python3
"""Build reachability-pilot row splits and condition reports.

The EEST stateless manifest already records the reference ``succ`` byte.  This
tool makes that classification explicit before any instrumentation runs:
every row is labelled ``valid`` or ``invalid`` and the report keeps separate
denominators for the two populations.  A condition on a rejection path must
never turn ``0 observations`` into an unqualified reachability claim when the
target check was never reached by the invalid rows.

The tool is deliberately external to Lean.  It consumes the eight-column
``eest-stateless-to-input.py`` manifest and a small observation TSV emitted by
an instrumentation harness.  No probe modules are needed.

Row split schema (``reachability-row-v1``)::

    case_id  label  fixture_relpath  input_file  expected_success  row_class
    input_len  gas_limit  fixture_family  target_reached

Observation schema (``reachability-observation-v1``)::

    case_id  invocation_id  backend  routine  grade  arm  phase condition_id
    target_reached  predicate_holds  row_complete  entry_pc  exit_pc
    call_depth  detail

``predicate_holds`` and ``target_reached`` are ``0``/``1``.  One row may have
multiple invocations; ``row_complete`` is repeated on the terminal event for
that case.  Backend disagreement is represented by one observation per
backend with the same case/invocation/condition and conflicting values.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator


MANIFEST_FIELDS = (
    "label",
    "input_file",
    "expected_hex",
    "succ_bit",
    "input_len",
    "gas_limit",
    "fixture_relpath",
    "case_id",
)
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


@dataclass(frozen=True)
class Row:
    case_id: str
    label: str
    fixture_relpath: str
    input_file: str
    expected_success: int
    input_len: int
    gas_limit: int

    @property
    def row_class(self) -> str:
        return "valid" if self.expected_success else "invalid"

    @property
    def fixture_family(self) -> str:
        # Keep inherited fork paths visible.  The first directory after the
        # fork root is the smallest stable family key in the EEST tree.
        parts = self.fixture_relpath.split("/")
        if len(parts) >= 4:
            return "/".join(parts[:4])
        return self.fixture_relpath


def _die(message: str) -> "NoReturn":
    raise SystemExit(f"error: {message}")


def _read_tsv(path: Path, fields: tuple[str, ...]) -> Iterator[dict[str, str]]:
    with path.open(newline="") as handle:
        # Metadata comments are allowed at the beginning of generated files.
        lines = [line for line in handle if line.strip() and not line.startswith("#")]
        if lines and lines[0].rstrip("\n").split("\t") == list(fields):
            lines = lines[1:]
        rows = iter(lines)
        reader = csv.DictReader(rows, fieldnames=fields, delimiter="\t")
        for row in reader:
            if len(row) != len(fields):
                _die(f"{path}: malformed TSV row")
            yield row


def read_manifest(path: Path) -> list[Row]:
    rows: list[Row] = []
    seen: set[str] = set()
    for raw in _read_tsv(path, MANIFEST_FIELDS):
        try:
            expected = raw["expected_hex"].removeprefix("0x")
            succ = int(raw["succ_bit"])
            input_len = int(raw["input_len"])
            gas_limit = int(raw["gas_limit"])
        except ValueError as exc:
            _die(f"{path}: malformed numeric manifest field: {exc}")
        case_id = raw["case_id"]
        if succ not in (0, 1):
            _die(f"{path}: succ_bit must be 0 or 1 for {case_id}")
        if len(expected) < 66:
            _die(f"{path}: expected output too short for {case_id}")
        if int(expected[64:66], 16) != succ:
            _die(
                f"{path}: succ_bit disagrees with expected output byte for {case_id}"
            )
        if case_id in seen:
            _die(f"{path}: duplicate case_id {case_id}")
        seen.add(case_id)
        rows.append(
            Row(
                case_id=case_id,
                label=raw["label"],
                fixture_relpath=raw["fixture_relpath"],
                input_file=raw["input_file"],
                expected_success=succ,
                input_len=input_len,
                gas_limit=gas_limit,
            )
        )
    if not rows:
        _die(f"{path}: empty manifest")
    return rows


def write_split(rows: Iterable[Row], out_path: Path, source_manifest: Path) -> dict:
    rows = list(rows)
    counts = Counter(row.row_class for row in rows)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", newline="") as handle:
        handle.write("# schema=reachability-row-v1\n")
        handle.write(f"# source_manifest={source_manifest}\n")
        writer = csv.DictWriter(handle, fieldnames=ROW_FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "case_id": row.case_id,
                    "label": row.label,
                    "fixture_relpath": row.fixture_relpath,
                    "input_file": row.input_file,
                    "expected_success": row.expected_success,
                    "row_class": row.row_class,
                    "input_len": row.input_len,
                    "gas_limit": row.gas_limit,
                    "fixture_family": row.fixture_family,
                    # This is intentionally unknown before instrumentation.
                    # A false value here would manufacture a reachability claim.
                    "target_reached": "unknown",
                }
            )
    return {
        "schema": "reachability-row-v1",
        "source_manifest": str(source_manifest),
        "rows_total": len(rows),
        "valid_rows": counts["valid"],
        "invalid_rows": counts["invalid"],
        "target_reached": "unknown_before_instrumentation",
    }


def _rank(seed: int, case_id: str) -> bytes:
    return hashlib.sha256(f"{seed}\0{case_id}".encode()).digest()


def stratified_sample(rows: list[Row], size: int, seed: int) -> list[Row]:
    if size <= 0:
        _die("sample size must be positive")
    if size > len(rows):
        _die(f"sample size {size} exceeds corpus size {len(rows)}")
    by_class: dict[str, list[Row]] = defaultdict(list)
    for row in rows:
        by_class[row.row_class].append(row)
    if not by_class["valid"] or not by_class["invalid"]:
        _die("stratified sample requires both valid and invalid rows")

    # Keep the valid/invalid split visible in the sample.  When the requested
    # size is odd, the extra row goes to the larger population.
    quotas = {
        "valid": size // 2,
        "invalid": size - size // 2,
    }
    selected: list[Row] = []
    for cls, quota in quotas.items():
        groups: dict[str, list[Row]] = defaultdict(list)
        for row in by_class[cls]:
            groups[row.fixture_family].append(row)
        for group in groups.values():
            group.sort(key=lambda row: _rank(seed, row.case_id))
        # Round-robin the families so the pilot is not a front-loaded family
        # sample.  The rank within each family remains deterministic.
        ordered_groups = sorted(groups.values(), key=lambda group: _rank(seed, group[0].case_id))
        picked: list[Row] = []
        while len(picked) < quota:
            progressed = False
            for group in ordered_groups:
                if group and len(picked) < quota:
                    picked.append(group.pop(0))
                    progressed = True
            if not progressed:
                break
        if len(picked) != quota:
            _die(f"could not select {quota} {cls} rows")
        selected.extend(picked)
    selected.sort(key=lambda row: _rank(seed, row.case_id))
    return selected


def write_sample(rows: list[Row], out_path: Path, source_split: Path, seed: int) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", newline="") as handle:
        handle.write("# schema=reachability-row-v1-sample\n")
        handle.write(f"# source_split={source_split}\n")
        handle.write(f"# seed={seed}\n")
        writer = csv.DictWriter(handle, fieldnames=ROW_FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "case_id": row.case_id,
                    "label": row.label,
                    "fixture_relpath": row.fixture_relpath,
                    "input_file": row.input_file,
                    "expected_success": row.expected_success,
                    "row_class": row.row_class,
                    "input_len": row.input_len,
                    "gas_limit": row.gas_limit,
                    "fixture_family": row.fixture_family,
                    "target_reached": "unknown",
                }
            )


def _load_rows(path: Path) -> dict[str, dict[str, str]]:
    rows = {}
    for row in _read_tsv(path, ROW_FIELDS):
        case_id = row["case_id"]
        if case_id in rows:
            _die(f"{path}: duplicate case_id {case_id}")
        rows[case_id] = row
    if not rows:
        _die(f"{path}: empty row split")
    return rows


def summarize(rows_path: Path, observations_path: Path, out_path: Path) -> None:
    rows = _load_rows(rows_path)
    observations = list(_read_tsv(observations_path, OBS_FIELDS))
    for obs in observations:
        if obs["case_id"] not in rows:
            _die(f"{observations_path}: unknown case_id {obs['case_id']}")
        if obs["target_reached"] not in ("0", "1"):
            _die(f"{observations_path}: target_reached must be 0/1")
        if obs["predicate_holds"] not in ("0", "1"):
            _die(f"{observations_path}: predicate_holds must be 0/1")
        if obs["row_complete"] not in ("0", "1"):
            _die(f"{observations_path}: row_complete must be 0/1")

    by_condition: dict[tuple[str, ...], list[dict[str, str]]] = defaultdict(list)
    for obs in observations:
        key = (
            obs["routine"],
            obs["grade"],
            obs["arm"],
            obs["phase"],
            obs["condition_id"],
            obs["backend"],
        )
        by_condition[key].append(obs)

    reports = []
    for key, events in sorted(by_condition.items()):
        routine, grade, arm, phase, condition_id, backend = key
        case_ids = {event["case_id"] for event in events}
        complete_cases = {
            event["case_id"] for event in events if event["row_complete"] == "1"
        }
        reached_cases = {
            event["case_id"] for event in events if event["target_reached"] == "1"
        }
        observed_cases = {
            event["case_id"]
            for event in events
            if event["target_reached"] == "1" and event["predicate_holds"] == "1"
        }
        valid_reached = sum(1 for case in reached_cases if rows[case]["row_class"] == "valid")
        invalid_reached = sum(1 for case in reached_cases if rows[case]["row_class"] == "invalid")
        disagreements = 0
        values: dict[tuple[str, str], set[str]] = defaultdict(set)
        for event in events:
            values[(event["case_id"], event["invocation_id"])].add(
                event["predicate_holds"]
            )
        disagreements = sum(len(vals) > 1 for vals in values.values())
        violated = any(
            event["target_reached"] == "1" and event["predicate_holds"] == "0"
            for event in events
        )
        all_complete = len(complete_cases) == len(rows)
        if disagreements or not all_complete:
            status = "INCONCLUSIVE"
        elif violated:
            status = "VIOLATED"
        elif observed_cases:
            status = "OBSERVED"
        elif not reached_cases:
            # This is deliberately not a reachability claim.  In particular,
            # rejection-path conditions can have zero reached invalid rows.
            status = "NEVER_OBSERVED_CORPUS_LIMITED"
        else:
            status = "NEVER_OBSERVED_ON_REACHED_TARGET"
        reports.append(
            {
                "routine": routine,
                "grade": grade,
                "arm": arm,
                "phase": phase,
                "condition_id": condition_id,
                "kind": "register/value-or-memory-projection",
                "backend": backend,
                "rows_total": len(rows),
                "rows_completed": len(complete_cases),
                "valid_rows": sum(row["row_class"] == "valid" for row in rows.values()),
                "invalid_rows": sum(row["row_class"] == "invalid" for row in rows.values()),
                "target_rows_reached": len(reached_cases),
                "valid_target_rows_reached": valid_reached,
                "invalid_target_rows_reached": invalid_reached,
                "invocations": len(events),
                "observed_count": len(observed_cases),
                "violated_count": sum(
                    event["target_reached"] == "1" and event["predicate_holds"] == "0"
                    for event in events
                ),
                "case_ids": sorted(case_ids),
                "backend_disagreements": disagreements,
                "status": status,
                "coverage_note": (
                    "invalid-path denominator is target_rows_reached, not all invalid rows"
                    if invalid_reached == 0 and sum(row["row_class"] == "invalid" for row in rows.values())
                    else "target denominator recorded"
                ),
            }
        )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({"schema": "reachability-report-v1", "conditions": reports}, indent=2) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    split = sub.add_parser("split", help="write valid/invalid row split")
    split.add_argument("--manifest", required=True, type=Path)
    split.add_argument("--out", required=True, type=Path)
    split.add_argument("--summary", required=True, type=Path)

    sample = sub.add_parser("sample", help="select a deterministic stratified sample")
    sample.add_argument("--split", required=True, type=Path)
    sample.add_argument("--out", required=True, type=Path)
    sample.add_argument("--size", required=True, type=int)
    sample.add_argument("--seed", required=True, type=int)

    report = sub.add_parser("summarize", help="summarize condition observations")
    report.add_argument("--rows", required=True, type=Path)
    report.add_argument("--observations", required=True, type=Path)
    report.add_argument("--out", required=True, type=Path)

    args = parser.parse_args()
    if args.command == "split":
        rows = read_manifest(args.manifest)
        summary = write_split(rows, args.out, args.manifest)
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(json.dumps(summary, indent=2) + "\n")
        print(json.dumps(summary, sort_keys=True))
    elif args.command == "sample":
        rows = [
            Row(
                case_id=row["case_id"],
                label=row["label"],
                fixture_relpath=row["fixture_relpath"],
                input_file=row["input_file"],
                expected_success=int(row["expected_success"]),
                input_len=int(row["input_len"]),
                gas_limit=int(row["gas_limit"]),
            )
            for row in _load_rows(args.split).values()
        ]
        selected = stratified_sample(rows, args.size, args.seed)
        write_sample(selected, args.out, args.split, args.seed)
        print(json.dumps({"size": len(selected), "seed": args.seed, "valid": sum(r.expected_success for r in selected), "invalid": sum(not r.expected_success for r in selected)}, sort_keys=True))
    else:
        summarize(args.rows, args.observations, args.out)
        print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
