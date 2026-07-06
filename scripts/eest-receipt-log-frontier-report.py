#!/usr/bin/env python3
"""Classify receipt/log-related EEST stateless frontier rows.

The stateless harness currently records only the final
SszStatelessValidationResult bytes, so this report uses two signals:

* region diffs from ``<case>.result.tsv`` vs ``manifest.tsv`` expected hex;
* fixture path / label keywords that identify likely receipt/log surfaces.

The output is intentionally conservative. It is a triage map for the
feature-completeness queue, not a proof that a fixture's only blocker is the
named surface.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


BEADS = {
    "execution_status": "evm-asm-fhsxz.2.4.2.63.1.3",
    "cumulative_gas": "evm-asm-fhsxz.2.4.2.57.7",
    "logs_list": "evm-asm-fhsxz.2.4.2.63.1.2",
    "logs_bloom": "evm-asm-fhsxz.2.4.2.63.1.4",
    "receipts_root": "evm-asm-fhsxz.2.4.2.63.1.5",
    "create_address": "evm-asm-fhsxz.2.4.2.61.1",
    "typed_receipt": "evm-asm-fhsxz.2.4.2.63.1.3",
}


@dataclass(frozen=True)
class ManifestRow:
    label: str
    input_path: Path
    expected_hex: str
    succ_bit: str
    input_len: str
    relpath: str


def read_manifest(path: Path, strict: bool) -> list[ManifestRow]:
    rows: list[ManifestRow] = []
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != 6:
            if strict:
                raise SystemExit(f"{path}:{line_no}: expected 6 TSV fields, got {len(fields)}")
            continue
        label, input_path, expected_hex, succ_bit, input_len, relpath = fields
        rows.append(
            ManifestRow(
                label=label,
                input_path=Path(input_path),
                expected_hex=expected_hex,
                succ_bit=succ_bit,
                input_len=input_len,
                relpath=relpath,
            )
        )
    return rows


def classify_keywords(row: ManifestRow) -> list[str]:
    hay = f"{row.label} {row.relpath}".lower()
    classes: list[str] = []

    if any(k in hay for k in ("log0", "log1", "log2", "log3", "log4", "/log", "logs")):
        classes.extend(["logs_list", "logs_bloom"])
    if "receipt" in hay:
        classes.append("receipts_root")
    if any(k in hay for k in ("create2", "create_", "/create", "contract_creation")):
        classes.append("create_address")
    if any(k in hay for k in ("eip2930", "eip1559", "eip4844", "eip7702", "typed")):
        classes.append("typed_receipt")
    if any(k in hay for k in ("refund", "gas", "intrinsic", "out_of_gas", "oog")):
        classes.append("cumulative_gas")
    if any(k in hay for k in ("revert", "invalid", "exception", "failure", "static")):
        classes.append("execution_status")

    return sorted(set(classes))


def result_status(run_dir: Path, row: ManifestRow) -> tuple[str, str, str]:
    result_path = run_dir / f"{row.label}.result.tsv"
    if not result_path.exists():
        return ("MISSING", "----", "")
    fields = result_path.read_text().splitlines()[0].split("\t", 1)
    if len(fields) != 2:
        return ("ERROR", "malformed-result", "")
    status, actual = fields
    if status != "OK":
        return ("ERROR", actual, "")

    expected = row.expected_hex[:210]
    actual = actual[:210]
    regions = [
        "root" if actual[:64] == expected[:64] else "root_diff",
        "succ" if actual[64:66] == expected[64:66] else "succ_diff",
        "tail" if actual[66:210] == expected[66:210] else "tail_diff",
    ]
    verdict = "FULL" if actual == expected else "DIFF"
    return (verdict, ",".join(regions), actual)


def iter_report_rows(
    rows: Iterable[ManifestRow], run_dir: Path, include_all: bool
) -> Iterable[tuple[ManifestRow, str, str, list[str]]]:
    for row in rows:
        classes = classify_keywords(row)
        verdict, regions, _actual = result_status(run_dir, row)
        if not include_all and verdict == "FULL":
            continue
        if not classes and not include_all:
            continue
        yield row, verdict, regions, classes


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", type=Path, default=Path("gen-out/eest-run"))
    parser.add_argument("--all", action="store_true", help="include full matches and unclassified rows")
    parser.add_argument("--limit", type=int, default=0, help="maximum rows to print after filtering")
    parser.add_argument("--strict", action="store_true", help="reject non-six-column manifest lines")
    args = parser.parse_args()

    manifest = args.run_dir / "manifest.tsv"
    if not manifest.exists():
        raise SystemExit(f"missing manifest: {manifest}")

    rows = read_manifest(manifest, strict=args.strict)
    printed = 0
    summary: dict[str, int] = {}
    print("label\tverdict\tregions\tclasses\tblocker_beads\trelpath")
    for row, verdict, regions, classes in iter_report_rows(rows, args.run_dir, args.all):
        for cls in classes or ["unclassified"]:
            summary[cls] = summary.get(cls, 0) + 1
        blocker_beads = ",".join(BEADS[cls] for cls in classes if cls in BEADS)
        print(
            f"{row.label}\t{verdict}\t{regions}\t"
            f"{','.join(classes) if classes else 'unclassified'}\t"
            f"{blocker_beads if blocker_beads else '-'}\t{row.relpath}"
        )
        printed += 1
        if args.limit and printed >= args.limit:
            break

    print("\n# summary")
    print(f"rows_printed\t{printed}")
    for cls in sorted(summary):
        print(f"{cls}\t{summary[cls]}")


if __name__ == "__main__":
    main()
