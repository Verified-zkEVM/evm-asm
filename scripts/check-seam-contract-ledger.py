#!/usr/bin/env python3
"""Check the explicit semantic seam-contract ledger (#12926).

The source tree contains many ordinary ``Prop`` definitions, so a syntactic
``def ... : Prop`` census cannot tell which declarations are intended as
machine-contract seams.  This gate uses an explicit opt-in ledger instead.
Each row names the declaration, its source file, and the expected result/shape.
Missing inhabitance or adjacent-consistency evidence is represented by the
literal ``NONE`` plus a required reason; it is never represented by omission.
Evidence names must both resolve to a declaration and be printed by the
kernel-witness module, keeping the ledger on the same audit surface as the
other progress registries.

Usage::

    python3 scripts/check-seam-contract-ledger.py
    python3 scripts/check-seam-contract-ledger.py --self-test
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "scripts" / "seam-contract-ledger.tsv"
WITNESSES = ROOT / "EvmAsm" / "Progress" / "AxiomWitnesses.lean"
EVMASM = ROOT / "EvmAsm"

NONE = "NONE"
EXPECTED_COLUMNS = 10
DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:def|abbrev|theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)
PROP_RESULT_RE = re.compile(r":\s*Prop\s*:=")
WITNESS_PRINT_RE = re.compile(r"^#print axioms (EvmAsm\.[A-Za-z0-9_.']+)$", re.MULTILINE)


@dataclass(frozen=True)
class Row:
    line: int
    target: str
    source: str
    result_type: str
    shape: str
    inhabitance: str
    consistency: str
    issue: str
    inhabitance_reason: str
    consistency_reason: str
    notes: str


def load_rows(path: Path = LEDGER) -> tuple[list[Row], list[str]]:
    errors: list[str] = []
    rows: list[Row] = []
    if not path.is_file():
        return [], [f"missing ledger: {path.relative_to(ROOT)}"]
    for line_no, raw in enumerate(path.read_text().splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != EXPECTED_COLUMNS:
            errors.append(
                f"line {line_no}: expected {EXPECTED_COLUMNS} tab-separated columns, "
                f"got {len(fields)}"
            )
            continue
        rows.append(Row(line_no, *fields))
    if not rows:
        errors.append("ledger has no data rows")
    return rows, errors


def declaration_segments(source: str) -> dict[str, str]:
    matches = list(DECL_RE.finditer(source))
    out: dict[str, str] = {}
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(source)
        out[match.group(1)] = source[match.start() : end]
    return out


def declarations() -> dict[str, set[str]]:
    """Return short declaration names grouped by source path."""
    out: dict[str, set[str]] = {}
    for path in EVMASM.rglob("*.lean"):
        out[str(path.relative_to(ROOT))] = set(
            declaration_segments(path.read_text(errors="ignore"))
        )
    return out


def witness_prints() -> set[str]:
    if not WITNESSES.is_file():
        return set()
    return set(WITNESS_PRINT_RE.findall(WITNESSES.read_text(errors="ignore")))


def validate(path: Path = LEDGER) -> list[str]:
    rows, errors = load_rows(path)
    by_source = declarations()
    printed = witness_prints()
    seen: set[str] = set()
    known_shapes = {"cpsNBranchWithin", "cpsTripleWithin", "conjunction"}

    for row in rows:
        if row.target in seen:
            errors.append(f"line {row.line}: duplicate target {row.target}")
        seen.add(row.target)
        if not row.target.startswith("EvmAsm."):
            errors.append(f"line {row.line}: target is not EvmAsm-qualified: {row.target}")
        if row.result_type != "Prop":
            errors.append(f"line {row.line}: expected result type Prop, got {row.result_type!r}")
        if row.shape not in known_shapes:
            errors.append(f"line {row.line}: unknown contract shape {row.shape!r}")
        source_path = ROOT / row.source
        if not source_path.is_file():
            errors.append(f"line {row.line}: source file does not exist: {row.source}")
            continue
        source_text = source_path.read_text(errors="ignore")
        segments = declaration_segments(source_text)
        namespace = row.target.rsplit(".", 1)[0]
        if re.search(
            r"^\s*namespace\s+" + re.escape(namespace) + r"\s*$",
            source_text,
            re.MULTILINE,
        ) is None:
            errors.append(
                f"line {row.line}: target namespace {namespace} is not declared in {row.source}"
            )
        short = row.target.rsplit(".", 1)[-1]
        segment = segments.get(short)
        if segment is None:
            errors.append(
                f"line {row.line}: target {row.target} is not declared in {row.source}"
            )
        else:
            if PROP_RESULT_RE.search(segment) is None:
                errors.append(
                    f"line {row.line}: target {row.target} does not have an explicit `: Prop` result"
                )
            if row.shape != "conjunction" and row.shape not in segment:
                errors.append(
                    f"line {row.line}: target {row.target} does not expose recorded shape {row.shape}"
                )
            if row.shape == "conjunction" and "∧" not in segment and "And" not in segment:
                errors.append(
                    f"line {row.line}: conjunction target {row.target} has no conjunction in declaration"
                )

        if not row.issue.isdigit():
            errors.append(f"line {row.line}: issue must be numeric, got {row.issue!r}")
        for label, ref, reason in (
            ("inhabitance", row.inhabitance, row.inhabitance_reason),
            ("consistency", row.consistency, row.consistency_reason),
        ):
            if ref == NONE:
                if not reason.strip() or reason.strip() == "-":
                    errors.append(
                        f"line {row.line}: {label} is NONE but has no explicit reason"
                    )
                continue
            if not ref.startswith("EvmAsm."):
                errors.append(f"line {row.line}: {label} reference is not qualified: {ref}")
                continue
            short_ref = ref.rsplit(".", 1)[-1]
            if not any(short_ref in names for names in by_source.values()):
                errors.append(
                    f"line {row.line}: {label} reference names no EvmAsm declaration: {ref}"
                )
            if ref not in printed:
                errors.append(
                    f"line {row.line}: {label} reference is outside AxiomWitnesses: {ref}"
                )
    return errors


def self_test() -> int:
    """Exercise the missing-target and missing-reason failure directions."""
    baseline = validate()
    if baseline:
        print("check-seam-contract-ledger --self-test: FAIL — baseline is invalid")
        for error in baseline:
            print(f"  {error}")
        return 1
    original = LEDGER.read_text()
    first_data = next(
        line for line in original.splitlines() if line.strip() and not line.lstrip().startswith("#")
    )

    with tempfile.TemporaryDirectory(prefix="seam-contract-ledger-") as td:
        temp = Path(td) / "ledger.tsv"
        # A target rename must fail loudly rather than silently dropping a row.
        temp.write_text(original.replace("priceBodyContract", "priceBodyContract_removed", 1))
        if not validate(temp):
            print("check-seam-contract-ledger --self-test: FAIL — stale target passed")
            return 1
        # A NONE marker without its reason must also fail; this protects the
        # explicit-unwitnessed state from degrading into an empty field.
        fields = first_data.split("\t")
        fields[7] = ""
        temp.write_text(
            original.replace(first_data, "\t".join(fields), 1)
        )
        if not validate(temp):
            print("check-seam-contract-ledger --self-test: FAIL — missing reason passed")
            return 1
    print(
        "check-seam-contract-ledger --self-test: PASS "
        "(stale-target and missing-reason failures both detected)"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test and self_test():
        return 1
    errors = validate()
    if errors:
        print(
            f"check-seam-contract-ledger: FAIL — {len(errors)} error(s)",
            file=sys.stderr,
        )
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1
    rows, _ = load_rows()
    missing_inhabitance = sum(row.inhabitance == NONE for row in rows)
    missing_consistency = sum(row.consistency == NONE for row in rows)
    print(
        f"check-seam-contract-ledger: OK — {len(rows)} explicit seam contracts; "
        f"{missing_inhabitance} lack an inhabitance witness and "
        f"{missing_consistency} lack adjacent-consistency evidence, each with an "
        "explicit reason; supplied evidence is axiom-witnessed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
