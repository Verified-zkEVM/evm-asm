#!/usr/bin/env python3
"""Check the explicit semantic-evidence ledger (#13030).

The axiom gate is intentionally registry-driven: it audits declarations reached
by witness abbrevs in the progress registries.  That is the right policy for
the registry, but it cannot discover a useful theorem which has no row and no
witness.  This ledger is the explicit opt-in surface for the other evidence
that reviewers rely on.

Evidence is deliberately typed.  A satisfiability instance, a negative
control, a machine-body contract, and a temporary module-floor print are not
interchangeable claims, even when all four are Lean ``Prop`` declarations.
Each row names its source and audit surface, so a rename or removal fails
loudly instead of making the evidence disappear from the check.

Usage::

    python3 scripts/check-evidence-ledger.py
    python3 scripts/check-evidence-ledger.py --self-test
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "scripts" / "evidence-ledger.tsv"
WITNESSES = ROOT / "EvmAsm" / "Progress" / "AxiomWitnesses.lean"
EVMASM = ROOT / "EvmAsm"

# target, source, kind, surface, evidence, consumer, issue, status, notes
EXPECTED_COLUMNS = 9
KINDS = {"nonvacuity", "negative-control", "machine-body", "module-floor"}
SURFACES = {"axiom-witness", "source-print"}
STATUSES = {"registered", "temporary"}

DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:def|abbrev|theorem|lemma|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)",
    re.MULTILINE,
)
PRINT_RE = re.compile(
    r"^\s*#print axioms ([A-Za-z_][A-Za-z0-9_.']*)\s*$", re.MULTILINE
)


@dataclass(frozen=True)
class Row:
    line: int
    target: str
    source: str
    kind: str
    surface: str
    evidence: str
    consumer: str
    issue: str
    status: str
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


def declaration_names(source: str) -> set[str]:
    return {m.group(1) for m in DECL_RE.finditer(source)}


def declarations() -> dict[str, set[str]]:
    out: dict[str, set[str]] = {}
    for path in EVMASM.rglob("*.lean"):
        out[str(path.relative_to(ROOT))] = declaration_names(
            path.read_text(errors="ignore")
        )
    return out


def qualified_names(decls: dict[str, set[str]]) -> set[str]:
    """Return short names; the ledger checks namespace separately."""
    return {name.rsplit(".", 1)[-1] for names in decls.values() for name in names}


def witness_prints(path: Path = WITNESSES, text: str | None = None) -> set[str]:
    if text is None and not path.is_file():
        return set()
    if text is None:
        text = path.read_text(errors="ignore")
    return set(PRINT_RE.findall(text))


def source_prints(source: str) -> set[str]:
    return set(PRINT_RE.findall(source))


def declaration_segments(source: str) -> dict[str, str]:
    matches = list(DECL_RE.finditer(source))
    return {
        m.group(1): source[
            m.start() : matches[i + 1].start() if i + 1 < len(matches) else len(source)
        ]
        for i, m in enumerate(matches)
    }


def validate(
    path: Path = LEDGER,
    *,
    source_overrides: dict[str, str] | None = None,
    witness_override: str | None = None,
) -> list[str]:
    rows, errors = load_rows(path)
    by_source = declarations()
    all_short = qualified_names(by_source)
    generated = (
        witness_prints(text=witness_override)
        if witness_override is not None
        else witness_prints()
    )
    seen: set[str] = set()
    source_overrides = source_overrides or {}

    for row in rows:
        if row.target in seen:
            errors.append(f"line {row.line}: duplicate target {row.target}")
        seen.add(row.target)

        if not row.target.startswith("EvmAsm."):
            errors.append(f"line {row.line}: target is not EvmAsm-qualified: {row.target}")
        if row.kind not in KINDS:
            errors.append(f"line {row.line}: unknown evidence kind {row.kind!r}")
        if row.surface not in SURFACES:
            errors.append(f"line {row.line}: unknown audit surface {row.surface!r}")
        if row.status not in STATUSES:
            errors.append(f"line {row.line}: unknown status {row.status!r}")
        if not row.issue.isdigit():
            errors.append(f"line {row.line}: issue must be numeric, got {row.issue!r}")
        if not row.consumer.strip():
            errors.append(f"line {row.line}: consumer/registry is empty")
        if not row.notes.strip():
            errors.append(f"line {row.line}: notes are empty")

        source_path = ROOT / row.source
        if not source_path.is_file():
            errors.append(f"line {row.line}: source file does not exist: {row.source}")
            continue
        source_text = source_overrides.get(
            row.source, source_path.read_text(errors="ignore")
        )
        segments = declaration_segments(source_text)
        short = row.target.rsplit(".", 1)[-1]
        if short not in segments:
            errors.append(
                f"line {row.line}: target {row.target} is not declared in {row.source}"
            )
        namespace = row.target.rsplit(".", 1)[0]
        if re.search(
            r"^\s*namespace\s+" + re.escape(namespace) + r"\s*$",
            source_text,
            re.MULTILINE,
        ) is None:
            errors.append(
                f"line {row.line}: target namespace {namespace} is not declared in {row.source}"
            )

        if not row.evidence.startswith("EvmAsm."):
            errors.append(
                f"line {row.line}: evidence reference is not EvmAsm-qualified: {row.evidence}"
            )
        elif row.evidence.rsplit(".", 1)[-1] not in all_short:
            errors.append(
                f"line {row.line}: evidence names no EvmAsm declaration: {row.evidence}"
            )

        if row.surface == "axiom-witness":
            if row.status != "registered":
                errors.append(
                    f"line {row.line}: axiom-witness surface must be registered, got {row.status!r}"
                )
            if row.evidence not in generated:
                errors.append(
                    f"line {row.line}: evidence is not printed by AxiomWitnesses: {row.evidence}"
                )
        elif row.surface == "source-print":
            if row.status != "temporary":
                errors.append(
                    f"line {row.line}: source-print surface must be temporary, got {row.status!r}"
                )
            printed = source_prints(source_text)
            short_evidence = row.evidence.rsplit(".", 1)[-1]
            if row.evidence not in printed and short_evidence not in printed:
                errors.append(
                    f"line {row.line}: temporary source print is absent: {row.evidence}"
                )

        if row.kind == "module-floor" and row.surface != "source-print":
            errors.append(
                f"line {row.line}: module-floor evidence must use source-print surface"
            )
        if row.kind != "module-floor" and row.surface == "source-print":
            errors.append(
                f"line {row.line}: only module-floor rows may use source-print surface"
            )

    return errors


def self_test() -> int:
    baseline = validate()
    if baseline:
        print("check-evidence-ledger --self-test: FAIL — baseline is invalid")
        for error in baseline:
            print(f"  {error}")
        return 1
    original = LEDGER.read_text()
    first_data = next(
        line for line in original.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    )
    first_fields = first_data.split("\t")
    stale_target_fields = first_fields.copy()
    stale_target_fields[0] = "EvmAsm.Codegen.Proofs.deleted_target"
    stale_evidence_fields = first_fields.copy()
    stale_evidence_fields[4] = "EvmAsm.Codegen.Proofs.deleted_evidence"

    with tempfile.TemporaryDirectory(prefix="evidence-ledger-") as td:
        temp = Path(td) / "evidence-ledger.tsv"

        def expect_failure(
            label: str,
            contents: str,
            *,
            source_overrides: dict[str, str] | None = None,
            witness_override: str | None = None,
        ) -> bool:
            temp.write_text(contents)
            if not validate(
                temp,
                source_overrides=source_overrides,
                witness_override=witness_override,
            ):
                print(f"check-evidence-ledger --self-test: FAIL — {label} passed")
                return False
            return True

        if not expect_failure(
            "stale target",
            original.replace(first_data, "\t".join(stale_target_fields), 1),
        ):
            return 1
        if not expect_failure(
            "stale evidence reference",
            original.replace(first_data, "\t".join(stale_evidence_fields), 1),
        ):
            return 1
        if not expect_failure("duplicate target", original + "\n" + first_data + "\n"):
            return 1
        fields = first_data.split("\t")
        fields[2] = "not-a-kind"
        if not expect_failure(
            "unknown kind",
            original.replace(first_data, "\t".join(fields), 1),
        ):
            return 1
        fields = first_data.split("\t")
        fields[3] = "source-print"
        if not expect_failure(
            "wrong surface for non-module evidence",
            original.replace(first_data, "\t".join(fields), 1),
        ):
            return 1
        body_row = next(row for row in load_rows()[0] if row.kind == "module-floor")
        body_source = ROOT / body_row.source
        body_text = body_source.read_text(errors="ignore")
        body_marker = "#print axioms body_spec"
        if body_marker not in body_text:
            print("check-evidence-ledger --self-test: FAIL — body print marker missing")
            return 1
        if not expect_failure(
            "missing temporary source print",
            original,
            source_overrides={
                body_row.source: body_text.replace(
                    body_marker, "#print axioms body_spec_removed", 1
                )
            },
        ):
            return 1
        witness_marker = "#print axioms EvmAsm.Codegen.Proofs.envelope_region_sat"
        witness_text = WITNESSES.read_text(errors="ignore")
        if witness_marker not in witness_text:
            print("check-evidence-ledger --self-test: FAIL — generated witness print missing")
            return 1
        if not expect_failure(
            "missing generated witness print",
            original,
            witness_override=witness_text.replace(
                witness_marker, "#print axioms EvmAsm.Fake.deleted_evidence", 1
            ),
        ):
            return 1

    print(
        "check-evidence-ledger --self-test: PASS "
        "(stale target, stale evidence, duplicate, bad kind, wrong surface, "
        "missing source print and missing generated witness failures detected)"
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
        print(f"check-evidence-ledger: FAIL — {len(errors)} error(s)", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1
    rows, _ = load_rows()
    counts = ", ".join(
        f"{kind}={sum(row.kind == kind for row in rows)}"
        for kind in sorted(KINDS)
    )
    print(
        f"check-evidence-ledger: OK — {len(rows)} explicit evidence rows ({counts}); "
        "axiom-witness rows are generated-witness checked and module-floor rows "
        "are temporary source-print checked"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
