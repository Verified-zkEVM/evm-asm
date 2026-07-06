#!/usr/bin/env python3
"""Report EEST precompile fixture coverage and current guest outcomes.

The report is intentionally path-driven. The EEST generated fixture relpaths
encode the source test module names, which are stable enough for assigning
precompile families without parsing every blockchain test payload.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


BEAD = "evm-asm-fhsxz.2.4.2.62.1"


@dataclass(frozen=True)
class Family:
    key: str
    surface: str
    addresses: str
    backend: str
    bead: str
    patterns: tuple[str, ...]


FAMILIES: tuple[Family, ...] = (
    Family(
        "warming",
        "Precompile account warming",
        "active precompiles",
        "VM call gas/account-access path before dispatch",
        BEAD,
        ("precompile_warming",),
    ),
    Family(
        "absence",
        "Precompile absence",
        "0x01..0x101 excluding active precompiles",
        "Absent-account CALL semantics before dispatch",
        "evm-asm-fhsxz.2.4.2.62.2.6",
        ("precompile_absence",),
    ),
    Family(
        "ecrecover",
        "ECRECOVER",
        "0x01",
        "zkvm_secp256k1_ecrecover bridge exists; stateless dispatch missing",
        "evm-asm-fhsxz.2.4.2.62.2",
        ("ecrecover",),
    ),
    Family(
        "sha256",
        "SHA256",
        "0x02",
        "zkvm_sha256 bridge exists; stateless dispatch missing",
        "evm-asm-fhsxz.2.4.2.62.2",
        ("sha256", "sha_256"),
    ),
    Family(
        "ripemd160",
        "RIPEMD160",
        "0x03",
        "zkvm_ripemd160 bridge exists; stateless dispatch missing",
        "evm-asm-fhsxz.2.4.2.62.2",
        ("ripemd", "ripemd160"),
    ),
    Family(
        "identity",
        "IDENTITY",
        "0x04",
        "in-guest memory copy; no accelerator",
        "evm-asm-fhsxz.2.4.2.62.2",
        ("identity_precompile", "test_identity", "identity_returndatasize"),
    ),
    Family(
        "modexp",
        "MODEXP",
        "0x05",
        "zkvm_modexp bridge exists; gas/return-data framing missing",
        "evm-asm-fhsxz.2.4.2.62.3",
        ("modexp", "eip198", "eip7823", "eip7883"),
    ),
    Family(
        "bn254",
        "BN254 add/mul/pairing",
        "0x06..0x08",
        "zkvm_bn254_* bridges exist; call framing missing",
        "evm-asm-fhsxz.2.4.2.62.3",
        ("alt_bn128", "bn128", "ec_add", "ecadd", "ec_mul", "ecmul", "ecpairing", "eip196", "eip197"),
    ),
    Family(
        "blake2f",
        "BLAKE2F",
        "0x09",
        "zkvm_blake2f bridge exists; call framing missing",
        "evm-asm-fhsxz.2.4.2.62.3",
        ("blake2f",),
    ),
    Family(
        "kzg",
        "KZG point evaluation",
        "0x0a",
        "zkvm_kzg_point_eval bridge exists; call framing missing",
        "evm-asm-fhsxz.2.4.2.62.3",
        ("point_evaluation", "kzg", "eip4844"),
    ),
    Family(
        "bls12",
        "BLS12-381",
        "0x0b..0x11",
        "zkvm_bls12_* bridges exist; call framing missing",
        "evm-asm-fhsxz.2.4.2.62.3",
        ("bls12", "bls_12_381", "eip2537"),
    ),
    Family(
        "p256verify",
        "P256VERIFY",
        "0x100",
        "zkvm_secp256r1_verify bridge exists; call framing missing",
        "evm-asm-fhsxz.2.4.2.62.3",
        ("p256verify", "secp256r1", "eip7951"),
    ),
    Family(
        "call_context",
        "CALL/STATICCALL/revert/create interactions with precompiles",
        "mixed",
        "VM call/create/revert semantics plus dispatch",
        BEAD,
        ("staticcall_precompile", "staticcall_to_precompile", "to_precompile", "precompiled", "precompile"),
    ),
)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def default_fixtures_dir(root: Path, tag: str) -> Path:
    return root / "gen-out" / "eest-fixtures" / tag / "fixtures" / "fixtures"


def default_manifest(root: Path) -> Path:
    run_root = root / "gen-out" / "eest-run"
    flat = run_root / "manifest.tsv"
    if flat.is_file():
        return flat

    manifests = sorted(
        run_root.glob("run-*/manifest.tsv"),
        key=lambda path: path.stat().st_mtime,
        reverse=True,
    )
    if manifests:
        return manifests[0]
    return flat


def normalize(path: str) -> str:
    return path.replace("\\", "/").lower()


def matching_family(relpath: str) -> Family | None:
    haystack = normalize(relpath)
    for family in FAMILIES:
        if any(pattern in haystack for pattern in family.patterns):
            return family
    return None


def fixture_relpaths(fixtures_dir: Path) -> Iterable[str]:
    if not fixtures_dir.is_dir():
        return ()
    return (
        path.relative_to(fixtures_dir).as_posix()
        for path in fixtures_dir.rglob("*.json")
        if matching_family(path.relative_to(fixtures_dir).as_posix()) is not None
    )


@dataclass
class Outcome:
    fixture_files: int = 0
    selected: int = 0
    full: int = 0
    root: int = 0
    succ: int = 0
    tail: int = 0
    root_only_diff: int = 0
    fail: int = 0
    error: int = 0
    missing_result: int = 0


def read_manifest(path: Path) -> Iterable[tuple[str, str, str]]:
    if not path.is_file():
        return ()

    rows: list[tuple[str, str, str]] = []
    with path.open() as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) == 6:
                label, _input_file, expected_hex, _succ_bit, _input_len, relpath = parts
            elif len(parts) == 7:
                label, _input_file, expected_hex, _succ_bit, _input_len, _gas_limit, relpath = parts
            else:
                raise SystemExit(f"bad manifest row with {len(parts)} columns: {line!r}")
            rows.append((label, expected_hex, relpath))
    return rows


def add_result(outcome: Outcome, results_dir: Path, label: str, expected_hex: str) -> None:
    result = results_dir / f"{label}.result.tsv"
    if not result.is_file():
        outcome.missing_result += 1
        return

    status, actual_hex = result.read_text().rstrip("\n").split("\t", 1)
    if status != "OK":
        outcome.error += 1
        return

    exp = expected_hex[:210]
    root = actual_hex[:64] == exp[:64]
    succ = actual_hex[64:66] == exp[64:66]
    tail = actual_hex[66:210] == exp[66:210]
    outcome.root += int(root)
    outcome.succ += int(succ)
    outcome.tail += int(tail)
    if actual_hex == exp:
        outcome.full += 1
    else:
        outcome.fail += 1
        outcome.root_only_diff += int((not root) and succ and tail)


def markdown_row(columns: Iterable[object]) -> str:
    return "| " + " | ".join(str(column) for column in columns) + " |"


def print_markdown(outcomes: dict[str, Outcome]) -> None:
    print(markdown_row(("family", "address", "fixture files", "selected", "full", "root", "succ", "tail", "fail", "error", "backend", "bead")))
    print(markdown_row(("---", "---", "---:", "---:", "---:", "---:", "---:", "---:", "---:", "---:", "---", "---")))
    for family in FAMILIES:
        outcome = outcomes[family.key]
        if outcome.fixture_files == 0 and outcome.selected == 0:
            continue
        print(
            markdown_row(
                (
                    family.surface,
                    family.addresses,
                    outcome.fixture_files,
                    outcome.selected,
                    outcome.full,
                    outcome.root,
                    outcome.succ,
                    outcome.tail,
                    outcome.fail,
                    outcome.error,
                    family.backend,
                    family.bead,
                )
            )
        )


def print_tsv(outcomes: dict[str, Outcome]) -> None:
    columns = [
        "family",
        "surface",
        "addresses",
        "fixture_files",
        "selected",
        "full",
        "root",
        "succ",
        "tail",
        "root_only_diff",
        "fail",
        "error",
        "missing_result",
        "backend",
        "bead",
    ]
    print("\t".join(columns))
    for family in FAMILIES:
        outcome = outcomes[family.key]
        if outcome.fixture_files == 0 and outcome.selected == 0:
            continue
        print(
            "\t".join(
                str(value)
                for value in (
                    family.key,
                    family.surface,
                    family.addresses,
                    outcome.fixture_files,
                    outcome.selected,
                    outcome.full,
                    outcome.root,
                    outcome.succ,
                    outcome.tail,
                    outcome.root_only_diff,
                    outcome.fail,
                    outcome.error,
                    outcome.missing_result,
                    family.backend,
                    family.bead,
                )
            )
        )


def main() -> int:
    root = repo_root()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", default="zkevm@v0.4.0")
    parser.add_argument("--fixtures-dir", type=Path, default=None)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=default_manifest(root),
        help="stateless harness manifest.tsv; omitted/missing means no run outcome columns",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=None,
        help="directory containing *.result.tsv (default: manifest parent)",
    )
    parser.add_argument("--markdown", action="store_true")
    args = parser.parse_args()

    fixtures_dir = args.fixtures_dir or default_fixtures_dir(root, args.tag)
    results_dir = args.results_dir or args.manifest.parent
    outcomes = {family.key: Outcome() for family in FAMILIES}

    for relpath in fixture_relpaths(fixtures_dir):
        family = matching_family(relpath)
        if family is not None:
            outcomes[family.key].fixture_files += 1

    for label, expected_hex, relpath in read_manifest(args.manifest):
        family = matching_family(relpath)
        if family is None:
            continue
        outcome = outcomes[family.key]
        outcome.selected += 1
        add_result(outcome, results_dir, label, expected_hex)

    if args.markdown:
        print_markdown(outcomes)
    else:
        print_tsv(outcomes)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
