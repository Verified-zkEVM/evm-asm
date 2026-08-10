#!/usr/bin/env python3
"""Class-A provided-BAL ratchet (#11183, #11796).

Enumerate emitted paths that touch the supplied-BAL cursor cells
(`bv_bal_*`, `bsr_bal_*`, and `c1_bal_*`; and, when the linked addresses are
known, li/imm of those addresses).  The four legitimate pointer/length edges
are an explicit allowlist; a separate body predicate is intentionally empty:

  * unexpected edge not in the allowlist → fail (regression: new Class-A edge)
  * body edge or known body consumer → fail (regression: supplied-BAL body read)

ENDPOINT (coord 11183 ruling): the guest must not read the provided BAL as an
EXECUTION INPUT. BIND rows that only locate the payload slice so it can be
hashed/serialized (fork.py:366/:390) are the legitimate finish line — NOT an
unfinished zero. The allowlist preserves those rows while the empty body
predicate rejects any new field/body path. CHECK rows (field compare /
parse-bail / body walk against supplied content) retire under the EQUIVALENCE
argument: spec validates only hash of the BUILT list (fork.py:390) and has no
supplied body — not under "hash covers it" (that needs collision-freedom, which
the maintainer ruled out).

Per path, record whether a following direct jal's return status (a0) is tested.
The same gate validates the merge-safe rationale sidecar and counts its explicit
bullet annotations, so regeneration cannot silently erase review context.

Operates on the EMITTED stateless_guest.s only — not Lean source strings.

Blind spots (CANNOT see) — documented for reviewers:
  * Lean comments/docstrings/source that never reach .s
  * Computed jalr targets not recovered as symbols
  * Non-BAL absolute arenas (0xa2b20000 account maps, etc.) unless added to the
    family predicate
  * Host/IO outside guest .text
  * Intentional untaint (li reg,0 after load) stops tracking that reg
  * The permitted hash sink bal_serializer_verify is CONDITIONAL on
    bv_bal_shadow_ready (sole writer: block_verdict setup); this ratchet does
    not prove the flag is set, only records edges that touch the BAL cells.

Usage:
  scripts/check-bal-class-a-ratchet.py [--elf-dir DIR]
  scripts/check-bal-class-a-ratchet.py --self-test
"""
from __future__ import annotations

import argparse
from collections import Counter
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_NOTES = ROOT / "scripts" / "bal-class-a-notes.md"
EXPECTED_ANNOTATION_COUNT = 1
# Known supplied-BAL cursor names.  The body predicate below intentionally
# covers the whole family; these six names remain the stable edge census used
# by the explicit BIND allowlist.
SEEDS = (
    "bv_bal_start",
    "bv_bal_len",
    "bsr_bal_start",
    "bsr_bal_len",
    "c1_bal_start",
    "c1_bal_len",
)
BAL_FAMILY = re.compile(r"\b(?:bv|bsr|c1)_bal_[A-Za-z0-9_]+\b")
BODY_CALLS = frozenset(
    {
        "bal_section_info",
        "bal_account_record_array",
        "rlp_walk_init",
        "rlp_walk_next",
        "bal_find_account_by_address",
        "bal_account_nonstorage_finals",
    }
)
# These fields are output/diagnostic state, not supplied-BAL body fields.
# Keeping them explicit prevents a future diagnostic addition from silently
# turning into a false body-read failure.
NON_BODY_SYMBOLS = frozenset({"bsr_bal_count"})
NON_BODY_PREFIXES = ("bv_bal_shadow_",)

# The four surviving edges are deliberately source-level facts, not a
# regenerable TSV.  Each reason is kept beside its row so BIND and diagnostic
# edges cannot be conflated by a future baseline refresh.
ALLOWED_BIND_ROWS: dict[str, str] = {
    "\t".join(
        [
            ".Lbv_after_tx_gate",
            "load",
            "bgv_u64le",
            "no",
            "la t2, bv_bal_start; ld t3, 0(t2); sub a1, a1, t3",
        ]
    ): "BIND: load bal_start to derive the SSZ BAL length",
    "\t".join(
        [
            ".Lbv_after_tx_gate",
            "store",
            "bgv_u32le",
            "no",
            "la t2, bv_bal_start; sd a0, 0(t2)",
        ]
    ): "BIND: store the SSZ BAL start pointer",
    "\t".join(
        [
            ".Lbv_after_tx_gate",
            "store",
            "bgv_u64le",
            "no",
            "la t2, bv_bal_len; sd a1, 0(t2)",
        ]
    ): "BIND: store the SSZ BAL length",
    "\t".join(
        [
            ".Lbv_ret",
            "store",
            "bal_gas_valid_from_builder",
            "yes",
            "la t0, bv_bal_len; ld t1, 0(t0); la t0, bv_bal_shadow_supplied_len; sd t1, 0(t0)",
        ]
    ): "DIAGNOSTIC: copy supplied length into the epilogue report; not a verdict input",
}
ALLOWED_BIND_KEYS = frozenset(ALLOWED_BIND_ROWS)
# Direct jal whose a0 is commonly status-tested after BAL helpers.
STATUS_JAL = re.compile(
    r"\bjal\s+ra,\s*([A-Za-z0-9_.]+)"
)
STATUS_TEST = re.compile(
    r"\b(bnez|beqz|bne|beq)\s+(a0|t0|t1|t2|t5|t6)\b|\b(bne|beq)\s+a0,"
)


def build_guest(out_prefix: Path) -> Path:
    out_prefix.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [
            "lake",
            "exe",
            "codegen",
            "--program",
            "stateless_guest",
            "--halt",
            "linux93",
            "-o",
            str(out_prefix),
        ],
        cwd=ROOT,
        check=True,
    )
    s_path = Path(str(out_prefix) + ".s")
    if not s_path.is_file():
        raise SystemExit(f"missing emitted asm {s_path}")
    return s_path


def parse_functions(lines: list[str]) -> list[tuple[str, int, int]]:
    """Return list of (name, start_idx, end_idx) for text labels."""
    label_re = re.compile(r"^([A-Za-z0-9_./]+):\s*$")
    labels: list[tuple[str, int]] = []
    for i, line in enumerate(lines):
        m = label_re.match(line)
        if m:
            labels.append((m.group(1), i))
    spans: list[tuple[str, int, int]] = []
    for i, (name, start) in enumerate(labels):
        end = labels[i + 1][1] if i + 1 < len(labels) else len(lines)
        spans.append((name, start, end))
    return spans


def norm_insn(line: str) -> str:
    s = line.split("#", 1)[0].strip()
    s = re.sub(r"\s+", " ", s)
    return s


def seed_hit(line: str) -> bool:
    return any(s in line for s in SEEDS)


def analyze(s_path: Path) -> list[dict[str, str]]:
    lines = s_path.read_text(errors="replace").splitlines()
    spans = parse_functions(lines)
    # map line -> function
    fn_at = ["?"] * len(lines)
    for name, start, end in spans:
        for i in range(start, end):
            fn_at[i] = name

    rows: list[dict[str, str]] = []
    for i, line in enumerate(lines):
        if not seed_hit(line):
            continue
        # skip pure definitions
        if re.match(
            r"^(bv_bal_start|bv_bal_len|bsr_bal_start|bsr_bal_len|"
            r"c1_bal_start|c1_bal_len):\s*$",
            line.strip(),
        ):
            continue
        if line.strip().startswith("#"):
            continue
        n = norm_insn(line)
        if not n or n.startswith("."):
            continue
        kind = "ref"
        if re.search(r"\bsd\b", n) and any(s in n for s in SEEDS):
            kind = "store"
        elif re.search(r"\bld\b", n) and any(s in n for s in SEEDS):
            kind = "load"
        elif re.search(r"\bla\b", n) and any(s in n for s in SEEDS):
            kind = "la"

        jal_target = ""
        ret_tested = "no"
        # look ahead in same function for jal + status test
        fn = fn_at[i]
        for j in range(i, min(i + 24, len(lines))):
            if fn_at[j] != fn:
                break
            jm = STATUS_JAL.search(lines[j])
            if jm and not jal_target:
                jal_target = jm.group(1)
                # scan a few more lines for status branch
                for k in range(j, min(j + 8, len(lines))):
                    if fn_at[k] != fn:
                        break
                    if STATUS_TEST.search(lines[k]):
                        ret_tested = "yes"
                        break
                break
            # store of bal ptr into another cell counts as handoff sink
            if re.search(r"\bsd\b", lines[j]) and "runtime_current_bal" in lines[j]:
                jal_target = jal_target or "STORE:runtime_current_bal"
                break

        # stable key fields
        rows.append(
            {
                "function": fn,
                "kind": kind,
                "jal_or_sink": jal_target or "-",
                "return_status_tested": ret_tested,
                "insn": n,
                "line": str(i),
            }
        )

    # stable sort
    rows.sort(key=lambda r: (r["function"], r["kind"], r["jal_or_sink"], r["insn"]))
    return rows


def row_key(r: dict[str, str]) -> str:
    return "\t".join(
        [
            r["function"],
            r["kind"],
            r["jal_or_sink"],
            r["return_status_tested"],
            r["insn"],
        ]
    )


def validate_bind_allowlist(rows: list[dict[str, str]]) -> tuple[list[str], list[str]]:
    """Return unexpected and missing rows against the explicit BIND allowlist."""
    current = {row_key(row) for row in rows}
    return sorted(current - ALLOWED_BIND_KEYS), sorted(ALLOWED_BIND_KEYS - current)


def _is_definition(line: str) -> bool:
    return bool(
        re.match(
            r"^(bv_bal_[A-Za-z0-9_]+|bsr_bal_[A-Za-z0-9_]+|"
            r"c1_bal_[A-Za-z0-9_]+):\s*$",
            line.strip(),
        )
    )


def _is_non_body_symbol(symbol: str) -> bool:
    return symbol in NON_BODY_SYMBOLS or any(
        symbol.startswith(prefix) for prefix in NON_BODY_PREFIXES
    )


def body_candidates(s_path: Path) -> list[str]:
    """Find supplied-BAL body edges; an empty result is the intended state."""
    lines = s_path.read_text(errors="replace").splitlines()
    spans = parse_functions(lines)
    fn_at = ["?"] * len(lines)
    span_lines: dict[str, range] = {}
    for name, start, end in spans:
        span_lines[name] = range(start, end)
        for i in range(start, end):
            fn_at[i] = name

    rows = analyze(s_path)
    row_by_line = {int(row["line"]): row for row in rows}
    found: set[str] = set()

    for i, line in enumerate(lines):
        if line.strip().startswith("#") or _is_definition(line):
            continue
        symbols = {
            symbol
            for symbol in BAL_FAMILY.findall(line)
            if not _is_non_body_symbol(symbol)
        }
        if not symbols:
            continue
        row = row_by_line.get(i)
        if row is not None and row_key(row) in ALLOWED_BIND_KEYS:
            continue
        found.add(
            f"family-ref {fn_at[i]}:{i + 1}: "
            f"{norm_insn(line)} ({', '.join(sorted(symbols))})"
        )

    # A body consumer may be called after a pointer has been copied into a
    # register, so it need not share a line with a BAL symbol.  Require both
    # facts in one function to avoid flagging generic RLP helpers unrelated to
    # the supplied BAL.
    for name, span in span_lines.items():
        body_calls = sorted(
            {
                match.group(1)
                for i in span
                for match in [STATUS_JAL.search(lines[i])]
                if match and match.group(1) in BODY_CALLS
            }
        )
        if not body_calls:
            continue
        family_symbols = sorted(
            {
                symbol
                for i in span
                for symbol in BAL_FAMILY.findall(lines[i])
                if not _is_definition(lines[i])
            }
        )
        if family_symbols:
            found.add(
                f"body-call {name}: {', '.join(body_calls)} "
                f"with {', '.join(family_symbols)}"
            )

    return sorted(found)


def self_test() -> int:
    """Prove a planted body read fails, then removal returns to OK."""
    clean_asm = """\
.text
synthetic_clean:
  ret
c1_bal_start:
  .zero 8
"""
    planted_asm = """\
.text
synthetic_body:
  la t1, c1_bal_start
  ld a1, 0(t1)
  jal ra, bal_find_account_by_address
  ret
c1_bal_start:
  .zero 8
"""

    with tempfile.TemporaryDirectory(prefix="bal-class-a-self-test-") as td:
        root = Path(td)
        clean_path = root / "clean.s"
        planted_path = root / "planted.s"
        clean_path.write_text(clean_asm)
        planted_path.write_text(planted_asm)

        clean_body = body_candidates(clean_path)
        planted_body = body_candidates(planted_path)
        if clean_body or not planted_body:
            print(
                "check-bal-class-a-ratchet --self-test: FAIL — body "
                "predicate did not distinguish the planted c1 read",
                file=sys.stderr,
            )
            return 1
        print(
            "check-bal-class-a-ratchet --self-test: planted synthetic c1 body read"
        )
        print(
            "check-bal-class-a-ratchet: FAIL (expected; body predicate fired)"
        )
        for candidate in planted_body:
            print(f"  + {candidate}")
        print(
            "check-bal-class-a-ratchet --self-test: synthetic body read removed"
        )
        print("check-bal-class-a-ratchet: OK (body predicate empty)")
    return 0


ANNOTATION_COUNT_RE = re.compile(r"^\s*<!--\s*annotation-count:\s*(\d+)\s*-->\s*$")
ANNOTATION_KEY_RE = re.compile(r"^##\s+key:\s*(.*?)\s*\|\s*(\S+)\s*$")


def load_annotation_notes(path: Path) -> dict[tuple[str, str], list[str]]:
    """Load merge-safe bullet annotations keyed by emitted function and jal/sink."""
    if not path.is_file():
        raise ValueError(f"missing annotation sidecar {path}")

    notes: dict[tuple[str, str], list[str]] = {}
    declared_count: int | None = None
    current_key: tuple[str, str] | None = None
    current_body: list[str] = []

    def finish_entry() -> None:
        nonlocal current_key, current_body
        if current_key is None:
            return
        annotations = []
        for line in current_body:
            stripped = line.strip()
            if not stripped:
                continue
            if not stripped.startswith("- "):
                raise ValueError(
                    f"annotation {current_key!r} must use one bullet per rationale"
                )
            annotations.append(stripped[2:].strip())
        if not annotations:
            raise ValueError(f"annotation {current_key!r} has no rationale text")
        if current_key in notes:
            raise ValueError(f"duplicate annotation key {current_key!r}")
        notes[current_key] = annotations
        current_key = None
        current_body = []

    for line in path.read_text().splitlines():
        count_match = ANNOTATION_COUNT_RE.match(line)
        if count_match:
            if declared_count is not None:
                raise ValueError("annotation sidecar declares its count more than once")
            declared_count = int(count_match.group(1))
            continue

        key_match = ANNOTATION_KEY_RE.match(line)
        if key_match:
            finish_entry()
            current_key = (key_match.group(1), key_match.group(2))
            continue

        if current_key is not None:
            current_body.append(line)

    finish_entry()

    if declared_count != EXPECTED_ANNOTATION_COUNT:
        raise ValueError(
            "annotation sidecar declares "
            f"{declared_count!r} annotations; expected {EXPECTED_ANNOTATION_COUNT}"
        )
    annotation_count = sum(len(annotations) for annotations in notes.values())
    # Zero is legal only when EXPECTED_ANNOTATION_COUNT is deliberately 0
    # (every annotated edge retired, e.g. #11183 bal_txs_independent).
    if annotation_count == 0 and EXPECTED_ANNOTATION_COUNT != 0:
        raise ValueError(
            "annotation sidecar has zero annotations; the rationale was lost"
        )
    if annotation_count != EXPECTED_ANNOTATION_COUNT:
        raise ValueError(
            f"annotation sidecar has {annotation_count} annotations; "
            f"expected {EXPECTED_ANNOTATION_COUNT}"
        )
    return notes


def validate_annotation_notes(
    path: Path, rows: list[dict[str, str]]
) -> int:
    """Require every durable annotation to identify exactly one current edge."""
    try:
        notes = load_annotation_notes(path)
    except ValueError as exc:
        print(f"check-bal-class-a-ratchet: FAIL — {exc}", file=sys.stderr)
        raise SystemExit(1) from exc

    row_counts = Counter((r["function"], r["jal_or_sink"]) for r in rows)
    missing = sorted(key for key in notes if row_counts[key] == 0)
    ambiguous = sorted(key for key in notes if row_counts[key] > 1)
    if missing or ambiguous:
        print("check-bal-class-a-ratchet: FAIL — annotation key drift", file=sys.stderr)
        for key in missing:
            print(f"  missing emitted edge: {key[0]} | {key[1]}", file=sys.stderr)
        for key in ambiguous:
            print(
                f"  ambiguous emitted edge ({row_counts[key]} rows): {key[0]} | {key[1]}",
                file=sys.stderr,
            )
        raise SystemExit(1)

    annotation_count = sum(len(annotations) for annotations in notes.values())
    print(
        f"check-bal-class-a-ratchet: annotation sidecar OK "
        f"({annotation_count}/{EXPECTED_ANNOTATION_COUNT} sidecar bullet annotations; "
        f"{len(notes)} keyed edges)"
    )
    return annotation_count


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--elf-dir",
        type=Path,
        default=None,
        help="dir containing stateless_guest.s (skip rebuild if present)",
    )
    ap.add_argument(
        "--notes",
        type=Path,
        default=DEFAULT_NOTES,
        help="merge-safe annotation sidecar (default scripts/bal-class-a-notes.md)",
    )
    ap.add_argument(
        "--no-build",
        action="store_true",
        help="require existing .s under --elf-dir",
    )
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="plant a synthetic body read, prove FAIL, then remove it and prove OK",
    )
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    if args.elf_dir:
        s_path = args.elf_dir / "stateless_guest.s"
        if not s_path.is_file():
            if args.no_build:
                print(f"missing {s_path}", file=sys.stderr)
                return 2
            s_path = build_guest(args.elf_dir / "stateless_guest")
    else:
        out = ROOT / "gen-out" / "bal-class-a" / "stateless_guest"
        s_path = build_guest(out)

    rows = analyze(s_path)
    if not rows:
        print(
            "check-bal-class-a-ratchet: FAIL closed — zero supplied-BAL cursor refs in emitted asm",
            file=sys.stderr,
        )
        return 1

    annotation_count = validate_annotation_notes(args.notes, rows)
    unexpected, missing = validate_bind_allowlist(rows)
    body = body_candidates(s_path)

    if unexpected or missing or body:
        print("check-bal-class-a-ratchet: FAIL", file=sys.stderr)
        if unexpected:
            print(
                f"\nUNEXPECTED supplied-BAL edges ({len(unexpected)}):",
                file=sys.stderr,
            )
            for key in unexpected:
                print(f"  + {key}", file=sys.stderr)
        if missing:
            print(
                f"\nALLOWLIST edges disappeared ({len(missing)}):",
                file=sys.stderr,
            )
            for key in missing:
                print(f"  - {key}", file=sys.stderr)
        if body:
            print(f"\nSUPPLIED-BAL BODY EDGES ({len(body)}):", file=sys.stderr)
            for candidate in body:
                print(f"  + {candidate}", file=sys.stderr)
        return 1

    print(
        f"check-bal-class-a-ratchet: OK ({len(rows)} explicit BIND/diagnostic "
        f"allowlist edges; body predicate empty; "
        f"{annotation_count} sidecar bullet annotations present)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
