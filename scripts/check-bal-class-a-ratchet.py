#!/usr/bin/env python3
"""Class-A provided-BAL ratchet (#11183, #11796).

Enumerate emitted paths that touch the supplied-BAL cursor cells
(`bv_bal_*`, `bsr_bal_*`, and `c1_bal_*`; and, when the linked addresses are
known, li/imm of those addresses). Compare to a checked-in baseline:

  * NEW path not in baseline  → fail (regression: new Class-A read)
  * BASELINE path disappeared → fail (force explicit baseline shrink on retirement)

ENDPOINT (coord 11183 ruling): the guest must not read the provided BAL as an
EXECUTION INPUT. BIND rows that only locate the payload slice so it can be
hashed/serialized (fork.py:366/:390) are the legitimate finish line — NOT an
unfinished zero. This ratchet tracks bv_bal_start/len REFERENCES and therefore
CONFLATES BIND WITH CHECK; a remaining BIND row is not incomplete work. CHECK
rows (field compare / parse-bail / body walk against supplied content) retire
under the EQUIVALENCE argument: spec validates only hash of the BUILT list
(fork.py:390) and has no supplied body — not under "hash covers it" (that needs
collision-freedom, which the maintainer ruled out).

Per path, record whether a following direct jal's return status (a0) is tested.
The same gate validates the merge-safe rationale sidecar and counts its explicit
bullet annotations, so regeneration cannot silently erase review context.

Operates on the EMITTED stateless_guest.s only — not Lean source strings.

Blind spots (CANNOT see) — documented for reviewers:
  * Lean comments/docstrings/source that never reach .s
  * Computed jalr targets not recovered as symbols
  * Non-BAL absolute arenas (0xa2b20000 account maps, etc.) unless added to SEEDS
  * Host/IO outside guest .text
  * Intentional untaint (li reg,0 after load) stops tracking that reg
  * The permitted hash sink bal_serializer_verify is CONDITIONAL on
    bv_bal_shadow_ready (sole writer: block_verdict setup); this ratchet does
    not prove the flag is set, only records edges that touch the BAL cells.

Usage:
  scripts/check-bal-class-a-ratchet.py [--elf-dir DIR] [--write-baseline]
  scripts/check-bal-class-a-ratchet.py --self-test
  scripts/check-bal-class-a-ratchet.py --baseline PATH   # default scripts/bal-class-a-baseline.tsv
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
DEFAULT_BASELINE = ROOT / "scripts" / "bal-class-a-baseline.tsv"
DEFAULT_NOTES = ROOT / "scripts" / "bal-class-a-notes.md"
EXPECTED_ANNOTATION_COUNT = 1
# Class-A predicate: every emitted reference to a supplied-BAL cursor. Keep the
# predicate here, beside the baseline/debt check, so the next reader can
# re-derive the census instead of trusting the TSV row count (#11796).
SEEDS = (
    "bv_bal_start",
    "bv_bal_len",
    "bsr_bal_start",
    "bsr_bal_len",
    "c1_bal_start",
    "c1_bal_len",
)
# One-way debt ratchet: this is the number of currently baselined emitted
# paths in the predicate above. It is a debt figure, not a target; it may only
# decrease, and a retirement plus this constant's decrease must land together.
EXPECTED_CLASS_A_DEBT = 12
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


HEADER = (
    "# bal-class-a-baseline.tsv — emitted paths touching supplied-BAL cursors\n"
    "# Predicate: bv_bal_*, bsr_bal_*, and c1_bal_* start/len cells\n"
    "# Debt count constant: EXPECTED_CLASS_A_DEBT in check-bal-class-a-ratchet.py\n"
    "# Columns: function  kind  jal_or_sink  return_status_tested  insn\n"
    "# Maintained by scripts/check-bal-class-a-ratchet.py\n"
    "# NEW path => fail; MISSING baselined path => fail (shrink baseline on purpose).\n"
    "# return_status_tested=yes means a direct jal soon after is followed by a0/t*-status branch.\n"
    "#\n"
    "# ENDPOINT (#11183): remaining rows should be BIND (locate BAL slice for hash/\n"
    "# serialize per fork.py:366/:390), NOT CHECKs against supplied body content.\n"
    "# Ratchet conflates BIND with CHECK (tracks start/len refs). BIND residual is\n"
    "# the finish line — not unfinished work. Retire CHECKs via EQUIVALENCE (spec\n"
    "# only hashes the BUILT list at fork.py:390; no supplied body), never via\n"
    "# \"hash covers it\" (needs collision-freedom; ruled out).\n"
)


def write_baseline(path: Path, rows: list[dict[str, str]]) -> None:
    body = "\n".join(row_key(r) for r in rows) + ("\n" if rows else "")
    path.write_text(HEADER + body)


def load_baseline(path: Path) -> set[str]:
    keys: set[str] = set()
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        keys.add(line.rstrip("\n"))
    return keys


def compare_rows(
    rows: list[dict[str, str]], baseline: set[str]
) -> tuple[list[str], list[str]]:
    """Return new and disappeared paths for the Class-A set comparison."""
    current = {row_key(r) for r in rows}
    return sorted(current - baseline), sorted(baseline - current)


def self_test() -> int:
    """Prove a newly planted cursor read fails, then removal returns to OK."""
    clean_asm = """\
.text
synthetic_bal_consumer:
  la t0, bv_bal_start
  ld a0, 0(t0)
  ret
bv_bal_start:
  .zero 8
c1_bal_start:
  .zero 8
"""
    planted_asm = clean_asm.replace(
        "  ret\n",
        "  la t1, c1_bal_start\n"
        "  ld a1, 0(t1)\n"
        "  ret\n",
        1,
    )

    with tempfile.TemporaryDirectory(prefix="bal-class-a-self-test-") as td:
        root = Path(td)
        clean_path = root / "clean.s"
        planted_path = root / "planted.s"
        clean_path.write_text(clean_asm)
        planted_path.write_text(planted_asm)

        clean_rows = analyze(clean_path)
        baseline = {row_key(row) for row in clean_rows}
        planted_rows = analyze(planted_path)
        new, missing = compare_rows(planted_rows, baseline)
        if len(new) != 1 or missing:
            print(
                "check-bal-class-a-ratchet --self-test: FAIL — planted "
                "c1_bal_start read did not create exactly one new path",
                file=sys.stderr,
            )
            return 1
        print(
            "check-bal-class-a-ratchet --self-test: planted synthetic "
            "c1_bal_start read"
        )
        print(
            "check-bal-class-a-ratchet: FAIL (expected; 1 new Class-A path)"
        )
        print(f"  + {new[0]}")

        new, missing = compare_rows(clean_rows, baseline)
        if new or missing:
            print(
                "check-bal-class-a-ratchet --self-test: FAIL — removing the "
                "synthetic read did not restore the baseline",
                file=sys.stderr,
            )
            return 1
        print(
            "check-bal-class-a-ratchet --self-test: synthetic read removed"
        )
        print(
            f"check-bal-class-a-ratchet: OK (debt={len(clean_rows)} "
            "synthetic baseline paths; no new Class-A edges)"
        )
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
    ap.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    ap.add_argument(
        "--notes",
        type=Path,
        default=DEFAULT_NOTES,
        help="merge-safe annotation sidecar (default scripts/bal-class-a-notes.md)",
    )
    ap.add_argument(
        "--write-baseline",
        action="store_true",
        help="write baseline from current guest and exit 0",
    )
    ap.add_argument(
        "--no-build",
        action="store_true",
        help="require existing .s under --elf-dir",
    )
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="plant a synthetic cursor read, prove FAIL, then remove it and prove OK",
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

    if args.write_baseline:
        write_baseline(args.baseline, rows)
        print(
            f"wrote {args.baseline} (debt={len(rows)} paths; "
            f"{annotation_count} annotations) from {s_path}"
        )
        return 0

    if not args.baseline.is_file():
        print(f"missing baseline {args.baseline} — run with --write-baseline", file=sys.stderr)
        return 2

    base = load_baseline(args.baseline)
    new, missing = compare_rows(rows, base)
    debt_drift = len(rows) != EXPECTED_CLASS_A_DEBT

    if debt_drift or new or missing:
        print("check-bal-class-a-ratchet: FAIL", file=sys.stderr)
        if debt_drift:
            print(
                "\nClass-A debt ratchet drift: "
                f"expected exactly {EXPECTED_CLASS_A_DEBT} paths, found {len(rows)}; "
                "update the committed debt only with the corresponding source "
                "retirement.",
                file=sys.stderr,
            )
        if new:
            print(f"\nNEW paths not in baseline ({len(new)}):", file=sys.stderr)
            for k in new:
                print(f"  + {k}", file=sys.stderr)
        if missing:
            print(
                f"\nBASELINE paths disappeared ({len(missing)}) — shrink baseline deliberately:",
                file=sys.stderr,
            )
            for k in missing:
                print(f"  - {k}", file=sys.stderr)
        print(
            "\nUpdate scripts/bal-class-a-baseline.tsv via:\n"
            "  scripts/check-bal-class-a-ratchet.py --write-baseline\n"
            "after reviewing each edge (Class-A retirement must shrink, not grow).",
            file=sys.stderr,
        )
        return 1

    print(
        f"check-bal-class-a-ratchet: OK (debt={len(rows)} baselined paths; "
        f"no new Class-A edges; no silent shrink; "
        f"{annotation_count} sidecar bullet annotations present)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
