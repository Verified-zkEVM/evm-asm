#!/usr/bin/env python3
"""Class-A provided-BAL ratchet (#11183).

Enumerate emitted paths that touch bv_bal_start / bv_bal_len (and, when the
linked addresses are known, li/imm of those addresses). Compare to a checked-in
baseline:

  * NEW path not in baseline  → fail (regression: new Class-A read)
  * BASELINE path disappeared → fail (force explicit baseline shrink on retirement)

Per path, record whether a following direct jal's return status (a0) is tested.

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
  scripts/check-bal-class-a-ratchet.py --baseline PATH   # default scripts/bal-class-a-baseline.tsv
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BASELINE = ROOT / "scripts" / "bal-class-a-baseline.tsv"
SEEDS = ("bv_bal_start", "bv_bal_len")
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
        if re.match(r"^(bv_bal_start|bv_bal_len):\s*$", line.strip()):
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
    "# bal-class-a-baseline.tsv — emitted paths touching bv_bal_start/bv_bal_len\n"
    "# Columns: function  kind  jal_or_sink  return_status_tested  insn\n"
    "# Maintained by scripts/check-bal-class-a-ratchet.py\n"
    "# NEW path => fail; MISSING baselined path => fail (shrink baseline on purpose).\n"
    "# return_status_tested=yes means a direct jal soon after is followed by a0/t*-status branch.\n"
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
        "--write-baseline",
        action="store_true",
        help="write baseline from current guest and exit 0",
    )
    ap.add_argument(
        "--no-build",
        action="store_true",
        help="require existing .s under --elf-dir",
    )
    args = ap.parse_args()

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
            "check-bal-class-a-ratchet: FAIL closed — zero bv_bal_start/len refs in emitted asm",
            file=sys.stderr,
        )
        return 1

    if args.write_baseline:
        write_baseline(args.baseline, rows)
        print(f"wrote {args.baseline} ({len(rows)} paths) from {s_path}")
        return 0

    if not args.baseline.is_file():
        print(f"missing baseline {args.baseline} — run with --write-baseline", file=sys.stderr)
        return 2

    base = load_baseline(args.baseline)
    cur = {row_key(r) for r in rows}
    new = sorted(cur - base)
    missing = sorted(base - cur)

    if new or missing:
        print("check-bal-class-a-ratchet: FAIL", file=sys.stderr)
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
        f"check-bal-class-a-ratchet: OK ({len(rows)} baselined paths; "
        f"no new Class-A edges; no silent shrink)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
