#!/usr/bin/env python3
"""#11520 guard: code_at_header_state_root must not compile a missing preimage
into empty code without an EMPTY_CODE_HASH identity check.

Spec (pin e5a8caf1b witness_state.py:204-212):
  * EMPTY_CODE_HASH → return b"" (legitimately empty)
  * any other missing hash → raise KeyError → REJECTION
A guest site that treats status-5 (code hash present on account, preimage
absent from codes) as empty WITHOUT comparing cahsr_acct_struct.code_hash to
EMPTY_CODE_HASH has compiled a raise into a fallback value.

Two correct sites already exist (ChildFrameHandlers status-5 + cd_empty_code_hash;
BlockVerdictDispatchTx materialize path + chahsr_empty_code_hash). This gate
makes a regression uncompilable-to-CI rather than merely reviewable.

Checks (Lean source of Codegen Programs / Dispatch — no guest emit required):

  1. FUNCTION PAIRING: any non-probe `def` whose body contains
     `jal ra, code_at_header_state_root` must also contain an
     `*empty_code_hash` load (`la …, …empty_code_hash`). Missing → violator.
  2. STATUS-5 ANTI-PATTERN: after a `jal ra, code_at_header_state_root`, a
     `li r, 5` followed by `beq a0, r, …empty…` (or swap) WITHOUT an intervening
     `*empty_code_hash` load → violator (even if the same function has a
     correct site elsewhere — DispatchTx has both).

Allow-list: scripts/code-preimage-empty-hash-allow.txt
  lines: kind\\tfile\\tdef\\tordinal   kind in {pair, anti}
EXPECTED_VIOLATOR_COUNT must match the allow-list length and ratchet DOWN only
with an explicit edit in the same commit that fixes a site (same durability
rule as EXPECTED_ANNOTATION_COUNT / #11505).

OUT OF SCOPE (different family — do not count as covered by this gate):
  account_exists_at_header_state_root / account_is_empty_at_header_state_root
  callers that treat nonzero as "no charge" (ChildFrameHandlers:974-989,
  BlockVerdictSimpleTransferGas, Selfdestruct, ChildFrameHandlerTailHelpers
  exists/empty path). Tracked separately (#11526 FA-directional undercharge).

Usage:
  python3 scripts/check-code-preimage-empty-hash.py
  python3 scripts/check-code-preimage-empty-hash.py --write-allowlist
"""
from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCAN_ROOTS = [
    ROOT / "EvmAsm" / "Codegen" / "Programs",
    ROOT / "EvmAsm" / "Codegen" / "Dispatch.lean",
]
ALLOW_PATH = ROOT / "scripts" / "code-preimage-empty-hash-allow.txt"
# Durability: every allow-list line is one known violator. Drive to zero.
EXPECTED_VIOLATOR_COUNT = 7

JAL_CODE = re.compile(r"jal\s+ra,\s*code_at_header_state_root\b")
EMPTY_LA = re.compile(r"la\s+\w+,\s*\w*empty_code_hash\b")
DEF = re.compile(r"^def\s+(\w+)\b", re.M)
PROBE_NAME = re.compile(
    r"^(zisk|Zisk)|Prologue$|Probe|probe|Selftest|selftest|DataSection|Data$"
)


def _iter_files() -> list[Path]:
    out: list[Path] = []
    for root in SCAN_ROOTS:
        if root.is_file():
            out.append(root)
        elif root.is_dir():
            out.extend(sorted(root.rglob("*.lean")))
    return out


def _def_spans(text: str) -> list[tuple[str, int, int]]:
    """Return (name, start, end) for each top-level def; end = next def or EOF."""
    ms = list(DEF.finditer(text))
    spans = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        spans.append((m.group(1), m.start(), end))
    return spans


def _is_probe(name: str) -> bool:
    return bool(PROBE_NAME.search(name))


def find_violators() -> list[tuple[str, str, str, int]]:
    """Return list of (kind, relpath, def_name, ordinal)."""
    viol: list[tuple[str, str, str, int]] = []
    for path in _iter_files():
        text = path.read_text(errors="replace")
        if "code_at_header_state_root" not in text:
            continue
        rel = str(path.relative_to(ROOT))
        spans = _def_spans(text)
        # map byte offset -> owning def
        def owner_at(pos: int) -> str:
            for name, s, e in spans:
                if s <= pos < e:
                    return name
            return "?"

        # Per-def jal ordinals
        jal_ord: dict[str, int] = defaultdict(int)
        for m in JAL_CODE.finditer(text):
            name = owner_at(m.start())
            if _is_probe(name):
                jal_ord[name] += 1
                continue
            ord_i = jal_ord[name]
            jal_ord[name] += 1
            # window after jal for anti-pattern (raw Lean with \n escapes)
            win = text[m.end() : m.end() + 2500].replace("\\n", "\n")
            # anti: li r,5 ; beq a0,r, …empty… without empty_code_hash before beq
            anti = False
            for sm in re.finditer(r"li\s+(\w+),\s*5\b", win):
                reg = sm.group(1)
                after = win[sm.end() : sm.end() + 350]
                if re.search(
                    rf"beq\s+(?:a0,\s*{reg}|{reg},\s*a0),\s*\S*[Ee]mpty", after
                ):
                    pre = win[: sm.start()]
                    if not EMPTY_LA.search(pre) and "empty_code_hash" not in pre:
                        anti = True
                        break
            if anti:
                viol.append(("anti", rel, name, ord_i))

        # function pairing: def has jal code_at and no empty_code_hash anywhere
        for name, s, e in spans:
            if _is_probe(name):
                continue
            body = text[s:e]
            if not JAL_CODE.search(body):
                continue
            body_n = body.replace("\\n", "\n")
            if EMPTY_LA.search(body_n) or "empty_code_hash" in body_n:
                continue
            # one pair entry per def (ordinal 0)
            viol.append(("pair", rel, name, 0))
    # stable order
    viol.sort()
    return viol


def load_allow() -> set[tuple[str, str, str, int]]:
    if not ALLOW_PATH.exists():
        return set()
    out: set[tuple[str, str, str, int]] = set()
    for line in ALLOW_PATH.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 4:
            raise SystemExit(f"bad allow line (want kind\\tfile\\tdef\\tord): {line!r}")
        kind, f, d, o = parts
        out.add((kind, f, d, int(o)))
    return out


def write_allow(viol: list[tuple[str, str, str, int]]) -> None:
    lines = [
        "# #11520 code_at_header_state_root empty-hash guard allow-list",
        "# kind\\tfile\\tdef\\tordinal",
        "# kind=pair: function has jal code_at_header without *empty_code_hash",
        "# kind=anti: status-5 beq-to-empty without EMPTY_CODE_HASH compare",
        "# EXPECTED_VIOLATOR_COUNT in check-code-preimage-empty-hash.py must match.",
        "# Ratchet DOWN only with a same-commit site fix. Never raise without coord.",
        "",
    ]
    for kind, f, d, o in viol:
        lines.append(f"{kind}\t{f}\t{d}\t{o}")
    ALLOW_PATH.write_text("\n".join(lines) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--write-allowlist",
        action="store_true",
        help="rewrite allow-list to current violators (bootstrap / deliberate shrink)",
    )
    args = ap.parse_args()
    viol = find_violators()
    if args.write_allowlist:
        write_allow(viol)
        print(
            f"wrote {ALLOW_PATH.relative_to(ROOT)}: {len(viol)} violators "
            f"(set EXPECTED_VIOLATOR_COUNT = {len(viol)})"
        )
        return 0

    allow = load_allow()
    problems: list[str] = []

    if len(allow) != EXPECTED_VIOLATOR_COUNT:
        problems.append(
            f"allow-list has {len(allow)} entries but EXPECTED_VIOLATOR_COUNT="
            f"{EXPECTED_VIOLATOR_COUNT} — update both in the same commit"
        )
    if len(viol) != EXPECTED_VIOLATOR_COUNT:
        problems.append(
            f"found {len(viol)} violators but EXPECTED_VIOLATOR_COUNT="
            f"{EXPECTED_VIOLATOR_COUNT} (allow {len(allow)})"
        )

    viol_set = set(viol)
    new = sorted(viol_set - allow)
    gone = sorted(allow - viol_set)
    for kind, f, d, o in new:
        problems.append(f"NEW violator not on allow-list: {kind} {f} {d} #{o}")
    for kind, f, d, o in gone:
        problems.append(
            f"allow-list entry gone (fix landed? shrink EXPECTED + allow): "
            f"{kind} {f} {d} #{o}"
        )

    if problems:
        print("check-code-preimage-empty-hash: FAIL")
        for p in problems:
            print(f"  {p}")
        print(
            f"  (pairing+anti violators={len(viol)}; allow={len(allow)}; "
            f"EXPECTED={EXPECTED_VIOLATOR_COUNT})"
        )
        print(
            "  OUT OF SCOPE: account_exists/is_empty_at_header_state_root no-charge "
            "family (#11526) — not covered by this gate."
        )
        return 1

    print(
        f"check-code-preimage-empty-hash: OK "
        f"({len(viol)}/{EXPECTED_VIOLATOR_COUNT} allow-listed violators; "
        f"0 new; pair+anti). OUT OF SCOPE: exists/is_empty no-charge family."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
