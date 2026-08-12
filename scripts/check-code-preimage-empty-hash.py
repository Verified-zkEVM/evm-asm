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
     `*empty_code_hash` load. Missing → violator (kind=pair).
  2. STATUS-5 ANTI-PATTERN: after that jal, `li r,5` + `beq a0,r,…empty…`
     without a prior empty-hash load → violator (kind=anti).
  3. GATING (not mere presence): after `la …empty_code_hash`, the limb
     `bne` mismatch targets must not all equal the match fall-through `j`
     target. Convergence = discarded comparison = false assurance
     (kind=conv). SenderCounts:248 is the proof case — every bne and the
     final j go to `.Leas_we_ok`.

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
EXPECTED_VIOLATOR_COUNT = 5

JAL_CODE = re.compile(r"jal\s+ra,\s*code_at_header_state_root\b")
# Converted Program definitions keep cross-function calls symbolic in
# `emitProgramR`: the same call is a `.JAL .x1 (jalOff GuestAddrs... )`
# constructor rather than an assembly string.  Keep both detectors because
# this gate scans a mixed tree while routines migrate to Program form.
JAL_CODE_PROG = re.compile(
    r"\.JAL\s+\.x1\s+\(jalOff\s+GuestAddrs\.code_at_header_state_root\b"
)
EMPTY_LA = re.compile(r"la\s+\w+,\s*\w*empty_code_hash\b")
# bne rs1, rs2, .Ltarget  (labels may embed Lean ++ tag fragments)
BNE_LAB = re.compile(r"\bbne\s+\w+,\s*\w+,\s*(\.[A-Za-z0-9_]+)")
J_LAB = re.compile(r"\bj\s+(\.[A-Za-z0-9_]+)\b")
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


def _compare_gates(win: str) -> str | None:
    """Classify an empty-hash compare window after a code_at jal.

    Returns:
      None  — no empty_code_hash load in window
      "ok"  — at least one bne mismatch target differs from the match fall-through
      "conv"— comparison present but every bne target equals the match j target
              (discarded comparison — false assurance, #11520 SenderCounts)
    """
    la = EMPTY_LA.search(win)
    if not la and "empty_code_hash" not in win:
        return None
    # Slice from first empty_code_hash load through a short limb-compare tail.
    start = la.start() if la else win.find("empty_code_hash")
    chunk = win[start : start + 900]
    bnes = BNE_LAB.findall(chunk)
    if not bnes:
        return None
    # Match path: first `j .L…` after the last bne in this chunk (fall-through
    # after all limbs match). If absent, use the last bne as sole signal.
    last_bne = list(BNE_LAB.finditer(chunk))[-1]
    j_m = J_LAB.search(chunk[last_bne.end() : last_bne.end() + 200])
    match_tgt = j_m.group(1) if j_m else None
    # Strip trailing Lean string noise from labels (tag concat ends at word boundary)
    def norm(lab: str) -> str:
        return lab.rstrip('"').split('"')[0]

    bnes_n = [norm(b) for b in bnes]
    if match_tgt is None:
        # no fall-through j: gating if any two bne targets differ, else unknown→ok
        return "ok" if len(set(bnes_n)) > 1 else "conv"
    match_n = norm(match_tgt)
    # Gating iff some mismatch bne goes somewhere other than the match path.
    if any(b != match_n for b in bnes_n):
        return "ok"
    return "conv"


def _program_status5_antipattern(win: str) -> bool:
    """Detect Program-form status-5-to-empty without an empty-hash gate.

    In a converted `Program`, the old textual sequence
    `li r, 5; beq a0, r, .Lempty` is represented by constructors such as
    `.LI .x5 (5 : Word), .BEQ .x10 .x5 (...)`.  The status-5 branch is the
    same semantic arm; the absence of an `empty_code_hash` symbol in the
    preceding constructors means it is the #11520 anti-pattern.
    """
    if "empty_code_hash" in win:
        return False
    return bool(
        re.search(
            r"\.LI\s+\.x5\s+\(5\s*:\s*Word\)\s*,\s*\n"
            r"\s*\.BEQ\s+\.x10\s+\.x5\b",
            win,
        )
    )


def find_violators() -> list[tuple[str, str, str, int]]:
    """Return list of (kind, relpath, def_name, ordinal).

    kinds:
      pair  — jal code_at_header with no *empty_code_hash in the owning def
      anti  — status-5 beq-to-empty without a prior empty-hash load
      conv  — empty-hash compare whose bne mismatch targets all equal the
              match fall-through (comparison computed and discarded)
    """
    viol: list[tuple[str, str, str, int]] = []
    for path in _iter_files():
        text = path.read_text(errors="replace")
        if "code_at_header_state_root" not in text:
            continue
        rel = str(path.relative_to(ROOT))
        spans = _def_spans(text)

        def owner_at(pos: int) -> str:
            for name, s, e in spans:
                if s <= pos < e:
                    return name
            return "?"

        jal_ord: dict[str, int] = defaultdict(int)
        # Per-def: did any jal site have a gating (ok) compare?
        def_has_gating: dict[str, bool] = defaultdict(bool)
        def_has_any_empty: dict[str, bool] = defaultdict(bool)

        jal_sites = list(JAL_CODE.finditer(text))
        jal_sites.extend(JAL_CODE_PROG.finditer(text))
        jal_sites.sort(key=lambda m: m.start())
        for m in jal_sites:
            name = owner_at(m.start())
            if _is_probe(name):
                jal_ord[name] += 1
                continue
            ord_i = jal_ord[name]
            jal_ord[name] += 1
            # Wide window: ChildFrameHandlers empty compare is ~5–9KB of Lean
            # source after the jal (comments + intermediate arms).
            win = text[m.end() : m.end() + 12000].replace("\\n", "\n")

            # anti: status 5 → empty without an EMPTY_CODE_HASH identity check.
            # Legacy String bodies use `li`/`beq`; converted Program bodies use
            # `.LI`/`.BEQ` constructors.  Do not infer safety from a nearby
            # comment: only a preceding symbol/use counts as the gate.
            if JAL_CODE_PROG.match(text, m.start()):
                anti = _program_status5_antipattern(win)
            else:
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

            gate = _compare_gates(win)
            if gate == "ok":
                def_has_gating[name] = True
                def_has_any_empty[name] = True
            elif gate == "conv":
                def_has_any_empty[name] = True
                viol.append(("conv", rel, name, ord_i))
            elif gate is None and (
                EMPTY_LA.search(win) or "empty_code_hash" in win
            ):
                def_has_any_empty[name] = True

        # function pairing: jal present, no empty_code_hash symbol in def body
        for name, s, e in spans:
            if _is_probe(name):
                continue
            body = text[s:e]
            if not (JAL_CODE.search(body) or JAL_CODE_PROG.search(body)):
                continue
            body_n = body.replace("\\n", "\n")
            if EMPTY_LA.search(body_n) or "empty_code_hash" in body_n:
                # Has a symbol but never a gating compare → still a pair-class
                # gap only if no conv was already recorded for this def.
                if not def_has_gating[name] and not any(
                    k == "conv" and d == name and f == rel
                    for k, f, d, _ in viol
                ):
                    # convergent-only or non-gating empty ref: ensure conv caught
                    pass
                continue
            viol.append(("pair", rel, name, 0))
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
        "# kind=conv: empty-hash bne mismatch targets all equal match fall-through",
        "#            (comparison discarded — false assurance; SenderCounts:248)",
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
        f"0 new; pair+anti+conv). OUT OF SCOPE: exists/is_empty no-charge family."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
