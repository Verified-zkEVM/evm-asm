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
  3. GATING (not mere presence): after `la …empty_code_hash`, the contiguous
     limb `bne` mismatch targets must not all equal the match fall-through
     `j` target. Convergence = discarded comparison = false assurance
     (kind=conv). SenderCounts:248 is the proof case — every bne and the
     final j go to `.Leas_we_ok`.
  4. POLARITY: a mismatch must enter a path whose control-flow body reaches a
     rejecting sink. A mismatch routed to the benign empty path is a polarity
     violation (kind=polarity), even when the compare is present and its
     targets differ. The sink check follows local labels and looks for failure
     result/status writes. It also recognizes the project idiom where the
     path sets a nonzero set-only .bss flag and a cross-file terminal `bnez`
     consumes that flag before writing `bv_fail_code`; a flag write alone is
     not a sink. Label names alone are not enough.

Allow-list: scripts/code-preimage-empty-hash-allow.txt
  lines: kind\\tfile\\tdef\\tordinal   kind in {pair, anti, conv, polarity}
EXPECTED_VIOLATOR_COUNT must match the allow-list length. The count may move
UP when polarity-aware classification exposes an existing debt that the old
detector could not see; a down-ratchet still requires an explicit same-commit
site fix (same durability rule as EXPECTED_ANNOTATION_COUNT / #11505).

OUT OF SCOPE (different family — do not count as covered by this gate):
  account_exists_at_header_state_root / account_is_empty_at_header_state_root
  callers that treat nonzero as "no charge" (ChildFrameHandlers:974-989,
  BlockVerdictSimpleTransferGas, Selfdestruct, ChildFrameHandlerTailHelpers
  exists/empty path). Tracked separately (#11526 FA-directional undercharge).

Usage:
  python3 scripts/check-code-preimage-empty-hash.py
  python3 scripts/check-code-preimage-empty-hash.py --write-allowlist
  python3 scripts/check-code-preimage-empty-hash.py --self-test
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
EXPECTED_VIOLATOR_COUNT = 1

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
# A local label definition in either a plain assembly string or a string with
# a dynamic `++ tag ++` suffix. The captured prefix is the same normalized
# prefix returned by BNE_LAB, which makes tagged helper bodies followable
# without pretending the tag is a concrete label.
LABEL_DEF = re.compile(r'(?m)(?:^|[\n"])\s*(\.[A-Za-z0-9_]+)[^:\n]*:')
BRANCH_LAB = re.compile(
    r"\b(?:j|beq|bne|beqz|bnez|blt|bltu|bge|bgeu)"
    r"(?:\s+[^,\n]+,){0,2}\s*(\.[A-Za-z0-9_]+)\b"
)
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


def _asm_text(text: str) -> str:
    """Turn Lean string escapes into enough assembly text for local scans."""
    return text.replace("\\n", "\n").replace("\\t", "\t")


def _label_bodies(text: str) -> dict[str, str]:
    """Return bodies keyed by normalized local-label prefix.

    Codegen sources often spell a label as `".Lfail_" ++ tag ++ ":\\n"`.
    Capturing only the prefix intentionally mirrors BNE_LAB; this is a source
    scan, not an attempt to evaluate Lean's string concatenation.
    """
    asm = _asm_text(text)
    starts = list(LABEL_DEF.finditer(asm))
    return {
        m.group(1): asm[m.end() : starts[i + 1].start() if i + 1 < len(starts) else len(asm)]
        for i, m in enumerate(starts)
    }


def _body_sets_nonzero_flag(body: str, flag: str) -> bool:
    """Recognize a set-only latch write in one local-label body."""
    asm = _asm_text(body)
    for la in re.finditer(rf"\bla\s+(\w+),\s*{re.escape(flag)}\b", asm):
        reg = la.group(1)
        tail = asm[la.end() : la.end() + 220]
        if re.search(
            rf"\bli\s+\w+,\s*(?:0x[1-9a-fA-F][0-9a-fA-F]*|[1-9][0-9]*)\b"
            rf"[\s\S]*?\bsd\s+\w+,\s*0\({re.escape(reg)}\)",
            tail,
        ):
            return True
    return False


def _terminal_flag_names(
    sources: list[str], labels: dict[str, str]
) -> set[str]:
    """Find set-only flags whose bnez reader reaches a rejection sink.

    This is deliberately cross-file: a resolver may set a .bss flag and return
    its published status, while the receipts tail consumes that flag at the
    terminal verdict gate. A local mismatch-target walk cannot see that gate.
    """
    candidates: set[str] = set()
    for source in sources:
        asm = _asm_text(source)
        candidates.update(
            m.group(2)
            for m in re.finditer(r"\bla\s+(\w+),\s*([A-Za-z_][A-Za-z0-9_]*)\b", asm)
            if m.group(2).endswith("_flag")
        )

    terminal: set[str] = set()
    for flag in candidates:
        has_nonzero_write = False
        has_reader = False
        unknown_reader = False
        reader_targets: set[str] = set()
        for source in sources:
            asm = _asm_text(source)
            for la in re.finditer(rf"\bla\s+(\w+),\s*{re.escape(flag)}\b", asm):
                reg = la.group(1)
                tail = asm[la.end() : la.end() + 260]
                if re.search(rf"\bsd\s+zero,\s*0\({re.escape(reg)}\)", tail):
                    continue
                if re.search(
                    rf"\bli\s+\w+,\s*(?:0x[1-9a-fA-F][0-9a-fA-F]*|[1-9][0-9]*)\b"
                    rf"[\s\S]*?\bsd\s+\w+,\s*0\({re.escape(reg)}\)",
                    tail,
                ):
                    has_nonzero_write = True
                    continue
                ld = re.search(rf"\bld\s+(\w+),\s*0\({re.escape(reg)}\)", tail)
                if ld:
                    bnez = re.search(
                        rf"\bbnez\s+{re.escape(ld.group(1))},\s*(\.[A-Za-z0-9_]+)",
                        tail[ld.end() :],
                    )
                    if bnez:
                        has_reader = True
                        reader_targets.add(bnez.group(1))
                    else:
                        unknown_reader = True
                    continue
                unknown_reader = True
        if (
            has_nonzero_write
            and has_reader
            and not unknown_reader
            and reader_targets
            and all(_label_reaches_reject(target, labels) is True for target in reader_targets)
        ):
            terminal.add(flag)
    return terminal


def _label_reaches_reject(
    label: str,
    labels: dict[str, str],
    terminal_flags: set[str] | frozenset[str] = frozenset(),
) -> bool | None:
    """Prove a local branch target has a rejecting outcome by source shape.

    The rejection result is not uniformly named across the guest. Some
    routines write bv_fail_code; status-oriented routines write bv_stop_code
    from a `_fail` sink; child-frame routines push zero and clear result cells
    before their failure return. A local body may also set a set-only flag whose
    cross-file terminal consumer writes bv_fail_code; `terminal_flags` carries
    only flags whose consumer was independently resolved. Require those body
    markers in addition to any label spelling, then follow local branches for
    intermediate labels such as `_lookup_done`.
    """
    pending = [label]
    seen: set[str] = set()
    saw_body = False
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        body = labels.get(current)
        if body is None:
            continue
        saw_body = True
        body_l = body.lower()
        if "bv_fail_code" in body_l:
            return True
        if any(_body_sets_nonzero_flag(body, flag) for flag in terminal_flags):
            return True
        if "_fail" in current.lower() and (
            "bv_stop_code" in body_l
            or re.search(r"\bsd\s+x0\s*,", body_l)
            or re.search(r"\b(?:li|addi)\s+(?:a0|x10|t1)\s*,\s*[0-9]+\b", body_l)
        ):
            return True
        for target in BRANCH_LAB.findall(body):
            if target not in seen:
                pending.append(target)
    # A target synthesized in another helper may have no local definition in
    # this def. That is not evidence of benign-empty routing; leave it
    # unclassified rather than manufacturing a polarity finding from a
    # missing instrument.
    return False if saw_body else None


def _compare_gates(
    win: str,
    owner_body: str | None = None,
    global_labels: dict[str, str] | None = None,
    terminal_flags: set[str] | frozenset[str] = frozenset(),
) -> str | None:
    """Classify an empty-hash compare window after a code_at jal.

    Returns:
      None  — no empty_code_hash load in window
      "ok"  — mismatch targets reach a rejecting local sink
      "conv"— comparison present but every bne target equals the match j target
              (discarded comparison — false assurance, #11520 SenderCounts)
      "polarity" — a mismatch target is not shown to reach rejection
    """
    la = EMPTY_LA.search(win)
    if not la and "empty_code_hash" not in win:
        return None
    # Slice from first empty_code_hash load through a short limb-compare tail.
    start = la.start() if la else win.find("empty_code_hash")
    chunk = win[start : start + 900]
    bne_ms = list(BNE_LAB.finditer(chunk))
    if not bne_ms:
        return None

    # Keep only the contiguous limb compare. Looking at every later bne was
    # the old false assurance: an unrelated branch can make a bad four-limb
    # compare appear polarity-aware. Between limbs we permit only loads and
    # string-concatenation noise; the first control-flow instruction ends it.
    limb_ms = [bne_ms[0]]
    for nxt in bne_ms[1:]:
        between = chunk[limb_ms[-1].end() : nxt.start()]
        if re.search(
            r"\b(?:bne|beq|bnez|beqz|blt|bltu|bge|bgeu|j|jal|ret|call|li|mv|sd|sw)\b",
            between,
        ) or not re.search(r"\bld\b", between):
            break
        limb_ms.append(nxt)

    # Match path: first `j .L…` after the last contiguous limb (fall-through
    # after all limbs match).
    last_bne = limb_ms[-1]
    j_m = J_LAB.search(chunk[last_bne.end() : last_bne.end() + 200])
    match_tgt = j_m.group(1) if j_m else None
    # Strip trailing Lean string noise from labels (tag concat ends at word boundary)
    def norm(lab: str) -> str:
        return lab.rstrip('"').split('"')[0]

    bnes_n = [norm(m.group(1)) for m in limb_ms]
    if match_tgt is None:
        # No fall-through j means the source does not establish the match
        # path. Require a sink proof when a local body is available; a set of
        # same-target mismatch branches can still be a valid deferred reject.
        labels = global_labels or (_label_bodies(owner_body) if owner_body is not None else {})
        sink_results = [
            _label_reaches_reject(target, labels, terminal_flags)
            for target in set(bnes_n)
        ]
        return "ok" if all(result is not False for result in sink_results) else "polarity"
    match_n = norm(match_tgt)
    if all(b == match_n for b in bnes_n):
        return "conv"
    labels = global_labels or (_label_bodies(owner_body) if owner_body is not None else {})
    mismatch_targets = {b for b in bnes_n if b != match_n}
    sink_results = [
        _label_reaches_reject(target, labels, terminal_flags)
        for target in mismatch_targets
    ]
    if all(result is not False for result in sink_results):
        return "ok"
    return "polarity"


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
    file_texts = [(path, path.read_text(errors="replace")) for path in _iter_files()]
    global_labels: dict[str, str] = {}
    for _, text in file_texts:
        global_labels.update(_label_bodies(text))
    terminal_flags = _terminal_flag_names(
        [text for _, text in file_texts], global_labels
    )

    for path, text in file_texts:
        if "code_at_header_state_root" not in text:
            continue
        rel = str(path.relative_to(ROOT))
        spans = _def_spans(text)

        def owner_at(pos: int) -> str:
            for name, s, e in spans:
                if s <= pos < e:
                    return name
            return "?"

        def owner_body_at(pos: int) -> str:
            for _, s, e in spans:
                if s <= pos < e:
                    return text[s:e]
            return ""

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

            gate = _compare_gates(
                win,
                owner_body_at(m.start()),
                global_labels,
                terminal_flags,
            )
            if gate == "ok":
                def_has_gating[name] = True
                def_has_any_empty[name] = True
            elif gate == "conv":
                def_has_any_empty[name] = True
                viol.append(("conv", rel, name, ord_i))
            elif gate == "polarity":
                def_has_any_empty[name] = True
                viol.append(("polarity", rel, name, ord_i))
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
        "# kind=polarity: mismatch target is not proven to reach rejection",
        "# EXPECTED_VIOLATOR_COUNT in check-code-preimage-empty-hash.py must match.",
        "# A polarity-aware reclassification may raise the honest count; ratchet",
        "# down only with a same-commit site fix and coordinator review.",
        "",
    ]
    for kind, f, d, o in viol:
        lines.append(f"{kind}\t{f}\t{d}\t{o}")
    ALLOW_PATH.write_text("\n".join(lines) + "\n")


def _self_test() -> None:
    """Exercise polarity and the contiguous-limb boundary without Lean.

    The late unrelated branch is the regression that motivated this test: the
    old 900-character scan could see it and incorrectly bless a bad empty
    route. The synthetic owner body gives the positive case a real failure
    sink, so the test checks the same body-following mechanism as the gate.
    """
    owner = (
        '".Lreject:\\n" ++ '
        '"  la t0, bv_fail_code\\n" ++ '
        '"  sd t1, 0(t0)\\n" ++ '
        '".Lempty:\\n" ++ '
        '"  li a0, 2\\n" ++ '
        '".Lempty_bad:\\n" ++ "  li a0, 2\\n"'
    )
    good = (
        "la t1, empty_code_hash\n"
        "ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lreject\n"
        "ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lreject\n"
        "ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lreject\n"
        "ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lreject\n"
        "j .Lempty\n"
    )
    bad = good.replace(".Lreject", ".Lempty_bad")
    masked_bad = bad + "bne t2, t3, .Lreject\n"
    checks = {
        "reject polarity": _compare_gates(good, owner) == "ok",
        "benign-empty polarity": _compare_gates(bad, owner) == "polarity",
        "late branch cannot mask": _compare_gates(masked_bad, owner) == "polarity",
        "convergence": _compare_gates(good.replace(".Lreject", ".Lempty"), owner) == "conv",
    }
    latch_source = (
        ".Lset:\n"
        "  la t0, test_unresolved_flag\n"
        "  li t1, 1; sd t1, 0(t0)\n"
        ".Lgate:\n"
        "  la t0, test_unresolved_flag; ld t0, 0(t0); bnez t0, .Lfail\n"
        ".Lfail:\n"
        "  li t1, 75; la t2, bv_fail_code; sd t1, 0(t2)\n"
    )
    latch_labels = _label_bodies(latch_source)
    latch_flags = _terminal_flag_names([latch_source], latch_labels)
    checks["set-only terminal latch"] = "test_unresolved_flag" in latch_flags
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise AssertionError("polarity self-test failed: " + ", ".join(failed))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--write-allowlist",
        action="store_true",
        help="rewrite allow-list to current violators (bootstrap / deliberate shrink)",
    )
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="run synthetic polarity/control-flow checks without scanning the tree",
    )
    args = ap.parse_args()
    if args.self_test:
        _self_test()
        print("check-code-preimage-empty-hash: polarity self-test OK")
        return 0
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
            f"  (all classified violators={len(viol)}; allow={len(allow)}; "
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
        f"0 new; pair+anti+conv+polarity). OUT OF SCOPE: exists/is_empty "
        f"no-charge family."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
