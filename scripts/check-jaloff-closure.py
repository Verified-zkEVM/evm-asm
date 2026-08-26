#!/usr/bin/env python3
"""jalOff-closure gate (GH #12403, cr track): every `jalOff` target of every
`guestImageEntries` Program must itself be a `guestImageEntries` first
component.

WHY THIS GATE EXISTS.  `guestImageCodeReq` (EvmAsm/Codegen/Proofs/GuestImage.lean)
asserts the guest's code memory contains exactly the registered entry Programs.
A Hoare triple anchored at an entry PC composes with a callee only while the
callee's fetch is pinned by that CodeReq: `cpsTripleWithin_needs_entry_code`
(TopComposition.lean) shows that executing an address the CodeReq leaves
unpinned makes the triple FALSE, not merely unproven.  An entry Program that
`jal`s into an UNREGISTERED routine is therefore a phase-instantiation blocker
even when the callee carries a complete proven spec — the measured instance on
main is `rlp_field_to_u64` (registered) calling `rlp_content_to_u64`
(spec `rlp_content_to_u64_spec_within` exists; no `guestImageEntries` row).

Nothing else checks this.  The byte-identity gate
(`check-guest-image-program-bytes.py`) compares registered Programs against
the linked ELF; the liveness gate (`check_routine_liveness.py`) censuses
symbol-level references; neither asks whether a registered Program's control
flow stays inside the registered set.  `check-no-hardcoded-guest-pc.sh` gates
the jalOff argument SHAPE, not the target's membership.

WHAT IT CHECKS.  Pure source scan, seconds, no build:

  1. Parse the `(GuestAddrs.<sym>, <prog>)` rows of
     EvmAsm/Codegen/Proofs/GuestImageEntries.lean.
  2. Index every top-level `def`/`abbrev` body under EvmAsm/.
  3. From each entry Program, transitively expand referenced definitions
     (aliases like `rlpFieldToU64_prog := rlpFieldToU64Wrapper_prog`,
     layout-parameterised generators like `…_prog_of guestLayout`,
     `++`-composites, `flatten` bodies) and collect every `jalOff` first
     argument:
       * `GuestAddrs.<t>`                 -> target symbol `t`
       * `(GuestAddrs.<t> + N)`           -> internal jump when `t` is the
                                             entry's own symbol; otherwise a
                                             mid-extent cross jump (flagged)
       * `<L>.<f>` / `(<L>.<f> + N)`      -> GuestLayout field; `guestLayout`
                                             binds every field FROM
                                             `GuestAddrs.<f>`, so the target
                                             symbol is `f`
       * any other anchor (offline-Addrs constants, bare PC abbreviations)
     in an entry closure                  -> flagged separately (not an entry
                                             first component by construction)
  4. Every collected target symbol must be a `guestImageEntries` first
     component.  Violations are reported as (entry, target) pairs; the
     annotated allowlist scripts/jaloff-closure-allow.txt (target, issue,
     reason — the rowed-liveness-allow.txt contract) exempts a KNOWN hole.
     An allowlist row whose target is no longer violated is reported
     STALE-EXEMPTION and fails: the file cannot outlive its findings.

LIMITATIONS (textual over-approximation, accepted): the expansion follows
identifiers, not elaboration, so a helper shared with a non-entry context
attributes all of its `jalOff`s to the entry.  A false positive is resolved
by inspecting the reported (entry, def, target) triple — the report always
names the defining file and line.  The kernel-side `decide` version of this
gate (exact, no approximation) is follow-up work once the generated artefacts
settle.

SELF-TEST (the check-region-overlap.py standard: a gate never seen to fail is
indistinguishable from one that cannot): `--self-test` injects an in-memory
synthetic entry whose Program `jalOff`s an unregistered target and asserts
the gate flags exactly it; the real tree is never modified.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENTRIES = os.path.join(REPO, "EvmAsm", "Codegen", "Proofs", "GuestImageEntries.lean")
ALLOWLIST = os.path.join(REPO, "scripts", "jaloff-closure-allow.txt")

ROW_RE = re.compile(
    r"\(GuestAddrs\.([A-Za-z_][A-Za-z0-9_']*),\s*([A-Za-z_][A-Za-z0-9_'.]*)\)")

# Top-level declaration openers (column 0).  Bodies run to the next opener.
DECL_RE = re.compile(
    r"^(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)")
BOUNDARY_RE = re.compile(
    r"^(?:/-|/--|\(noncomputable|@\[|def|abbrev|theorem|lemma|example|instance|"
    r"structure|inductive|class|axiom|opaque|namespace|section|end\b|mutual|"
    r"#guard|#eval|#check|open\b|import\b|variable\b)")

IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")

# Never expand these: the relocation helpers themselves.
NO_EXPAND = {"jalOff", "jalOffInRange", "laHi", "laLo", "brOff", "GuestAddrs"}

# Bare identifiers resolve against EVERY top-level def in EvmAsm/, so generic
# names (`prog`, `code`, `block`, `ADDI`, …) would drag the whole machine
# model into every entry's closure.  A bare reference is followed only when
#   * it resolves to a def IN THE SAME FILE (program fragments are defined
#     next to the Program that cites them: wrappers, `…Body`, offset helpers),
#     or
#   * its name carries a program suffix (`…_prog`, `…_prog_of`,
#     `…_prog_with_cap`) — the cross-file bare-reference shape used by the
#     layout bridge files (`foo_prog := foo_prog_of guestLayout`),
# and the target def can actually carry instructions (census of every
# jalOff-containing def on main: Program / List Instr / BitVec 21 / Word /
# CodeReq / List RoutineEntry / Stmt) or itself applies `jalOff`.
# Dotted references (`Ns.foo_prog`) are deliberate cross-module links and are
# always followed (by last segment).
# Return-type shapes that can carry an instruction-bearing body.  This must
# match the declaration's *return* annotation, not a parameter annotation:
# ``def f (x : Word) : Fn := ...`` is not a Program and following it pulls the
# whole proof tower into the textual closure (including unrelated jalOffs).
# The first-line scanner below recognizes the top-level colon after any
# parenthesized/braced binders; declarations whose return type is wrapped onto
# later lines are still eligible through the explicit ``jalOff`` test.
EXPAND_RETURN_TYPES = {
    "Program", "List Instr", "Stmt", "BitVec 21", "Word", "CodeReq",
    "List RoutineEntry",
}

PROG_SUFFIX_RE = re.compile(r"(?:_prog|_prog_of|_prog_with_cap)$")


def expandable(body: str) -> bool:
    first = body.splitlines()[0]
    # A declaration can contain colons in parameter binders.  Find only a
    # colon at nesting depth zero, i.e. the return annotation before `:=`.
    m = re.match(
        r"^(?:(?:noncomputable|private|protected)\s+)*"
        r"(?:def|abbrev)\s+[A-Za-z_][A-Za-z0-9_']*\b", first)
    return_type = None
    if m:
        tail = first[m.end():]
        depth = 0
        for i, ch in enumerate(tail):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth = max(0, depth - 1)
            elif ch == ":" and depth == 0 and not tail[i:i + 2] == ":=":
                candidate = tail[i + 1:].split(":=", 1)[0].strip()
                return_type = candidate
    return (return_type in EXPAND_RETURN_TYPES or
            "jalOff" in strip_noise(body))

SELFTEST_ENTRY = "__jaloff_closure_selftest_entry"
SELFTEST_PROG = "__jaloffClosureSelftest_prog"
SELFTEST_TARGET = "__jaloff_closure_unregistered_target"


def parse_entries(text: str) -> list[tuple[str, str]]:
    rows = ROW_RE.findall(text)
    if not rows:
        raise RuntimeError(f"no GuestImageEntries rows found in {ENTRIES}")
    seen: set[str] = set()
    for entry, _prog in rows:
        if entry in seen:
            raise RuntimeError(f"duplicate GuestAddrs.{entry} in {ENTRIES}")
        seen.add(entry)
    return rows


def index_defs(files: dict[str, str]) -> dict[str, list[tuple[str, int, str]]]:
    """name -> [(path, def-line, body-text)] for every top-level def/abbrev."""
    defs: dict[str, list[tuple[str, int, str]]] = {}
    for path, text in files.items():
        lines = text.splitlines()
        starts: list[int] = [i for i, ln in enumerate(lines) if BOUNDARY_RE.match(ln)]
        starts.append(len(lines))
        for k in range(len(starts) - 1):
            i = starts[k]
            m = DECL_RE.match(lines[i])
            if not m:
                continue
            body = "\n".join(lines[i:starts[k + 1]])
            defs.setdefault(m.group(1), []).append((path, i + 1, body))
    return defs


def resolve(token: str, defs: dict[str, list[tuple[str, int, str]]]) -> str | None:
    """Map a referenced identifier to a def name (exact, else last segment)."""
    if token in defs:
        return token
    last = token.rsplit(".", 1)[-1]
    if last in defs:
        return last
    return None


def reachable_bodies(
    prog: str, defs: dict[str, list[tuple[str, int, str]]]
) -> list[tuple[str, str, int, str]]:
    """All (name, path, line, body) reachable from `prog` via referenced defs."""
    out: list[tuple[str, str, int, str]] = []
    seen: set[str] = set()
    worklist = [prog]
    while worklist:
        name = worklist.pop()
        if name in seen or name in NO_EXPAND:
            continue
        seen.add(name)
        for path, line, body in defs.get(name, []):
            out.append((name, path, line, body))
            for tok in IDENT_RE.findall(strip_noise(body)):
                tgt = None
                if "." in tok:
                    tgt = resolve(tok, defs)  # dotted: deliberate cross-module
                elif tok in defs:
                    cands = defs[tok]
                    same = [c for c in cands if c[0] == path]
                    pool = same if same else (
                        cands if PROG_SUFFIX_RE.search(tok) else [])
                    if any(expandable(b) for _, _, b in pool):
                        tgt = tok
                if tgt is not None and tgt not in seen:
                    worklist.append(tgt)
    return out


def strip_noise(text: str) -> str:
    """Blank out comments and string literals (positions preserved via spaces).

    Without this, prose like "-- the internal brOff/jalOff offsets stay
    valid" parses as a `jalOff` application with first arg `offsets`.
    Lean block comments nest; strings use backslash escapes.
    """
    out = list(text)
    i, n = 0, len(text)
    depth = 0  # block-comment nesting
    while i < n:
        two = text[i:i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
            elif two == "-/":
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif two == "/-":
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        elif text[i] == '"':
            out[i] = " "
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    out[i] = out[i + 1] = " "
                    i += 2
                else:
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
            if i < n:
                out[i] = " "
                i += 1
        else:
            i += 1
    return "".join(out)


def parse_jaloff_targets(body: str) -> list[tuple[int, str]]:
    """(line-offset, first-arg-text) for every `jalOff` application."""
    body = strip_noise(body)
    out: list[tuple[int, str]] = []
    for m in re.finditer(r"\bjalOff\b\s*", body):
        i = m.end()
        if i >= len(body):
            continue
        if body[i] == "(":
            depth = 0
            j = i
            while j < len(body):
                if body[j] == "(":
                    depth += 1
                elif body[j] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            arg = body[i:j + 1]
        else:
            m2 = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", body[i:])
            if not m2:
                continue
            arg = m2.group(0)
        out.append((body.count("\n", 0, m.start()) + 1,
                    re.sub(r"\s+", " ", arg)))
    return out


def classify_target(arg: str) -> tuple[str, str | None]:
    """(kind, target-symbol) of a jalOff first argument.

    kind: 'guestaddrs'  -> plain or offset GuestAddrs anchor
          'layout'      -> GuestLayout field (bound from GuestAddrs by the
                           unique instance, so the field name IS the symbol)
          'other'       -> non-GuestAddrs anchor (offline-Addrs constant,
                           bare PC abbreviation, …): never an entry row
    """
    inner = arg.strip()
    if inner.startswith("(") and inner.endswith(")"):
        inner = inner[1:-1].strip()
    m = re.match(r"^GuestAddrs\.([A-Za-z_][A-Za-z0-9_']*)\s*(?:[+-]\s*\d+)?$", inner)
    if m:
        return ("guestaddrs", m.group(1))
    m = re.match(
        r"^([A-Za-z_][A-Za-z0-9_']*)\.([A-Za-z_][A-Za-z0-9_']*)\s*(?:[+-]\s*\d+)?$",
        inner)
    if m and not m.group(1).endswith("Addrs"):
        return ("layout", m.group(2))
    return ("other", None)


def collect_violations(
    rows: list[tuple[str, str]],
    defs: dict[str, list[tuple[str, int, str]]],
) -> tuple[list[tuple[str, str, str, int, str]], list[str]]:
    """[(entry, target, def-file, def-line, kind)] + warnings."""
    entry_syms = {e for e, _ in rows}
    violations: list[tuple[str, str, str, int, str]] = []
    warnings: list[str] = []
    for entry, prog in rows:
        if prog not in defs:
            warnings.append(f"entry {entry}: program {prog} has no def (skipped)")
            continue
        for name, path, line, body in reachable_bodies(prog, defs):
            for off, arg in parse_jaloff_targets(body):
                kind, target = classify_target(arg)
                if kind == "other":
                    violations.append((entry, arg, path, line + off - 1, "other"))
                    continue
                assert target is not None
                if "+" in arg or "-" in arg:
                    # Offset anchor: fine only when it is the entry's own
                    # symbol (an internal long jump within the same Program).
                    if target == entry:
                        continue
                    violations.append(
                        (entry, target, path, line + off - 1, "mid-extent"))
                elif target not in entry_syms:
                    violations.append((entry, target, path, line + off - 1, kind))
    return violations, warnings


def parse_allowlist(text: str) -> dict[str, str]:
    """target -> raw reason line (format: <target>\\tissue=<NNNN>\\t<reason>)."""
    out: dict[str, str] = {}
    for ln, line in enumerate(text.splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 3 or not parts[1].startswith("issue="):
            raise RuntimeError(
                f"{ALLOWLIST}:{ln}: want '<target>\\tissue=<NNNN>\\t<reason>'")
        out[parts[0]] = line
    return out


def report(
    violations: list[tuple[str, str, str, int, str]], allow: dict[str, str]
) -> int:
    bad = [(e, t, p, l, k) for e, t, p, l, k in violations
           if t not in allow or k in ("other", "mid-extent")]
    # (other/mid-extent rows are never allowlisted: they are structural, not
    # a known hole — an offset/non-entry anchor must be fixed, not exempted.)
    stale = set(allow) - {t for _e, t, _p, _l, k in violations if k == "guestaddrs"
                          or k == "layout"}
    rc = 0
    if bad:
        rc = 1
        print(f"FAIL: {len(bad)} jalOff target(s) leave the registered entry set:")
        for e, t, p, l, k in sorted(bad):
            rel = os.path.relpath(p, REPO)
            print(f"  {e} -> {t}  [{kind_label(k)}]  ({rel}:{l})")
    exempted = [(e, t) for e, t, _p, _l, k in violations
                if t in allow and k in ("guestaddrs", "layout")]
    if exempted:
        print(f"allowlisted known holes ({len(exempted)}):")
        for e, t in sorted(set(exempted)):
            print(f"  {e} -> {t}    ({allow[t]})")
    if stale:
        rc = 1
        for t in sorted(stale):
            print(f"STALE-EXEMPTION: allowlist row '{t}' is no longer violated;"
                  " remove it (the hole is closed or the caller changed)")
    if not rc:
        print(f"PASS: all jalOff targets of the {GLOBAL_ROW_COUNT} registered"
              " entries stay within the registered entry set"
              + (f" ({len(exempted)} allowlisted)" if exempted else ""))
    return rc


def kind_label(k: str) -> str:
    return {"guestaddrs": "unregistered GuestAddrs target",
            "layout": "unregistered GuestLayout-field target",
            "mid-extent": "offset cross-entry jump (not a first component)",
            "other": "non-GuestAddrs anchor in entry closure"}[k]


GLOBAL_ROW_COUNT = 0


def load_corpus() -> dict[str, str]:
    files: dict[str, str] = {}
    root = os.path.join(REPO, "EvmAsm")
    for dirpath, _dirs, names in os.walk(root):
        for n in names:
            if n.endswith(".lean"):
                p = os.path.join(dirpath, n)
                with open(p, encoding="utf-8") as f:
                    files[p] = f.read()
    return files


def main() -> int:
    global GLOBAL_ROW_COUNT
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--self-test", action="store_true",
                    help="inject an in-memory violation and require detection")
    args = ap.parse_args()

    files = load_corpus()
    rows = parse_entries(files[ENTRIES])
    allow = parse_allowlist(open(ALLOWLIST, encoding="utf-8").read())

    if args.self_test:
        # In-memory only: add a synthetic registered entry whose Program jals
        # an unregistered target, plus its def.  The gate must flag exactly it.
        rows = rows + [(SELFTEST_ENTRY, SELFTEST_PROG)]
        canary = (
            f"def {SELFTEST_PROG} : Program :=\n"
            f"  [ .JAL .x1 (jalOff GuestAddrs.{SELFTEST_TARGET} (0 + 0)) ]\n")
        files["<selftest>"] = canary
        defs = index_defs(files)
        violations, warnings = collect_violations(rows, defs)
        for w in warnings:
            print(f"warning: {w}", file=sys.stderr)
        hits = [v for v in violations
                if v[0] == SELFTEST_ENTRY and v[1] == SELFTEST_TARGET]
        unexpected = [v for v in violations
                      if not (v[0] == SELFTEST_ENTRY) and v[1] not in allow]
        if not hits:
            print("SELF-TEST FAIL: planted violation was not detected")
            return 1
        if unexpected:
            print("SELF-TEST FAIL: unexpected extra violations "
                  f"{[(e, t) for e, t, *_ in unexpected]}")
            return 1
        print("SELF-TEST PASS: planted unregistered jalOff target was flagged")
        return 0

    defs = index_defs(files)
    GLOBAL_ROW_COUNT = len(rows)
    violations, warnings = collect_violations(rows, defs)
    for w in warnings:
        print(f"warning: {w}", file=sys.stderr)
    return report(violations, allow)


if __name__ == "__main__":
    sys.exit(main())
