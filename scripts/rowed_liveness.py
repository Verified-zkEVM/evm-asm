#!/usr/bin/env python3
"""rowed-liveness gate (GH #12381), invoked by scripts/check-rowed-liveness.sh.

THE GAP THIS CLOSES: a registry row asserts "this proven code is part of the
guest's story". `check-routine-liveness.sh` (#11303) answers *is the symbol
PRESENT* — it accepts "appears in the linked guest's symbol census" as
liveness, by design (call-site scanning misses routines reached only through
the linked ELF's own internal calls). Nothing answered *is the symbol CALLED*.
A routine can be emitted into the image, carry a `.proven` row, and never
execute: every gate stays green while the registry advertises a proof about
code that is not on any path.

The class is not hypothetical. #12351 (from `docs/spec-aligned-rewrite-workflow.md`
§2's manual measurement) found three such routines —
`chain_validate_{increasing_timestamps, consecutive_numbers, post_merge_full}` —
duplicated by inline code on the live path. This gate's own instrument found
**five more** of the same class on the 2026-08-14 link (#12386): the four other
`chain_validate_*` leaf checks plus `rlp_field_to_u256_be`.

DIVISION OF LABOUR (the issue's "unify rather than duplicate"): presence is
`check_routine_liveness.py`'s question and stays there — this gate imports that
module's registry parser rather than re-deriving the symbol population, and
treats a rowed symbol that is absent from the image as NOT-IN-IMAGE, reported
and delegated, never re-adjudicated here.

WHAT IT CHECKS: for every distinct `routine "<symbol>"` in
EvmAsm/Progress/Routines.lean that IS in the linked image, require one of:

  CALLED         >= 1 direct `jal`/`j`/tail edge whose target is exactly the
                 symbol's entry address, from a DIFFERENT enclosing symbol.
                 Self-recursion alone is not liveness (SELF-ONLY is a finding:
                 a routine that only calls itself is still unreachable).
  BRANCH-ENTERED a conditional-branch target from another symbol. Not a call,
                 but genuinely entered — reported distinctly so a
                 branch-entered routine is never false-flagged.
  ADDR-TAKEN     its entry address is materialized by an `auipc`+`addi` pair,
                 or appears as a 4/8-byte little-endian word in a non-.text
                 section (a dispatch table). This is the indirect-call escape
                 the issue insists on: "zero direct call sites is not proof of
                 dead code". Reported, never flagged.
  ENTRY-ROOT     the symbol is the ELF entry point.
  ALLOWED        an annotated exemption in scripts/rowed-liveness-allow.txt.

Anything else is a finding. The gate NEVER deletes and never proposes a
deletion by itself: the resolution is a maintainer's choice between removing
code+row (the #12351 pattern, both ledgers in one PR) and annotating why the
symbol lives.

WHY ONE ANNOTATED SECTION AND NOT `[baseline]`/`[known-open]`: the orphan-block
snapshot's two buckets separate long-standing-and-unrefuted from
tracked-live-defect. No such split exists here. Every uncalled rowed symbol is
either a deletion candidate or an indirect-dispatch fact, and BOTH need a
stated reason — a silent "long-standing" bucket would be precisely the rot this
gate exists to prevent. So there is one section, every row carries
`issue=<NNNN>` plus prose, and a row whose symbol has become live is itself a
failure (STALE-EXEMPTION), so the file cannot outlive its findings.

SELF-TEST (`--self-test`, requires no ELF): drives the real `classify()` with
synthetic censuses and asserts, in both directions, that
  * an in-image rowed symbol with no edge of any kind is FLAGGED,
  * the same symbol with a direct call edge is not,
  * a self-recursive-only symbol is still FLAGGED,
  * branch-entered / addr-taken / data-table / entry-root symbols are NOT flagged,
  * an exemption row missing `issue=` is rejected at parse time,
  * an exemption for a symbol that is now called is reported STALE.
The real tree is never modified.
"""

from __future__ import annotations

import argparse
import bisect
import collections
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_ELF = os.path.join(ROOT, "gen-out", "regionmap", "stateless_guest.elf")
ALLOW = os.path.join(ROOT, "scripts", "rowed-liveness-allow.txt")

sys.path.insert(0, os.path.join(ROOT, "scripts"))
# Presence/population parsing is #11303's, not ours (the issue's "unify rather
# than duplicate"). Importing it also means a change to the row syntax updates
# both gates at once.
from check_routine_liveness import registry_symbols  # noqa: E402

SECTION = "[annotated]"
ISSUE_RE = re.compile(r"^issue=(\d+)$")

# Verdicts that count as live.
LIVE = ("CALLED", "BRANCH-ENTERED", "ADDR-TAKEN", "DATA-TABLE", "ENTRY-ROOT",
        "NOT-IN-IMAGE")

CALL_OPS = {"jal", "j", "jump", "call", "tail", "c.j", "c.jal"}
BRANCH_RE = re.compile(r"^(?:c\.)?b(?:eq|ne|lt|ge|ltu|geu|eqz|nez|lez|gez|ltz|gtz)$")
INSN_RE = re.compile(r"^\s*([0-9a-f]+):\s+([0-9a-f ]+)\t(\S+)\s*(.*?)\s*$")
TARGET_RE = re.compile(r"\b([0-9a-f]{4,})\s*(?:<[^>]+>)?$")


def die(msg: str, code: int = 1) -> None:
    print(f"rowed-liveness: {msg}", file=sys.stderr)
    raise SystemExit(code)


def _riscv_tool(env_var: str, tool: str) -> str:
    """Resolve a RISC-V binutils tool across both triple spellings.

    Same convention as `_riscv_tool` in scripts/asm_to_program.py and
    `resolve_riscv_tool` in scripts/codegen-eest-stateless-check.sh: CI installs
    `binutils-riscv64-unknown-elf`, Homebrew ships the identical GNU binutils as
    `riscv64-elf-*`. Without the fallback this gate would skip on macOS, which
    reads as "verified" when nothing ran (#11043, and its named regressions).
    """
    return (os.environ.get(env_var)
            or shutil.which(f"riscv64-unknown-elf-{tool}")
            or shutil.which(f"riscv64-elf-{tool}")
            or f"riscv64-unknown-elf-{tool}")


def _run(tool: str, args: list[str]) -> str:
    if shutil.which(tool) is None:
        die(f"{tool} not found — this gate needs RISC-V binutils (nm/objdump). "
            f"Install binutils-riscv64-unknown-elf (CI) or riscv64-elf-binutils "
            f"(Homebrew); set $RISCV_NM/$RISCV_OBJDUMP to override.")
    proc = subprocess.run([tool, *args], capture_output=True, text=True)
    if proc.returncode != 0:
        die(f"{tool} {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout


def text_symbols(elf: str) -> dict[str, int]:
    """Linked .text symbol -> entry address (linker facts)."""
    nm = _riscv_tool("RISCV_NM", "nm")
    out: dict[str, int] = {}
    for line in _run(nm, [elf]).splitlines():
        parts = line.split()
        if len(parts) != 3 or parts[1].lower() not in ("t", "w"):
            continue
        try:
            out[parts[2]] = int(parts[0], 16)
        except ValueError:
            continue
    return out


def entry_address(elf: str) -> int | None:
    objdump = _riscv_tool("RISCV_OBJDUMP", "objdump")
    for line in _run(objdump, ["-f", elf]).splitlines():
        m = re.search(r"start address 0x([0-9a-f]+)", line)
        if m:
            return int(m.group(1), 16)
    return None


def control_edges(elf: str, sym_addr: dict[str, int]) -> tuple[
        dict[int, set[str]], dict[int, set[str]], set[int]]:
    """Parse the whole-image disassembly once.

    Returns (call_edges, branch_edges, materialized) where the edge maps send a
    TARGET ADDRESS to the set of enclosing symbols the transfer comes FROM, and
    `materialized` holds every address built by an `auipc`+`addi` pair.
    """
    objdump = _riscv_tool("RISCV_OBJDUMP", "objdump")
    dis = _run(objdump, ["-d", elf])

    ordered = sorted(set(sym_addr.values()))
    by_addr: dict[int, str] = {}
    for name, addr in sorted(sym_addr.items()):
        by_addr.setdefault(addr, name)

    def enclosing(addr: int) -> str | None:
        i = bisect.bisect_right(ordered, addr) - 1
        return by_addr[ordered[i]] if i >= 0 else None

    calls: dict[int, set[str]] = collections.defaultdict(set)
    branches: dict[int, set[str]] = collections.defaultdict(set)
    materialized: set[int] = set()
    pending: dict[str, tuple[int, int]] = {}

    for line in dis.splitlines():
        m = INSN_RE.match(line)
        if not m:
            continue
        ia, op, rest = int(m.group(1), 16), m.group(3), m.group(4)
        if op in CALL_OPS or BRANCH_RE.match(op):
            tm = TARGET_RE.search(rest)
            if tm:
                target = int(tm.group(1), 16)
                sink = calls if op in CALL_OPS else branches
                sink[target].add(enclosing(ia) or "?")
        # `la sym` lowers to auipc+addi; the pair is how an indirect dispatch
        # gets a routine's address, so it must count as a reference.
        if op == "auipc":
            am = re.match(r"([a-z0-9]+),\s*0x([0-9a-f]+)$", rest)
            if am:
                pending[am.group(1)] = (ia, int(am.group(2), 16))
        elif op == "addi":
            am = re.match(r"([a-z0-9]+),\s*([a-z0-9]+),\s*(-?\d+)$", rest)
            if am and am.group(2) in pending:
                base, hi = pending[am.group(2)]
                materialized.add((base + (hi << 12) + int(am.group(3)))
                                 & 0xFFFFFFFFFFFFFFFF)
    return dict(calls), dict(branches), materialized


def data_table_addresses(elf: str, wanted: set[int]) -> set[int]:
    """Which `wanted` addresses appear as a 4/8-byte LE word outside .text.

    A jump table lives in .data, so an address there is an indirect reference
    that no disassembly scan can see.
    """
    if not wanted:
        return set()
    objdump = _riscv_tool("RISCV_OBJDUMP", "objdump")
    blobs: dict[str, bytearray] = {}
    cur: str | None = None
    for line in _run(objdump, ["-s", elf]).splitlines():
        m = re.match(r"^Contents of section (\S+):", line)
        if m:
            cur = m.group(1)
            blobs[cur] = bytearray()
            continue
        if cur is None or cur == ".text":
            continue
        m = re.match(r"^\s*[0-9a-f]+\s((?:[0-9a-f]{2,8}\s){1,4})", line)
        if m:
            for group in m.group(1).split():
                try:
                    blobs[cur].extend(bytes.fromhex(group))
                except ValueError:
                    pass
    found: set[int] = set()
    for sec, blob in blobs.items():
        if sec == ".text":
            continue
        for addr in wanted:
            for width in (8, 4):
                if addr >= (1 << (8 * width)):
                    continue
                if blob.find(addr.to_bytes(width, "little")) >= 0:
                    found.add(addr)
                    break
    return found


def load_allow(path: str = ALLOW) -> dict[str, tuple[str, str]]:
    """symbol -> (issue, reason). Every row needs `issue=<NNNN>` AND prose."""
    if not os.path.exists(path):
        return {}
    out: dict[str, tuple[str, str]] = {}
    section: str | None = None
    with open(path, encoding="utf-8") as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.split("#", 1)[0].strip() if raw.lstrip().startswith("#") else raw.rstrip("\n")
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("[") and line.endswith("]"):
                if line != SECTION:
                    die(f"{path}:{lineno}: unknown section {line!r} (want {SECTION})")
                section = line
                continue
            if section is None:
                die(f"{path}:{lineno}: entry before {SECTION}: {line!r}")
            fields = [f.strip() for f in line.split("\t") if f.strip()]
            if len(fields) < 3:
                die(f"{path}:{lineno}: need `<symbol>\\tissue=<NNNN>\\t<reason>`, got {line!r}")
            sym, issue_tok, reason = fields[0], fields[1], " ".join(fields[2:])
            if ISSUE_RE.match(issue_tok) is None:
                die(f"{path}:{lineno}: exemption must cite issue=<NNNN> "
                    f"(got {issue_tok!r} on {sym})")
            if not reason:
                die(f"{path}:{lineno}: exemption for {sym} has no reason")
            if sym in out:
                die(f"{path}:{lineno}: duplicate exemption for {sym}")
            out[sym] = (ISSUE_RE.match(issue_tok).group(1), reason)
    if section is None:
        die(f"{path}: missing {SECTION} section header")
    return out


def classify(rowed: set[str], sym_addr: dict[str, int],
             calls: dict[int, set[str]], branches: dict[int, set[str]],
             materialized: set[int], data_tables: set[int],
             entry: int | None) -> dict[str, str]:
    """Verdict per rowed symbol. Pure function of the censuses — the self-test
    drives exactly this."""
    verdicts: dict[str, str] = {}
    for sym in sorted(rowed):
        addr = sym_addr.get(sym)
        if addr is None:
            # Presence is #11303's question; do not re-adjudicate it here.
            verdicts[sym] = "NOT-IN-IMAGE"
            continue
        if entry is not None and addr == entry:
            verdicts[sym] = "ENTRY-ROOT"
            continue
        callers = calls.get(addr, set())
        if callers - {sym}:
            verdicts[sym] = "CALLED"
        elif (branches.get(addr, set()) - {sym}):
            verdicts[sym] = "BRANCH-ENTERED"
        elif addr in materialized:
            verdicts[sym] = "ADDR-TAKEN"
        elif addr in data_tables:
            verdicts[sym] = "DATA-TABLE"
        elif callers:
            verdicts[sym] = "SELF-ONLY"
        else:
            verdicts[sym] = "UNCALLED"
    return verdicts


def findings(verdicts: dict[str, str], allow: dict[str, tuple[str, str]]
             ) -> tuple[list[tuple[str, str]], list[tuple[str, str]], list[str]]:
    """(unannotated findings, annotated-and-reported, stale exemptions)."""
    new: list[tuple[str, str]] = []
    annotated: list[tuple[str, str]] = []
    for sym, verdict in verdicts.items():
        if verdict in LIVE:
            continue
        if sym in allow:
            annotated.append((sym, verdict))
        else:
            new.append((sym, verdict))
    stale = sorted(s for s in allow
                   if verdicts.get(s, "MISSING") in LIVE
                   or s not in verdicts)
    return new, annotated, stale


def measure(elf: str) -> tuple[set[str], dict[str, str]]:
    if not os.path.exists(elf):
        die(f"{elf} not found — build it with:\n"
            f"  lake build codegen && lake exe codegen --program stateless_guest "
            f"--halt linux93 -o gen-out/regionmap/stateless_guest")
    rowed = registry_symbols()
    if not rowed:
        die("EvmAsm/Progress/Routines.lean yielded no `routine \"<sym>\"` rows — "
            "the row parser is broken (vacuous success forbidden)")
    sym_addr = text_symbols(elf)
    calls, branches, materialized = control_edges(elf, sym_addr)
    wanted = {sym_addr[s] for s in rowed if s in sym_addr}
    data_tables = data_table_addresses(elf, wanted)
    verdicts = classify(rowed, sym_addr, calls, branches, materialized,
                        data_tables, entry_address(elf))
    return rowed, verdicts


def report(rowed: set[str], verdicts: dict[str, str],
           allow: dict[str, tuple[str, str]]) -> int:
    new, annotated, stale = findings(verdicts, allow)
    tally = collections.Counter(verdicts.values())
    for sym, verdict in new:
        print(f"  {verdict:14s} {sym} — rowed in Progress/Routines.lean with no "
              f"call, branch, address-taken or dispatch-table reference on the "
              f"fresh link")
    for sym, verdict in annotated:
        issue, reason = allow[sym]
        print(f"  ANNOTATED      {sym} [{verdict}] issue=#{issue} — {reason}")
    for sym in stale:
        print(f"  STALE-EXEMPTION {sym} — exempted in "
              f"scripts/rowed-liveness-allow.txt but now {verdicts.get(sym, 'absent from the registry')}; "
              f"delete the row")
    summary = ", ".join(f"{v.lower()} {n}" for v, n in sorted(tally.items()))
    print(f"  {len(rowed)} rowed symbols: {summary}")
    if new or stale:
        print(f"check-rowed-liveness: FAILED ({len(new)} unannotated, "
              f"{len(stale)} stale of {len(rowed)} rowed symbols).")
        print("  Resolve each by EITHER deleting the code and its registry row in")
        print("  one PR (the #12351 pattern — both ledgers together), OR adding an")
        print("  annotated row to scripts/rowed-liveness-allow.txt stating why the")
        print("  symbol lives (indirect dispatch, staged wiring + its issue).")
        print("  This gate never deletes and never decides which of the two applies.")
        return 1
    print(f"check-rowed-liveness: OK — {len(rowed)} rowed symbols, "
          f"{tally['CALLED']} called, {len(annotated)} annotated-uncalled "
          f"(reported above, not accepted silently).")
    return 0


def self_test() -> None:
    import contextlib
    import io
    import tempfile

    @contextlib.contextmanager
    def muted():
        """Swallow the deliberate failure output of the controls below.

        The controls MUST make the gate print its FAILED block and its parse
        rejections — that is what is being asserted. Letting that text reach a
        CI log during a PASSING self-test would be its own defect: a reader
        greps `FAILED` and believes the gate is red.
        """
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            yield buf

    sym_addr = {"live": 0x1000, "dead": 0x2000, "recursive": 0x3000,
                "branched": 0x4000, "pointed": 0x5000, "tabled": 0x6000,
                "root": 0x7000}
    rowed = set(sym_addr) | {"unlinked"}
    calls = {0x1000: {"caller"}, 0x3000: {"recursive"}}
    branches = {0x4000: {"neighbour"}}
    v = classify(rowed, sym_addr, calls, branches, {0x5000}, {0x6000}, 0x7000)

    expect = {"live": "CALLED", "dead": "UNCALLED", "recursive": "SELF-ONLY",
              "branched": "BRANCH-ENTERED", "pointed": "ADDR-TAKEN",
              "tabled": "DATA-TABLE", "root": "ENTRY-ROOT",
              "unlinked": "NOT-IN-IMAGE"}
    for sym, want in expect.items():
        if v[sym] != want:
            die(f"--self-test FAILED: {sym} classified {v[sym]}, want {want}")

    # The negative control that matters: the gate must go RED on an uncalled
    # rowed symbol, and SELF-ONLY must not pass as liveness.
    new, annotated, stale = findings(v, {})
    flagged = {s for s, _ in new}
    if flagged != {"dead", "recursive"}:
        die(f"--self-test FAILED: flagged {sorted(flagged)}, want ['dead', 'recursive']")
    with muted():
        rc = report(rowed, v, {})
    if rc != 1:
        die("--self-test FAILED: report() returned success with findings present")

    # An exemption silences exactly one symbol, and is REPORTED while doing so.
    new, annotated, stale = findings(v, {"dead": ("12351", "deletion tracked")})
    if {s for s, _ in new} != {"recursive"} or [s for s, _ in annotated] != ["dead"]:
        die("--self-test FAILED: exemption did not move `dead` to annotated")

    # ...and a stale exemption (symbol now live) is itself a failure, so the
    # allowlist cannot outlive its findings.
    _new, _annotated, stale = findings(v, {"live": ("1", "was dead once")})
    if stale != ["live"]:
        die(f"--self-test FAILED: stale exemption not reported (got {stale})")

    # Parse strictness: issue= is mandatory, a reason is mandatory.
    with tempfile.TemporaryDirectory() as d:
        for body, why in (
            (f"{SECTION}\nfoo\tbecause\tI said so\n", "missing issue="),
            (f"{SECTION}\nfoo\tissue=12\n", "missing reason"),
            (f"foo\tissue=12\treason\n", "entry before section header"),
            (f"{SECTION}\nfoo\tissue=12\ta\nfoo\tissue=13\tb\n", "duplicate symbol"),
        ):
            p = os.path.join(d, "allow.txt")
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(body)
            try:
                with muted():
                    load_allow(p)
            except SystemExit:
                continue
            die(f"--self-test FAILED: allowlist parser accepted a row with {why}")
        p = os.path.join(d, "good.txt")
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(f"# comment\n{SECTION}\nfoo\tissue=12351\tinline duplicate\n")
        got = load_allow(p)
        if got != {"foo": ("12351", "inline duplicate")}:
            die(f"--self-test FAILED: allowlist parse produced {got}")

    print("check-rowed-liveness --self-test: OK — uncalled and self-only "
          "controls fire, live/branch/addr/table/root controls do not, "
          "exemptions are reported and expire, parser rejects unannotated rows.")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--elf", default=DEFAULT_ELF)
    ap.add_argument("--report", action="store_true",
                    help="print verdicts and exit 0 (measurement, not a gate)")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        self_test()
        return

    allow = load_allow()
    rowed, verdicts = measure(args.elf)
    rc = report(rowed, verdicts, allow)
    raise SystemExit(0 if args.report else rc)


if __name__ == "__main__":
    main()
