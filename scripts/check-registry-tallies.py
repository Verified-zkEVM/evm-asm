#!/usr/bin/env python3
"""check-registry-tallies.py -- re-derive the registries' decide-checked totals
from their row sets and compare against the asserted literals (#12825).

Why this exists
---------------
`Routines.lean` and `Correspondence.lean` both assert their own tallies as
`:= by decide` theorems, so a wrong number CANNOT ship: the kernel rejects it.
That protection is real and this gate does not replace it.

What it adds is *when* the rejection happens.

The failure mode is a MERGE, and specifically a merge with NO CONFLICT. Two
branches each add a row to the same registry from the same base; both write the
same new literal; git takes it without complaint; the union has one more row
than the number says. It fired four times in a single day (2026-08-24) across
PRs #12777, #12813, #12823 and #12824. On one of them -- #12777's
`basis_counts` -- NEITHER SIDE was right: main had reclassified a row
`machineOnly -> ported` (10/6) while the branch added a `machineOnly` row (9/7),
and the union is 10/7. Resolving the two lines that *did* conflict would have
left four others silently wrong.

`decide` catches every one of these. It catches them in a ~50 minute CI build,
or on a developer's full local rebuild. This script catches them in about a
second, by parsing the rows and doing the arithmetic in Python, which is exactly
the point: the fix after the merge is the same either way, but the feedback loop
is three orders of magnitude shorter.

Read `scripts/check-embedded-counts.sh` for the complementary rule -- that gate
forbids RESTATING these tallies in prose, so that the `decide`-checked theorem
stays the single source of truth. This one checks that source against the rows.

Usage:  python3 scripts/check-registry-tallies.py [--self-test]
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ROUTINES = ROOT / "EvmAsm" / "Progress" / "Routines.lean"
CORRESPONDENCE = ROOT / "EvmAsm" / "Progress" / "Correspondence.lean"

# A row's tier may sit on the same line as the symbol or wrap to the next, so
# the separator has to be able to cross a newline. Anchoring on "\n  routine "
# keeps it from matching the word inside a `notes :=` string, which is indented
# further.
ROW_RE = re.compile(r'\n  routine "([^"]+)"\s+\.(\w+)')

CORR_ROW_RE = re.compile(r'\n  \{ family :=')

# -- registry chunk ceiling (#13210) -------------------------------------------
# `routineRegistry` is split into `routineRegistryPart*` chunks because a single
# flat list hits the CODE GENERATOR's recursion limit -- a limit `set_option
# maxRecDepth` does NOT reach, so the error names neither the registry nor a size
# and the obvious remedy does nothing. Measured on the pre-split monolith: 243
# rows build, 244 rows fail even when the added row's prose is 425 characters,
# i.e. shorter than the smallest row already present. There was zero headroom.
#
# #13213 recorded that threshold as a comment at the split site. A number that
# only a comment defends is a number that rots, so this enforces it: the split
# bought headroom, and the point of the gate is that the NEXT contributor is told
# to rechunk in one second by a message that names the cause, instead of
# rediscovering the codegen error the hard way.
CHUNK_RE = re.compile(
    r'^def (routineRegistryPart[A-Za-z0-9_]*)\s*:\s*List RoutineEntry\s*:=\s*\[',
    re.M)
# The measured wall.
CHUNK_CEILING = 244
# Act well before it: a chunk this size still builds, but it is time to split.
CHUNK_LIMIT = 200


def _fail(msgs: list[str], msg: str) -> None:
    msgs.append(msg)


def _assert_literal(text: str, pattern: str, label: str, actual: int,
                    msgs: list[str]) -> None:
    """Compare one asserted literal against the re-derived value."""
    m = re.search(pattern, text)
    if m is None:
        _fail(msgs, f"{label}: could not find the asserted literal "
                    f"(pattern {pattern!r}) -- the theorem was renamed or "
                    f"removed, so this gate is no longer checking it")
        return
    claimed = int(m.group(1))
    if claimed != actual:
        _fail(msgs, f"{label}: asserts {claimed}, rows give {actual}")


def chunk_row_counts(text: str) -> list[tuple[str, int]]:
    """Rows per `routineRegistryPart*` chunk, in file order.

    A chunk runs from its `:= [` to the next chunk header, or -- for the last
    one -- to the `def routineRegistry :` that concatenates them.
    """
    starts = [(m.group(1), m.end()) for m in CHUNK_RE.finditer(text)]
    if not starts:
        return []
    try:
        tail = text.index("\ndef routineRegistry :", starts[-1][1])
    except ValueError:
        tail = len(text)
    bounds = [s for _, s in starts[1:]] + [tail]
    return [(name, len(ROW_RE.findall(text[start:end])))
            for (name, start), end in zip(starts, bounds)]


def check_chunk_ceiling(text: str, rows: list, msgs: list[str]) -> None:
    """Keep every registry chunk clear of the codegen recursion wall (#13210)."""
    counts = chunk_row_counts(text)
    if not counts:
        _fail(msgs, "Routines.lean: found NO routineRegistryPart* chunks -- "
                    "either the registry was un-chunked (it will hit the code "
                    "generator's recursion limit again; see #13210) or CHUNK_RE "
                    "has drifted and this ceiling check is silently vacuous")
        return

    # Non-blindness control, the point of which is that a gate whose parser has
    # gone blind PASSES. If the per-chunk walk does not account for every row
    # the file-wide regex found, the slicing is wrong and the sizes are fiction.
    chunked = sum(n for _, n in counts)
    if chunked != len(rows):
        _fail(msgs, f"Routines.lean: chunk walk saw {chunked} rows but the "
                    f"file has {len(rows)} -- the chunk slicing is wrong, so "
                    f"the ceiling check below cannot be trusted; fix CHUNK_RE "
                    f"or chunk_row_counts")
        return

    for name, n in counts:
        if n >= CHUNK_LIMIT:
            _fail(msgs, f"Routines.lean: {name} holds {n} rows, at or past the "
                        f"{CHUNK_LIMIT}-row rechunk limit (the measured code "
                        f"generator wall is {CHUNK_CEILING}; `set_option "
                        f"maxRecDepth` does NOT reach it). Add a new "
                        f"`routineRegistryPart*` chunk and extend "
                        f"`routineRegistry`; see #13210")


def check_routines(text: str, msgs: list[str]) -> None:
    rows = ROW_RE.findall(text)
    if not rows:
        _fail(msgs, "Routines.lean: parsed ZERO rows -- the row syntax changed "
                    "and this gate is silently vacuous; fix ROW_RE")
        return
    check_chunk_ceiling(text, rows, msgs)
    tiers = Counter(tier for _, tier in rows)
    symbols = {sym for sym, _ in rows}

    _assert_literal(text, r"routineCount_eq\s*:\s*routineCount\s*=\s*(\d+)",
                    "routineCount_eq", len(rows), msgs)
    _assert_literal(text,
                    r"routineProvenCount_eq[^=]*=\s*(\d+)",
                    "routineProvenCount_eq", tiers["proven"], msgs)
    _assert_literal(text,
                    r"routineConditionalCount_eq[^=]*=\s*(\d+)",
                    "routineConditionalCount_eq", tiers["conditional"], msgs)
    _assert_literal(text,
                    r"routinePartlyCount_eq[^=]*=\s*(\d+)",
                    "routinePartlyCount_eq", tiers["partly"], msgs)
    _assert_literal(text,
                    r"routineSymbols_eq\s*:\s*routineSymbols\.length\s*=\s*(\d+)",
                    "routineSymbols_eq", len(symbols), msgs)

    # The tier split must also account for every row: a tier constructor added
    # without a corresponding theorem would otherwise pass every check above.
    counted = tiers["proven"] + tiers["conditional"] + tiers["partly"]
    if counted != len(rows):
        extra = {k: v for k, v in tiers.items()
                 if k not in ("proven", "conditional", "partly")}
        _fail(msgs, f"Routines.lean: {len(rows)} rows but only {counted} are "
                    f"proven/conditional/partly -- untallied tiers {extra}")


def _corr_rows(text: str) -> list[str]:
    """Split the Correspondence registry into per-row blocks."""
    lines = text.split("\n")
    starts = [i for i, l in enumerate(lines) if l.startswith("  { family :=")]
    out = []
    for k, i in enumerate(starts):
        end = starts[k + 1] if k + 1 < len(starts) else i + 16
        out.append("\n".join(lines[i:end]))
    return out


def check_correspondence(text: str, msgs: list[str]) -> None:
    rows = _corr_rows(text)
    if not rows:
        _fail(msgs, "Correspondence.lean: parsed ZERO rows -- the row syntax "
                    "changed and this gate is silently vacuous")
        return

    fam = Counter()
    basis = Counter()
    verdict = Counter()
    port_defect = 0
    for blk in rows:
        m = re.search(r'family := "([^"]+)"', blk)
        if m:
            fam[m.group(1)] += 1
        m = re.search(r"basis := \.(\w+)", blk)
        if m:
            basis[m.group(1)] += 1
        m = re.search(r"verdict := \.(\w+)", blk)
        if m:
            verdict[m.group(1)] += 1
        if re.search(r"portDefect := some", blk):
            port_defect += 1

    _assert_literal(text, r"registry_size\s*:\s*registry\.length\s*=\s*(\d+)",
                    "registry_size", len(rows), msgs)
    _assert_literal(text, r"countPortDefect\s*=\s*(\d+)",
                    "port_defect_count", port_defect, msgs)

    # Per-family theorems are named `<family>_rows`.
    for f, n in sorted(fam.items()):
        _assert_literal(text, rf'countFamily "{re.escape(f)}"\s*=\s*(\d+)',
                        f'countFamily "{f}"', n, msgs)

    for b, n in sorted(basis.items()):
        _assert_literal(text, rf"countBasis \.{b}\s*=\s*(\d+)",
                        f"countBasis .{b}", n, msgs)

    for v, n in sorted(verdict.items()):
        _assert_literal(text, rf"countVerdict \.{v}\s*=\s*(\d+)",
                        f"countVerdict .{v}", n, msgs)

    # Totals must close, or a row with an unlisted constructor slips through
    # every per-constructor check above.
    for name, c in (("basis", basis), ("verdict", verdict)):
        if sum(c.values()) != len(rows):
            _fail(msgs, f"Correspondence.lean: {len(rows)} rows but "
                        f"{sum(c.values())} carry a {name} -- a row is missing "
                        f"one, or the field syntax changed")


def run(routines_text: str, corr_text: str) -> list[str]:
    msgs: list[str] = []
    check_routines(routines_text, msgs)
    check_correspondence(corr_text, msgs)
    return msgs


def self_test() -> int:
    """Planted mismatches must be rejected; the real files must be clean."""
    rt = ROUTINES.read_text()
    ct = CORRESPONDENCE.read_text()
    failures = []

    def expect(name: str, msgs: list[str], want_fail: bool, needle: str = ""):
        got_fail = bool(msgs)
        if got_fail != want_fail:
            failures.append(f"{name}: expected "
                            f"{'FAIL' if want_fail else 'PASS'}, got "
                            f"{'FAIL' if got_fail else 'PASS'} {msgs}")
        elif want_fail and needle and not any(needle in m for m in msgs):
            failures.append(f"{name}: failed, but not about {needle!r}: {msgs}")

    # Clean controls -- the shipped files.
    expect("control: real files", run(rt, ct), want_fail=False)

    # 1. The exact merge trap: row set grows, literal does not.
    m = ROW_RE.search(rt)
    planted = rt[:m.start()] + '\n  routine "planted_row" .proven' + rt[m.start():]
    expect("planted: extra routine row", run(planted, ct), want_fail=True,
           needle="routineCount_eq")

    # 2. A tier reclassification that keeps the total identical -- the #12777
    #    shape, where the count line is right and the split is wrong.
    reclass = re.sub(r'\n  routine "([^"]+)"\s+\.conditional',
                     r'\n  routine "\1" .proven', rt, count=1)
    expect("planted: tier reclassification", run(reclass, ct), want_fail=True,
           needle="routineProvenCount_eq")

    # 3. Same for the Correspondence registry.
    cm = re.search(r"\n  \{ family := \"(\w+)\"", ct)
    fam0 = cm.group(1)
    corr_planted = (ct[:cm.start()] +
                    f'\n  {{ family := "{fam0}", routine := "planted",\n'
                    "    spec := none,\n"
                    "    verdict := .agrees, basis := .inspection,\n"
                    '    reference := "planted", note := "planted" }},' +
                    ct[cm.start():])
    expect("planted: extra correspondence row", run(rt, corr_planted),
           want_fail=True, needle="registry_size")

    # 4. A renamed theorem must fail loudly rather than stop checking.
    renamed = rt.replace("routineSymbols_eq", "routineSymbolsCount_eq")
    expect("planted: renamed theorem", run(renamed, ct), want_fail=True,
           needle="could not find")

    # 5. Negative control on the parser itself: if ROW_RE ever matches nothing,
    #    the gate must say so instead of passing vacuously.
    expect("planted: unparseable rows", run("-- no rows here --", ct),
           want_fail=True, needle="ZERO rows")

    # -- chunk ceiling (#13210) ------------------------------------------------
    def synth(chunks: list[tuple[str, int]]) -> str:
        """A minimal registry with the given chunk layout."""
        out = []
        for name, n in chunks:
            out.append(f"def {name} : List RoutineEntry := [")
            out += [f'  routine "s{i}" .proven (some "t"),' for i in range(n)]
            out.append("]\n")
        out.append("def routineRegistry : List RoutineEntry := "
                   + " ++ ".join(n for n, _ in chunks))
        return "\n" + "\n".join(out) + "\n"

    def chunk_msgs(text: str) -> list[str]:
        msgs: list[str] = []
        check_chunk_ceiling(text, ROW_RE.findall(text), msgs)
        return msgs

    # 6. An oversized chunk must be refused -- the whole point of the gate.
    expect("planted: chunk at the rechunk limit",
           chunk_msgs(synth([("routineRegistryPartA", CHUNK_LIMIT),
                             ("routineRegistryPartB", 10)])),
           want_fail=True, needle="rechunk limit")

    # 6a. The limit must stay BELOW the measured wall. Raising it past
    #     CHUNK_CEILING would leave the gate green right up to the build
    #     failure it exists to pre-empt -- a limit that only fits today.
    if CHUNK_LIMIT >= CHUNK_CEILING:
        failures.append(f"CHUNK_LIMIT ({CHUNK_LIMIT}) is not below the measured "
                        f"codegen wall CHUNK_CEILING ({CHUNK_CEILING}); the "
                        f"gate would pass up to the failure it exists to prevent")

    # 6b. WIRING control. Everything above calls check_chunk_ceiling directly,
    #     so the ceiling check could be dropped from check_routines and every
    #     one of them would still pass. This routes an oversized chunk through
    #     the real entry point, which is the only thing that proves the gate is
    #     actually reachable in a live run.
    expect("wiring: oversized chunk seen through run()",
           run(synth([("routineRegistryPartA", CHUNK_LIMIT),
                      ("routineRegistryPartB", 10)]), ct),
           want_fail=True, needle="rechunk limit")

    # 7. ...and the check must not be merely strict. One row below the limit is
    #    the shipping condition, so it must PASS, or the gate would block every
    #    registry that is doing exactly what it asks.
    expect("control: chunk just under the limit",
           chunk_msgs(synth([("routineRegistryPartA", CHUNK_LIMIT - 1),
                             ("routineRegistryPartB", CHUNK_LIMIT - 1)])),
           want_fail=False)

    # 8. Un-chunking the registry reintroduces the codegen wall #13213 removed,
    #    and must be refused rather than silently skipped.
    expect("planted: registry un-chunked",
           chunk_msgs(rt.replace("routineRegistryPartA", "routineRegistryFlat")
                        .replace("routineRegistryPartB", "routineRegistryFlat2")),
           want_fail=True, needle="NO routineRegistryPart* chunks")

    # 9. Blindness control, the one that matters: a chunk walk that LOSES rows
    #    reports small chunks and PASSES, so the ceiling check would go quiet
    #    exactly when the registry is growing. Rows living outside every
    #    `Part*` chunk -- a new chunk appended below the concatenation, say --
    #    must be caught by row conservation rather than silently dropped.
    #
    #    (Losing a chunk HEADER is the opposite, safe error: its rows are
    #    absorbed into the preceding slice, so sizes over-count and the limit
    #    fires early. Only under-counting can hide growth, so that is what this
    #    control plants.)
    orphaned = (synth([("routineRegistryPartA", 5), ("routineRegistryPartB", 5)])
                + "\ndef strayRegistryRows : List RoutineEntry := [\n"
                + "".join(f'  routine "o{i}" .proven (some "t"),\n' for i in range(4))
                + "]\n")
    expect("planted: rows outside every chunk", chunk_msgs(orphaned),
           want_fail=True, needle="chunk walk saw")

    # 10. The shipped registry must actually be seen by the walk -- a real
    #     count, not an exit status (a blinded gate passes).
    live = chunk_row_counts(rt)
    if sum(n for _, n in live) != len(ROW_RE.findall(rt)) or len(live) < 2:
        failures.append(f"control: live chunk walk is not seeing the registry: "
                        f"{live}")

    if failures:
        print("SELF-TEST: FAIL")
        for f in failures:
            print("  " + f)
        return 1
    print("SELF-TEST: PASS (13 checks: 1 clean control, 4 planted mismatches, "
          "1 vacuity control, 6 chunk-ceiling checks -- oversize, under-limit "
          "control, limit-below-wall, run() wiring, un-chunked, "
          "walk-blindness -- and 1 live-registry chunk control) "
          f"-- live chunks: {', '.join(f'{n}={c}' for n, c in live)}")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        rc = self_test()
        if rc:
            return rc

    msgs = run(ROUTINES.read_text(), CORRESPONDENCE.read_text())
    if msgs:
        print("check-registry-tallies: FAIL -- an asserted total does not "
              "match its row set.")
        for m in msgs:
            print("  " + m)
        print()
        print("This is almost always a MERGE, not an edit: two branches added "
              "rows from the same base and")
        print("wrote the same literal, so git merged the count line without a "
              "conflict. Re-derive every")
        print("total from the MERGED row set -- do not take either side, and "
              "do not trust a line that did")
        print("not conflict. On #12777 neither side's `basis_counts` was "
              "right.")
        return 1

    print("check-registry-tallies: OK (Routines + Correspondence totals match "
          "their row sets)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
