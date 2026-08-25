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


def check_routines(text: str, msgs: list[str]) -> None:
    rows = ROW_RE.findall(text)
    if not rows:
        _fail(msgs, "Routines.lean: parsed ZERO rows -- the row syntax changed "
                    "and this gate is silently vacuous; fix ROW_RE")
        return
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

    if failures:
        print("SELF-TEST: FAIL")
        for f in failures:
            print("  " + f)
        return 1
    print("SELF-TEST: PASS (6 checks: 1 clean control, "
          "4 planted mismatches, 1 vacuity control)")
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
