#!/usr/bin/env python3
"""check-nonvacuity-witnessed.py -- a theorem a row cites as its non-vacuity
evidence must be WITNESSED, not merely named in prose (#12857).

Why this exists
---------------
A `.conditional` row's gate is only meaningful if the gate is satisfiable, and a
`.proven` row's contract is only meaningful if its hypotheses are. Rows record
that by naming a reachability instance and a negative control in their
`notes :=` / `gate :=` prose:

    (gate := "... coverRef `foo_precondition_reachable` ... negative control
              `foo_refutable` where the same conjuncts are provably FALSE")

Those strings constrain nothing. `check-axioms.sh` audits exactly the
declarations reachable from the witness abbrevs in `Routines.lean`, so a theorem
that appears only inside a string is outside the gate: if it later acquired a
`sorryAx` or a TCB-expanding tactic, the ledger would stay green while the row's
prose kept citing it as the reason the gate is satisfiable.

The failure is silent in the way that matters, and it is not hypothetical -- it
was found three separate times in one week (2026-08-24/25):

  * `aer_gate_reachable` + two negative controls on `assemble_execution_requests`
    (#12813), caught in review;
  * the `header_extended_decode` rows (#12820);
  * three per-arm covers on `header_validate_parent_hash` whose module
    `Routines.lean` did not even import (#12833).

Each was found by a human reading one row. This finds all of them in a second.

What it does NOT do
-------------------
It does not check that the cited theorem *says* anything useful -- that is a
reading, not a gate. It checks only that the row's non-vacuity evidence is
inside the axiom gate rather than outside it.

KNOWN GAP, stated rather than hidden: detection is by name shape, so a control
whose name carries none of the recognised vocabulary is missed. The real example
is `mset_memcpy_align_bites` -- a genuine negative control on the `mset_memcpy`
row, found by reading and witnessed by hand, which this check would not have
flagged. Widening the pattern far enough to catch it means matching ordinary
prose, and a gate that cries wolf is one people learn to route around. The
durable fix is a naming convention: name a cited instance or control with one
of the words above, and the check sees it. Until then, treat a green result as
"no citation with an evidence-shaped name is unaudited", not as "every cited
theorem is audited".

Usage:  python3 scripts/check-nonvacuity-witnessed.py [--self-test]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ROUTINES = ROOT / "EvmAsm" / "Progress" / "Routines.lean"

# A row's prose makes a non-vacuity CLAIM when it uses one of these words. Rows
# that make no such claim are not the subject of this gate.
CLAIM_RE = re.compile(
    r"non-?vacu|coverRef|reachable|negative control|refutab|satisfiab|inhabit",
    re.IGNORECASE,
)

# Within such a row, a backticked identifier shaped like one of these is being
# offered AS the evidence. Helper lemmas mentioned in passing are not.
#
# The second group is the refutation vocabulary. A negative control is usually
# named after WHAT IT REFUTES rather than with the word "control" -- the two
# on `assemble_execution_requests` are `aer_gate_not_8aligned` and
# `aer_gate_buffer_too_short`, and `requests_hash_verify` names its controls
# `rhv_gate_unaligned` / `rhv_gate_short_expected`. Matching only the first
# group missed every one of them.
EVIDENCE_RE = re.compile(
    r"reachable|instance|control|refutab|cover"
    r"|nonvacuous|non_vacuous|_false|_not_|_wrong|_too_|unaligned|_fail|_bad",
    re.IGNORECASE,
)

# Every name declared anywhere under EvmAsm/, used only to tell the two failure
# modes apart in the report: a citation that names a real declaration needs a
# witness, while one that names nothing is stale -- a rename, a retirement, or
# a typo -- and no witness can fix it.
DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
    re.MULTILINE,
)


def declared_names() -> set[str]:
    """Short names of every declaration under EvmAsm/."""
    out: set[str] = set()
    for f in (ROOT / "EvmAsm").rglob("*.lean"):
        try:
            src = f.read_text(errors="ignore")
        except OSError:
            continue
        for n in DECL_RE.findall(src):
            out.add(n.rsplit(".", 1)[-1])
    return out

BACKTICKED_RE = re.compile(r"`([A-Za-z][A-Za-z0-9_']*)`")
ROW_SPLIT_RE = re.compile(r'\n  routine "')
WITNESS_RE = re.compile(r"abbrev\s+_\w+\s*:=\s*@([A-Za-z0-9_.]+)")
SPEC_RE = re.compile(r'\(some\s*\n?\s*"([A-Za-z0-9_\']+)"\)')


def analyse(text: str, declared: set[str] | None = None
            ) -> tuple[list[tuple[str, str]], int, int]:
    """Return (violations, rows_total, rows_claiming).

    `declared` is only used to label each violation; it never changes which
    citations are reported, so the check behaves identically with or without it.
    """
    start = text.find("def routineRegistry")
    end = text.find("theorem routineCount_eq")
    if start < 0 or end < 0 or end <= start:
        return ([("<parse>", "could not locate the registry body")], 0, 0)
    body = text[start:end]

    rows = ROW_SPLIT_RE.split(body)[1:]
    symbols = {r.split('"')[0] for r in rows}

    # Witnessed = named by a witness abbrev anywhere in the file (these are what
    # gen-axiom-witnesses.py turns into `#print axioms` lines).
    witnessed = {m.rsplit(".", 1)[-1] for m in WITNESS_RE.findall(text)}
    # A row's own `spec` field is separately audited, so it counts as covered.
    specs = set(SPEC_RE.findall(text))

    violations: list[tuple[str, str]] = []
    claiming = 0
    for r in rows:
        sym = r.split('"')[0]
        if not CLAIM_RE.search(r):
            continue
        claiming += 1
        for name in BACKTICKED_RE.findall(r):
            if not EVIDENCE_RE.search(name):
                continue
            # A registry SYMBOL is a routine name, not a theorem -- several
            # contain "witness" (`witness_lookup_by_hash`), so exclude them or
            # the gate is mostly false positives.
            if name in witnessed or name in specs or name in symbols:
                continue
            if (sym, name) not in [(s, n) for s, n, _ in violations]:
                kind = "unwitnessed" if declared is None or name in declared \
                    else "names nothing"
                violations.append((sym, name, kind))
    return (violations, len(rows), claiming)


def self_test() -> int:
    text = ROUTINES.read_text()
    failures: list[str] = []

    def expect(label: str, t: str, want_violation: str | None):
        v, _, _ = analyse(t)
        names = {n for _, n, _ in v}
        if want_violation is None:
            if v:
                failures.append(f"{label}: expected clean, got {sorted(names)}")
        elif want_violation not in names:
            failures.append(f"{label}: expected {want_violation!r}, got {sorted(names)}")

    base, _, _ = analyse(text)
    base_names = {n for _, n, _ in base}

    # 1. Planted: a row claims non-vacuity and cites an unwitnessed instance.
    m = ROW_SPLIT_RE.search(text)
    planted = (text[: m.start()] +
               '\n  routine "planted_sym" .conditional (some "planted_spec")\n'
               '      (gate := "planted; coverRef `planted_unwitnessed_instance`")' +
               text[m.start():])
    expect("planted: unwitnessed instance", planted, "planted_unwitnessed_instance")

    # 2. Negative control -- the SAME citation, now witnessed, must not fire.
    witnessed_ok = planted.replace(
        "private noncomputable abbrev _",
        "private noncomputable abbrev _planted_w :=\n"
        "  @EvmAsm.Fake.planted_unwitnessed_instance\n"
        "private noncomputable abbrev _", 1)
    v, _, _ = analyse(witnessed_ok)
    if "planted_unwitnessed_instance" in {n for _, n, _ in v}:
        failures.append("control: a witnessed citation still fired")

    # 3. Negative control -- an evidence-shaped name in a row that makes NO
    #    non-vacuity claim must not fire.
    quiet = (text[: m.start()] +
             '\n  routine "planted_quiet" .proven (some "planted_spec2")\n'
             '      (notes := "step bound only; uses `helper_instance`")' +
             text[m.start():])
    v, _, _ = analyse(quiet)
    if "helper_instance" in {n for _, n, _ in v}:
        failures.append("control: a non-claiming row fired")

    # 4. Negative control -- a registry SYMBOL containing an evidence word is
    #    not a theorem and must not fire (`witness_lookup_by_hash` etc.).
    if any(n in {"witness_lookup_by_hash", "extract_witness_state_section"}
           for n in base_names):
        failures.append("control: a registry symbol was reported as a theorem")

    # 5. The two failure modes are told apart: a citation naming a real
    #    declaration is "unwitnessed"; one naming nothing is "names nothing".
    #    Only the first is fixable by adding a witness, so the report must not
    #    conflate them.
    v, _, _ = analyse(planted, {"planted_unwitnessed_instance"})
    if not any(n == "planted_unwitnessed_instance" and k == "unwitnessed"
               for _, n, k in v):
        failures.append("classify: a declared citation was not graded "
                        "'unwitnessed'")
    v, _, _ = analyse(planted, set())
    if not any(n == "planted_unwitnessed_instance" and k == "names nothing"
               for _, n, k in v):
        failures.append("classify: an undeclared citation was not graded "
                        "'names nothing'")

    # 6. A negative control named after WHAT IT REFUTES, with none of the words
    #    "control"/"instance"/"reachable" in it, must still be caught. Matching
    #    only that first vocabulary missed every real control in the registry.
    refuting = (text[: m.start()] +
                '\n  routine "planted_refute" .conditional (some "planted_spec3")\n'
                '      (gate := "satisfiable; negative control '
                '`plgate_not_8aligned` where the gate is provably FALSE")' +
                text[m.start():])
    expect("planted: control named after its refutation", refuting,
           "plgate_not_8aligned")

    # 7. Vacuity control -- if row parsing ever breaks, fail loudly.
    v, total, _ = analyse("-- no registry here --")
    if not v or total != 0:
        failures.append("control: an unparseable file did not fail loudly")

    if failures:
        print("SELF-TEST: FAIL")
        for f in failures:
            print("  " + f)
        return 1
    print("SELF-TEST: PASS (2 planted cases, 6 controls: "
          "witnessed-does-not-fire, non-claiming-row, registry-symbol, "
          "declared-vs-names-nothing x2, unparseable-file)")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        rc = self_test()
        if rc:
            return rc

    violations, total, claiming = analyse(ROUTINES.read_text(), declared_names())
    if violations:
        unwitnessed = [(s, n) for s, n, k in violations if k == "unwitnessed"]
        stale = [(s, n) for s, n, k in violations if k == "names nothing"]
        print("check-nonvacuity-witnessed: FAIL")
        if unwitnessed:
            print()
            print("  Cited as non-vacuity evidence, but the axiom gate does not "
                  "audit it:")
            for sym, name in unwitnessed:
                print(f"    {sym}: `{name}`")
            print()
            print("  Each names a real declaration that is reachable from no "
                  "witness abbrev, so")
            print("  `check-axioms.sh` never sees it: it could acquire a "
                  "`sorryAx` while the ledger")
            print("  stayed green and the row kept citing it. Add to "
                  "Routines.lean")
            print()
            print("      private noncomputable abbrev _<row>_<what>_witness :=")
            print("        @<Full.Namespace>.<theorem>")
            print()
            print("  and regenerate: "
                  "`python3 scripts/gen-axiom-witnesses.py --write`.")
        if stale:
            print()
            print("  Cited as non-vacuity evidence, but NAMES NOTHING -- no such "
                  "declaration exists")
            print("  under EvmAsm/ (a rename, a retirement, or a typo). No "
                  "witness can fix these;")
            print("  the row is citing evidence that is not there:")
            for sym, name in stale:
                print(f"    {sym}: `{name}`")
            print()
            print("  Point the row at the theorem that replaced it, or drop the "
                  "claim.")
        print()
        print("  If a name is not a theorem at all (a routine symbol, a file, "
              "prose), unbacktick")
        print("  it -- backticks in a non-vacuity sentence read as a citation.")
        return 1

    print(f"check-nonvacuity-witnessed: OK ({claiming} of {total} rows make a "
          f"non-vacuity claim; every cited instance/control is witnessed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
