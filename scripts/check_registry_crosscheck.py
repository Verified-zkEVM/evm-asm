#!/usr/bin/env python3
"""Cross-registry verdict gate (GH #11294), invoked by scripts/check-registry-crosscheck.sh.

THE GAP THIS CLOSES: `EvmAsm/Progress/Routines.lean` (witnessed `RoutineEntry`
rows) and `EvmAsm/Progress/Correspondence.lean` (`verdict`/`basis` rows)
describe overlapping facts and could not detect disagreement.
`gen-axiom-witnesses.py`'s union cross-check keys on THEOREM NAMES (`some "…"`
refs -> abbrev bindings); an `.unproven` Correspondence row has `spec := none`,
so it contributes no name at all and is invisible to that check by
construction. `verdict_requires_spec` is the converse-free direction. It has
already bitten once: `rlp_encode_uint_be` sat `.unproven` while
`reub_spec_within` existed in the tree (#11281, caught by a human).

THE INVARIANT: a routine symbol with a witnessed row in Routines.lean must not
carry verdict `.unproven` in Correspondence.lean. With it enforced, both
registries have to be wrong in the same way for a stale verdict to survive.

TWO ENFORCEMENT LAYERS, deliberately redundant:
  * `witnessed_not_unproven` in Routines.lean — kernel-checked `decide` over
    the real registries, plus a kernel-checked negative-control `example` that
    runs the same decision procedure on a synthetic violation. Fires in the
    ~1 h `build` job.
  * this script — the same invariant re-derived from source text, so it fails
    in `source-checks` in SECONDS. (The issue asks for source-level
    explicitly: no ELF, no build.)

PARSER SELF-VALIDATION: Lean struct-literal parsing by regex is fragile, so
the parser cross-checks itself against the file's own kernel-checked censuses:
the parsed Correspondence row count must equal the pinned `registry_size`
value and the parsed witnessed-symbol count must equal the pinned
`routineSymbols` length, both read from the same files. A refactor that breaks
the regexes breaks the count and fails loudly instead of silently scanning
nothing (the #11042 silent-skip lesson).

⚠️ `Entry.verdict` DEFAULTS to `.unproven` — a row with no explicit
`verdict :=` field counts as `.unproven`, it is not skipped.

SELF-TEST (prove it can fire, per the issue): `--self-test` injects
`bal_canonical_sort` — a real `.unproven` row today — into the witnessed set
in memory and asserts the checker reports the violation.

Canary history / selection (do not "just pick the next .unproven"):
  * Was `rlp_item_span` until #11577 / PR #11936 lifted that row to
    `.domainRestricted`. The plain run then still passed; only `--self-test`
    failed — the fixture has to move with the achievement.
  * Do NOT use `rlp_encode_u64` here. Routines.lean's kernel negative control
    already points at that row; putting both controls on one symbol means a
    single future PR proving it would break two gates at once.
  * Prefer `bal_canonical_sort`: its Correspondence note records that a triple
    IS statable today and the row stays `.unproven` because nobody has stated
    one; the headline obligation is PERMUTATION (a sort that silently drops
    rows is still sorted; e2e hash tests cannot see it). That is a predicate
    gap nobody is about to close by accident.
"""

import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROUTINES = os.path.join(REPO, "EvmAsm", "Progress", "Routines.lean")
CORRESPOND = os.path.join(REPO, "EvmAsm", "Progress", "Correspondence.lean")
CANARY = "bal_canonical_sort"


def witnessed_symbols(text: str) -> set[str]:
    """Symbols of RoutineEntry rows (all rows are witnessed —
    `routineRegistry_all_witnessed` refuses a row without a proofRef)."""
    return set(re.findall(r'routine\s+"([A-Za-z0-9_]+)"', text))


def parse_entries(text: str) -> list[dict[str, str]]:
    """Parse `registry : List Entry := [ { … }, … ]` into per-row dicts by
    brace matching. Only the fields this gate reads are extracted."""
    m = re.search(r"def registry : List Entry := \[", text)
    if m is None:
        sys.exit("check-registry-crosscheck: cannot find "
                 "`def registry : List Entry := [` in Correspondence.lean")
    i, depth, start, entries = m.end(), 0, None, []
    while i < len(text):
        c = text[i]
        if c == "{":
            if depth == 0:
                start = i
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                entries.append(text[start : i + 1])
        elif c == "]" and depth == 0:
            break
        i += 1
    rows = []
    for block in entries:
        routine = re.search(r'routine := "([^"]+)"', block)
        if routine is None:
            sys.exit(f"check-registry-crosscheck: entry without a "
                     f"`routine :=` field:\n{block[:200]}")
        verdict = re.search(r"verdict := \.(\w+)", block)
        rows.append({
            "routine": routine.group(1),
            # verdict defaults to .unproven when the field is omitted
            "verdict": verdict.group(1) if verdict else "unproven",
        })
    return rows


def pinned(text: str, pattern: str, what: str, path: str) -> int:
    m = re.search(pattern, text)
    if m is None:
        sys.exit(f"check-registry-crosscheck: cannot find the pinned "
                 f"{what} census in {path}")
    return int(m.group(1))


def run(witnessed: set[str], rows: list[dict[str, str]],
        quiet: bool = False) -> list[str]:
    bad = []
    for r in rows:
        if r["verdict"] == "unproven" and r["routine"] in witnessed:
            bad.append(r["routine"])
            if not quiet:
                print(f"  DISAGREE {r['routine']} — witnessed RoutineEntry in "
                      f"Routines.lean, but Correspondence.lean says .unproven")
    return bad


def main() -> None:
    routines_text = open(ROUTINES).read()
    correspond_text = open(CORRESPOND).read()

    witnessed = witnessed_symbols(routines_text)
    rows = parse_entries(correspond_text)

    # Parser self-validation against the files' kernel-checked censuses.
    want_rows = pinned(correspond_text,
                       r"registry\.length = (\d+)", "registry_size",
                       "Correspondence.lean")
    if len(rows) != want_rows:
        sys.exit(f"check-registry-crosscheck: parsed {len(rows)} Correspondence "
                 f"rows but the kernel-checked census says {want_rows}; the "
                 f"parser regex has drifted from the file — fix the parser")
    want_syms = pinned(routines_text,
                       r"routineSymbols\.length = (\d+)", "routineSymbols",
                       "Routines.lean")
    if len(witnessed) != want_syms:
        sys.exit(f"check-registry-crosscheck: parsed {len(witnessed)} distinct "
                 f"witnessed symbols but the kernel-checked census says "
                 f"{want_syms}; the parser regex has drifted — fix the parser")

    if "--self-test" in sys.argv:
        if not any(r["routine"] == CANARY and r["verdict"] == "unproven"
                   for r in rows):
            sys.exit(f"check-registry-crosscheck --self-test: canary {CANARY} "
                     f"is no longer an .unproven Correspondence row; pick a "
                     f"new canary (and update the Lean negative-control "
                     f"`example` in Routines.lean, which uses the same one)")
        bad = run(witnessed | {CANARY}, rows, quiet=True)
        if CANARY in bad:
            print(f"check-registry-crosscheck --self-test: OK — gate fires "
                  f"when {CANARY} is witnessed while .unproven")
            sys.exit(0)
        sys.exit(f"check-registry-crosscheck --self-test: FAIL — injected a "
                 f"witnessed .unproven pair for {CANARY} and the checker did "
                 f"not flag it; the checker is broken")

    bad = run(witnessed, rows)
    if bad:
        print(f"check-registry-crosscheck: FAILED — {len(bad)} routine(s) "
              f"witnessed in Routines.lean but .unproven in Correspondence.lean.")
        print("  A spec theorem exists (the RoutineEntry witnesses it) while the")
        print("  correspondence row still claims no spec exists. Update the row's")
        print("  verdict/basis/spec — or, if the theorem was deleted, remove the")
        print("  RoutineEntry. The two registries must not disagree.")
        sys.exit(1)
    n_unproven = sum(1 for r in rows if r["verdict"] == "unproven")
    print(f"check-registry-crosscheck: OK — {len(witnessed)} witnessed symbols "
          f"x {len(rows)} correspondence rows; {n_unproven} .unproven row(s), "
          f"none witnessed.")


if __name__ == "__main__":
    main()
