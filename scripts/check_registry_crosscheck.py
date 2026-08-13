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

CENSUS PIN CHECK (#12266): Lean struct-literal parsing by regex is fragile, so
the parser cross-checks its counts against the textual `…length = N` pins in the
same files (`registry_size`, `routineSymbols_eq`). Those pins are `decide`-proven
when Lean compiles the file, but this script runs in source-checks where nothing
has compiled — it is reading a NUMBER FROM TEXT. A mismatch is therefore
ambiguous: the pin may be stale (rows added/removed without regenerating it) or
the parser may have drifted. We do not call the pin "kernel-checked" here, and
we do not assert a cause we have not established. Discrimination uses an
independent recount of the same source: when recount agrees with the primary
parse but not the pin, the pin is stale; when recount disagrees with the
primary parse, the parser has drifted.

⚠️ `Entry.verdict` DEFAULTS to `.unproven` — a row with no explicit
`verdict :=` field counts as `.unproven`, it is not skipped.

SELF-TEST (`--self-test`):
  1. Verdict gate: inject `bal_canonical_sort` into the witnessed set and
     assert the checker reports the disagreement.
  2. Stale pin (#12266): lower a textual pin; message must name the pin/census.
  3. Parser drift (#12266): under-count via the primary parse while the
     independent recount stays full; message must name the parser.

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

from __future__ import annotations

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


def independent_routine_symbol_count(text: str) -> int:
    """Recount distinct symbols inside `routineRegistry` only (line-anchored).

    Deliberately not the same regex surface as `witnessed_symbols`: a drift that
    makes the file-wide primary miss or double-count still has this list-scoped
    recount to disagree with.
    """
    m = re.search(r"def routineRegistry : List RoutineEntry := \[", text)
    if m is None:
        return -1
    i, depth = m.end(), 1  # already inside the outer `[`
    while i < len(text) and depth > 0:
        c = text[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
        i += 1
    body = text[m.end() : i - 1]
    return len(set(re.findall(r'(?m)^\s*routine\s+"([A-Za-z0-9_]+)"', body)))


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


def independent_correspondence_row_count(text: str) -> int:
    """Recount Correspondence rows by `routine :=` fields inside the registry.

    Independent of brace-matching in `parse_entries`: if the two disagree, the
    primary parser has drifted.
    """
    m = re.search(r"def registry : List Entry := \[", text)
    if m is None:
        return -1
    i, depth = m.end(), 1
    while i < len(text) and depth > 0:
        c = text[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
        i += 1
    body = text[m.end() : i - 1]
    return len(re.findall(r'routine := "', body))


def pinned(text: str, pattern: str, what: str, path: str) -> int:
    m = re.search(pattern, text)
    if m is None:
        sys.exit(f"check-registry-crosscheck: cannot find the pinned "
                 f"{what} census in {path}")
    return int(m.group(1))


def census_mismatch_message(
    parsed: int, pin: int, independent: int, *, what: str
) -> str:
    """Observation + discriminated hint (#12266). Never asserts an unproven cause."""
    obs = (
        f"check-registry-crosscheck: parsed {parsed} {what}; "
        f"textual census pin says {pin}."
    )
    if independent == parsed and parsed != pin:
        return (
            obs
            + " An independent recount agrees with the parser, so the pin is "
            "stale — regenerate the `…length = N` theorem (rows likely changed "
            "since it was last updated) before suspecting the parser."
        )
    if independent != parsed:
        return (
            obs
            + f" An independent recount got {independent}, which disagrees with "
            "the primary parser, so the parser has drifted — fix the parser."
        )
    # parsed == pin but we were called anyway; keep a non-vacuous observation.
    return obs + " One of these is stale; check row edits before the parser."


def check_census(
    parsed: int, pin: int, independent: int, *, what: str
) -> str | None:
    """Return an error message on mismatch, else None."""
    if parsed == pin:
        return None
    return census_mismatch_message(parsed, pin, independent, what=what)


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


def self_test(
    routines_text: str,
    correspond_text: str,
    witnessed: set[str],
    rows: list[dict[str, str]],
) -> None:
    # --- Leg 0: verdict disagreement canary (pre-existing) ---
    if not any(r["routine"] == CANARY and r["verdict"] == "unproven"
               for r in rows):
        sys.exit(f"check-registry-crosscheck --self-test: canary {CANARY} "
                 f"is no longer an .unproven Correspondence row; pick a "
                 f"new canary (and update the Lean negative-control "
                 f"`example` in Routines.lean, which uses the same one)")
    bad = run(witnessed | {CANARY}, rows, quiet=True)
    if CANARY not in bad:
        sys.exit(f"check-registry-crosscheck --self-test: FAIL — injected a "
                 f"witnessed .unproven pair for {CANARY} and the checker did "
                 f"not flag it; the checker is broken")

    # --- Leg 1: stale pin — lower the Correspondence length pin ---
    want_rows = pinned(correspond_text,
                       r"registry\.length = (\d+)", "registry_size",
                       "Correspondence.lean")
    if want_rows < 1:
        sys.exit("check-registry-crosscheck --self-test: FAIL — pin is 0")
    stale_text = re.sub(
        r"registry\.length = \d+",
        f"registry.length = {want_rows - 1}",
        correspond_text,
        count=1,
    )
    stale_pin = pinned(stale_text, r"registry\.length = (\d+)", "registry_size",
                       "Correspondence.lean")
    indep = independent_correspondence_row_count(correspond_text)
    msg = check_census(len(rows), stale_pin, indep, what="Correspondence rows")
    if msg is None or "pin is stale" not in msg:
        sys.exit(
            "check-registry-crosscheck --self-test: FAIL — stale-pin inject "
            f"did not name the pin (msg={msg!r})"
        )
    if "parser has drifted" in msg or "fix the parser" in msg:
        sys.exit(
            "check-registry-crosscheck --self-test: FAIL — stale-pin inject "
            f"blamed the parser (msg={msg!r})"
        )

    # --- Leg 2: parser drift — primary under-count, independent stays full ---
    if len(rows) < 1:
        sys.exit("check-registry-crosscheck --self-test: FAIL — no rows to drop")
    drifted_parsed = len(rows) - 1
    real_pin = pinned(correspond_text, r"registry\.length = (\d+)",
                      "registry_size", "Correspondence.lean")
    msg2 = check_census(
        drifted_parsed, real_pin, indep, what="Correspondence rows"
    )
    if msg2 is None or "parser has drifted" not in msg2:
        sys.exit(
            "check-registry-crosscheck --self-test: FAIL — parser-drift inject "
            f"did not name the parser (msg={msg2!r})"
        )
    if "pin is stale" in msg2:
        sys.exit(
            "check-registry-crosscheck --self-test: FAIL — parser-drift inject "
            f"blamed the pin (msg={msg2!r})"
        )

    # Same two legs on the Routines symbol census.
    want_syms = pinned(routines_text,
                       r"routineSymbols\.length = (\d+)", "routineSymbols",
                       "Routines.lean")
    stale_r = re.sub(
        r"routineSymbols\.length = \d+",
        f"routineSymbols.length = {want_syms - 1}",
        routines_text,
        count=1,
    )
    stale_sym_pin = pinned(stale_r, r"routineSymbols\.length = (\d+)",
                           "routineSymbols", "Routines.lean")
    indep_syms = independent_routine_symbol_count(routines_text)
    msg3 = check_census(
        len(witnessed), stale_sym_pin, indep_syms, what="distinct witnessed symbols"
    )
    if msg3 is None or "pin is stale" not in msg3:
        sys.exit(
            "check-registry-crosscheck --self-test: FAIL — routines stale-pin "
            f"inject did not name the pin (msg={msg3!r})"
        )
    msg4 = check_census(
        len(witnessed) - 1, want_syms, indep_syms,
        what="distinct witnessed symbols",
    )
    if msg4 is None or "parser has drifted" not in msg4:
        sys.exit(
            "check-registry-crosscheck --self-test: FAIL — routines parser-drift "
            f"inject did not name the parser (msg={msg4!r})"
        )

    print(
        "check-registry-crosscheck --self-test: OK — verdict canary fires; "
        "stale-pin message names the pin; parser-drift message names the parser "
        "(Correspondence + Routines)"
    )
    sys.exit(0)


def main() -> None:
    routines_text = open(ROUTINES).read()
    correspond_text = open(CORRESPOND).read()

    witnessed = witnessed_symbols(routines_text)
    rows = parse_entries(correspond_text)

    # Census pin check — observation + discriminate; do not delete this gate.
    want_rows = pinned(correspond_text,
                       r"registry\.length = (\d+)", "registry_size",
                       "Correspondence.lean")
    indep_rows = independent_correspondence_row_count(correspond_text)
    if indep_rows < 0:
        sys.exit("check-registry-crosscheck: cannot slice Correspondence registry "
                 "for independent recount")
    err = check_census(
        len(rows), want_rows, indep_rows, what="Correspondence rows"
    )
    if err is not None:
        sys.exit(err)

    want_syms = pinned(routines_text,
                       r"routineSymbols\.length = (\d+)", "routineSymbols",
                       "Routines.lean")
    indep_syms = independent_routine_symbol_count(routines_text)
    if indep_syms < 0:
        sys.exit("check-registry-crosscheck: cannot slice routineRegistry for "
                 "independent recount")
    err = check_census(
        len(witnessed), want_syms, indep_syms,
        what="distinct witnessed symbols",
    )
    if err is not None:
        sys.exit(err)

    if "--self-test" in sys.argv:
        self_test(routines_text, correspond_text, witnessed, rows)

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
