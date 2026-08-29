#!/usr/bin/env python3
"""Every gate wired into the blocking build workflow must be *capable* of failing.

#12931 fixed a gate that had been reporting four real drifts on green CI for
weeks, because the workflow invoked it without `--strict` and the script's
`return 1` sat behind that flag.  Nothing was broken, nothing was red, and the
step's presence in the workflow read as coverage.  That is the failure mode this
script exists to make impossible to reintroduce:

    A gate that is wired but structurally unable to fail is indistinguishable
    from not having the gate -- and it is worse, because the step reads as
    coverage to anyone scanning the workflow.

It was the fifth instrument found wrong in the quiet direction in a single day
(see #12906, #12907, #12908, #12922, #12931), and the only one of the five whose
defect was visible without running anything.

Two rules.

RULE A -- strict-capable, invoked non-strict.
  If a script parses a `--strict` flag and CI invokes it without one, the
  script's failure path is unreachable in CI.  That is allowed ONLY when the
  gate is declared advisory below, with a reason.  The point is not to forbid
  advisory gates -- some must be advisory -- but to make advisory a DECLARED
  state rather than something that happens by omission.  #12931's gate was
  advisory by omission; the two entries below are advisory on purpose, and the
  difference was invisible until someone read all three scripts.

RULE B -- no failure path at all.
  A wired script with no `exit 1` / `sys.exit(1)` / `return 1` and no `set -e`
  cannot fail however it is invoked.  `set -e` counts: a script under it fails
  implicitly when any command does.

Neither rule can tell whether a gate checks the RIGHT thing -- that is what a
`--self-test` is for.  This checks only that the failure path exists and is
reachable.  A gate can pass this and still be useless; it cannot pass this and
be structurally silent.

The blocking candidate set starts with direct `scripts/<name>` invocations in
`.github/workflows/build.yml` and follows executable `run_step scripts/<name>`
dispatches from those scripts (and their transitive dispatches).  This keeps
the workflow candidate set closed without depending on the `check-*` filename
convention or an opt-in list, while still seeing gates hidden behind the
parallel bundle.  The normal report distinguishes DIRECTLY INVOKED scripts
from BUNDLE-REACHABLE scripts and from the weaker source-level
STATIC-ANALYSED result, and lists any unanalysed names.  `--self-test` adds a
separate PLANT-PROVEN count for synthetic end-to-end cases; that count is not a
claim that a generic harness exercised every production gate's defect branch.

Usage:
  scripts/check-gates-can-fail.py              # audit build.yml script invocations
  scripts/check-gates-can-fail.py --self-test  # planted cases + controls
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
WORKFLOWS = REPO / ".github" / "workflows"
SCRIPTS = REPO / "scripts"
BUILD_WORKFLOW = WORKFLOWS / "build.yml"

# Gates deliberately run in advisory mode, each with the reason its own header
# gives.  Adding an entry here is a decision someone has to defend in review;
# leaving a gate out of it and non-strict is the bug this script catches.
ADVISORY_BY_DESIGN = {
    "check-obligation-blockers.sh":
        "needs network + `gh` auth, which CI environments may not have; and per "
        "AGENTS.md a new gate is seeded green rather than red-lighting day one",
    "check-statement-tamper.sh":
        "a heuristic over changed files, not a proof -- it reports rather than "
        "blocks by default (docs/agent-progress-steering-review.md R-C2)",
    "check-naming.sh":
        "a style nudge over new `h<Upper>` binders, with no failure path at all "
        "by design -- it prints `advisory scan complete (exit 0)` and every "
        "finding is a rename suggestion, not a defect",
}

# Matches the three idioms used in this repo to PARSE a strictness flag.  The
# context is required, not just the token: a script that merely mentions the
# flag in prose, or one that contains it as data, is not parsing it.  The first
# draft matched the bare token and so accused THIS script of being a silent
# gate, because the token appears in its own pattern and fixtures.
#
#   bash:   [[ "${1:-}" == "--strict" ]] && STRICT=1
#   bash:   --strict) STRICT=1 ;;
#   python: if "--strict" in sys.argv[1:]:
STRICT_PARSE = re.compile(
    r'--strict\)\s*[A-Z_]*STRICT'
    r'|==\s*"--strict"'
    r'|"--strict"\s+in\s+sys\.argv')
# An explicit nonzero exit, an exit through a variable or a computed status, or
# `set -e` (which makes failure implicit on any failing command).
#
# Deliberately generous: a false "can fail" merely leaves a gate unexamined,
# while a false "cannot fail" accuses a working gate and turns main red.  The
# first draft of this anchored `exit` to start-of-line and so missed BOTH
# `exit "$rc"` (check-guest-elf-override.sh) and `[[ $STRICT -eq 1 ]] && exit 1`
# (check-obligation-blockers.sh) -- two false accusations out of four hits.
CAN_FAIL = re.compile(
    r'\bexit\s+[1-9]'                 # exit 1
    r'|\bexit\s+"?\$'                 # exit "$rc" / exit $?
    r'|sys\.exit\(\s*[1-9]'           # sys.exit(1)
    r'|sys\.exit\(\s*[A-Za-z_]'       # sys.exit(main())
    r'|raise\s+SystemExit\(\s*[A-Za-z_1-9]'
    r'|^\s*return\s+[1-9]'
    r'|set\s+-[a-z]*e', re.M)


def strip_comments(src: str) -> str:
    """Drop whole-line comments.

    Usage blocks routinely contain lines like

        #   scripts/check-foo.sh --strict # exit 1 on a violation

    and counting that `exit 1` as a failure path would let a genuinely silent
    gate through -- the exact direction of error this script exists to catch.
    Inline trailing comments are left alone: in this repo the `exit N` mentions
    all sit on whole-line comments, and stripping after a bare `#` would
    mangle `${1:-}` and `$#`.
    """
    return "\n".join(l for l in src.splitlines() if not l.lstrip().startswith("#"))
# A `scripts/foo.sh [args...]` invocation inside a workflow, up to end of line
# or a shell separator.  Comment lines are dropped first.
INVOCATION = re.compile(r'(?<![\w/-])scripts/([A-Za-z0-9._-]+\.(?:sh|py))([^\n|&;)]*)')
# `check-build-parallel.sh` dispatches child gates through this function rather
# than from the workflow itself.  Restricting the nested scan to executable
# `run_step` calls avoids treating source helpers, documentation, or comments
# as gates.  The closure below is deliberately transitive: a future bundle may
# delegate to another bundle without reopening this blind spot.
DISPATCH_INVOCATION = re.compile(
    r'^\s*(?:start\s+\S+\s+)?run_step\s+'
    r'scripts/([A-Za-z0-9._-]+\.(?:sh|py))([^\n|&;)]*)')


def workflow_invocations(workflows: Path | None = None) -> dict[str, list[str]]:
    """Return script basename -> argument strings for workflow invocations.

    The live audit intentionally uses only build.yml: it is the blocking
    workflow's closed candidate set. A directory or file supplied explicitly
    is still accepted so the self-test can plant complete miniature workflows.
    """
    if workflows is None:
        workflow_files = [BUILD_WORKFLOW]
    elif workflows.is_file():
        workflow_files = [workflows]
    else:
        workflow_files = sorted(workflows.glob("*.yml"))
    found: dict[str, list[str]] = {}
    for wf in workflow_files:
        for raw in wf.read_text().splitlines():
            line = raw.strip()
            # Skip YAML comments and prose lines that merely name a script.
            if line.startswith("#"):
                continue
            for m in INVOCATION.finditer(line):
                name, args = m.group(1), m.group(2)
                found.setdefault(name, []).append(args.strip())
    return found


def dispatched_invocations(script: Path) -> dict[str, list[str]]:
    """Return executable ``run_step scripts/<name>`` edges in one script.

    The source is comment-stripped before matching, so a prose example of a
    dispatch cannot enlarge the gate population.  Missing scripts simply have
    no outgoing edges; their missing-source finding is still emitted by the
    caller that discovered them.
    """
    if not script.is_file():
        return {}
    found: dict[str, list[str]] = {}
    for raw in strip_comments(script.read_text()).splitlines():
        for m in DISPATCH_INVOCATION.finditer(raw):
            name, args = m.group(1), m.group(2)
            found.setdefault(name, []).append(args.strip())
    return found


def gate_invocations(workflows: Path | None = None,
                     scripts: Path | None = None) -> tuple[
                         dict[str, list[str]],
                         dict[str, list[str]],
                         dict[str, list[str]]]:
    """Return direct, bundle-only, and total workflow-reachable scripts.

    ``workflow_invocations`` remains the direct workflow view used by the
    self-test fixtures.  The total view follows ``run_step`` edges from every
    reachable script, preserving which names were direct and which were found
    only behind a bundle.  A set of visited parents prevents cycles while still
    allowing a nested bundle to expose its own child gates.
    """
    scripts = scripts or SCRIPTS
    direct = workflow_invocations(workflows)
    all_invocations: dict[str, list[str]] = {
        name: list(args) for name, args in direct.items()
    }
    bundled: dict[str, list[str]] = {}
    pending = list(direct)
    visited: set[str] = set()
    while pending:
        parent = pending.pop()
        if parent in visited:
            continue
        visited.add(parent)
        for child, args in dispatched_invocations(scripts / parent).items():
            all_invocations.setdefault(child, []).extend(args)
            if child not in direct:
                bundled.setdefault(child, []).extend(args)
            if child not in visited:
                pending.append(child)
    return direct, bundled, all_invocations


def gate_inventory(workflows: Path | None = None,
                   scripts: Path | None = None) -> dict[str, object]:
    """Classify every workflow-reachable script without using its filename.

    ``direct_invocations`` are the closed set named in ``build.yml``;
    ``bundled_invocations`` are executable ``run_step`` descendants. ``static``
    means the source file was read; ``static_can_fail`` is the weaker
    source-level result from ``CAN_FAIL``. Neither is a dynamic proof that a
    defect reaches the branch. The self-test's planted cases are the separate
    end-to-end evidence class.
    """
    scripts = scripts or SCRIPTS
    direct, bundled, invocations = gate_invocations(workflows, scripts)
    static: list[str] = []
    static_can_fail: list[str] = []
    static_silent: list[str] = []
    missing: list[str] = []
    for name in sorted(invocations):
        path = scripts / name
        if not path.is_file():
            missing.append(name)
            continue
        static.append(name)
        if CAN_FAIL.search(strip_comments(path.read_text())):
            static_can_fail.append(name)
        else:
            static_silent.append(name)
    return {
        "invocations": invocations,
        "direct_invocations": direct,
        "bundled_invocations": bundled,
        "static": static,
        "static_can_fail": static_can_fail,
        "static_silent": static_silent,
        "missing": missing,
    }


def check(workflows: Path | None = None, scripts: Path | None = None,
          advisory: dict[str, str] | None = None) -> list[str]:
    """Roots are parameters so the self-test can run the WHOLE check over a
    planted tree, rather than only asserting that the regexes match strings.

    #12907 is the cautionary case: a scanner whose `--self-test` proved the gate
    fired but not that the function under test still reached the code it was
    scanning.  A self-test that never calls `check()` has the same hole.
    """
    scripts = scripts or SCRIPTS
    advisory = ADVISORY_BY_DESIGN if advisory is None else advisory
    problems: list[str] = []
    inventory = gate_inventory(workflows, scripts)
    invocations = inventory["invocations"]
    bundled = inventory["bundled_invocations"]
    assert isinstance(invocations, dict)
    assert isinstance(bundled, dict)
    for name, arglists in sorted(invocations.items()):
        path = scripts / name
        if not path.is_file():
            route = "a bundle dispatch" if name in bundled else "the blocking workflow"
            problems.append(
                f"  x {name}  RULE C -- invoked by {route} but its "
                "source file is missing, so its failure path cannot be analysed")
            continue
        src = strip_comments(path.read_text())

        # RULE B first: a script with no failure path at all is worse than a
        # non-strict one, and the strict question is moot for it.
        if not CAN_FAIL.search(src):
            if name not in advisory:
                problems.append(
                    f"  x {name}  RULE B -- no failure path: no `exit N`/"
                    f"`return N`/`set -e` anywhere in the script, so no "
                    f"invocation can fail")
            continue

        if not STRICT_PARSE.search(src):
            continue  # no strictness flag; rule A does not apply

        # Ignore pure `--self-test` invocations: they exercise the gate, they
        # are not the gate.
        real = [a for a in arglists if "--self-test" not in a]
        if not real:
            continue
        if real and all("--strict" in a for a in real):
            continue

        if name in advisory:
            continue
        problems.append(
            f"  x {name}  RULE A -- parses `--strict` but CI invokes it without: "
            f"{' | '.join(repr(a) for a in real)}\n"
            f"      its failure path is unreachable in CI. Pass --strict, or add "
            f"it to ADVISORY_BY_DESIGN with a reason.")

    # Keep the advisory table honest: an entry that no longer describes reality
    # is a claim nobody is checking.
    for name in sorted(advisory):
        path = scripts / name
        if not path.is_file():
            problems.append(
                f"  x {name}  stale ADVISORY_BY_DESIGN entry -- no such script")
            continue
        if name not in invocations:
            problems.append(
                f"  x {name}  stale ADVISORY_BY_DESIGN entry -- not invoked by "
                f"any workflow")
            continue
        arglists = [a for a in invocations[name] if "--self-test" not in a]
        if arglists and all("--strict" in a for a in arglists):
            problems.append(
                f"  x {name}  stale ADVISORY_BY_DESIGN entry -- CI now passes "
                f"--strict, so the exemption is no longer needed. Drop it.")
    return problems


def _plant(tmp: Path, script: str, body: str, invocation: str) -> tuple[Path, Path]:
    """Write one fake gate and one fake workflow invoking it."""
    (tmp / "wf").mkdir(parents=True, exist_ok=True)
    (tmp / "sc").mkdir(parents=True, exist_ok=True)
    (tmp / "sc" / script).write_text(body)
    (tmp / "wf" / "planted.yml").write_text(f"      - name: x\n        run: {invocation}\n")
    return tmp / "wf", tmp / "sc"


def self_test() -> int:
    import shutil
    import tempfile
    ok = True
    # Spelled in two pieces on purpose: written whole, the planted fixtures
    # below would contain a literal `== "--strict"` and this file would trip its
    # OWN rule A. The gate takes no exemption for itself.
    flag = "--" + "strict"

    def expect(cond: bool, label: str) -> None:
        nonlocal ok
        if not cond:
            print(f"SELF-TEST FAIL: {label}", file=sys.stderr)
            ok = False

    # ---- end-to-end: the whole `check()` over planted trees, not just regexes.
    tmp = Path(tempfile.mkdtemp(prefix="gates-selftest-"))
    planted_passes = 0
    planted_labels: list[str] = []
    try:
        def expect_planted(cond: bool, label: str, name: str) -> None:
            nonlocal planted_passes
            if cond:
                planted_passes += 1
                planted_labels.append(name)
            expect(cond, label)

        # PLANTED 1 - strict-capable gate invoked bare, undeclared: rule A fires.
        wf, sc = _plant(tmp / "a", "check-planted.sh",
                        f'[[ "${{1:-}}" == "{flag}" ]] && STRICT=1\n'
                        '[[ $STRICT -eq 1 ]] && exit 1\nexit 0\n',
                        "scripts/check-planted.sh")
        r = check(wf, sc, advisory={})
        expect_planted(len(r) == 1 and "RULE A" in r[0], f"planted rule A: {r}",
                       "check-planted.sh / Rule A")

        # CONTROL 1a - the same gate invoked WITH --strict: silent.
        wf, sc = _plant(tmp / "b", "check-planted.sh",
                        f'[[ "${{1:-}}" == "{flag}" ]] && STRICT=1\n'
                        '[[ $STRICT -eq 1 ]] && exit 1\nexit 0\n',
                        f"scripts/check-planted.sh {flag}")
        expect(check(wf, sc, advisory={}) == [], "control: --strict passes")

        # CONTROL 1b - bare, but DECLARED advisory: silent.
        wf, sc = _plant(tmp / "c", "check-planted.sh",
                        f'[[ "${{1:-}}" == "{flag}" ]] && STRICT=1\n'
                        '[[ $STRICT -eq 1 ]] && exit 1\nexit 0\n',
                        "scripts/check-planted.sh")
        expect(check(wf, sc, advisory={"check-planted.sh": "reason"}) == [],
               "control: declared advisory passes")

        # PLANTED 2 - a gate with no failure path at all: rule B fires.
        wf, sc = _plant(tmp / "d", "check-mute.sh",
                        'echo "all good"\nexit 0\n', "scripts/check-mute.sh")
        r = check(wf, sc, advisory={})
        expect_planted(len(r) == 1 and "RULE B" in r[0], f"planted rule B: {r}",
                       "check-mute.sh / Rule B")

        # CONTROL 2a - `exit "$rc"` IS a failure path (the false accusation the
        # first draft of this script made against check-guest-elf-override.sh).
        wf, sc = _plant(tmp / "e", "check-rc.sh",
                        'rc=0\nfail() { rc=1; }\nexit "$rc"\n', "scripts/check-rc.sh")
        expect(check(wf, sc, advisory={}) == [], "control: exit \"$rc\" can fail")

        # CONTROL 2b - `&& exit 1` IS a failure path (the second false
        # accusation, against check-obligation-blockers.sh).
        wf, sc = _plant(tmp / "f", "check-and.sh",
                        'set -uo pipefail\n[[ $S -eq 1 ]] && exit 1\nexit 0\n',
                        "scripts/check-and.sh")
        expect(check(wf, sc, advisory={}) == [], "control: `&& exit 1` can fail")

        # CONTROL 2c - an `exit 1` that appears ONLY inside a usage comment does
        # NOT count. This is the direction that matters: counting it would let a
        # genuinely silent gate through.
        wf, sc = _plant(tmp / "g", "check-cmt.sh",
                        f'#   scripts/check-cmt.sh {flag} # exit 1 on a violation\n'
                        'echo hi\nexit 0\n', "scripts/check-cmt.sh")
        r = check(wf, sc, advisory={})
        expect(len(r) == 1 and "RULE B" in r[0],
               f"control: commented-out `exit 1` does not count: {r}")

        # CONTROL 2d - static presence is not dynamic reachability. An exit in
        # an unreachable branch is intentionally accepted by this source scan;
        # it is not counted among the plant-proven cases below.
        wf, sc = _plant(tmp / "g2", "check-unreachable.sh",
                        'if false; then exit 1; fi\nexit 0\n',
                        "scripts/check-unreachable.sh")
        expect(check(wf, sc, advisory={}) == [],
               "control: unreachable static exit is not called plant-proven")

        # CONTROL 3 - filename-neutral discovery: a silent script whose basename
        # is not `check-*` is still an analysed build candidate.
        wf, sc = _plant(tmp / "h", "report_thing.py",
                        'import sys\nprint("{}")\n', "python3 scripts/report_thing.py")
        r = check(wf, sc, advisory={})
        expect_planted(len(r) == 1 and "RULE B" in r[0],
                       f"filename-neutral silent script is caught: {r}",
                       "report_thing.py / Rule B")

        # CONTROL 3b - the queue tool remains covered without an opt-in name list.
        wf, sc = _plant(tmp / "h2", "callee-composition-queue.py",
                        'print("all good")\n',
                        "python3 scripts/callee-composition-queue.py --self-test")
        r = check(wf, sc, advisory={})
        expect_planted(len(r) == 1 and "RULE B" in r[0],
                       f"queue tool is checked without an opt-in list: {r}",
                       "callee-composition-queue.py / Rule B")

        # CONTROL 3c - import-graph-metrics is covered by the same behavioral
        # discovery, not by a special exception.
        wf, sc = _plant(tmp / "h3", "import-graph-metrics.py",
                        'print("all good")\n',
                        "python3 scripts/import-graph-metrics.py --check")
        r = check(wf, sc, advisory={})
        expect_planted(len(r) == 1 and "RULE B" in r[0],
                       f"metrics tool is checked without an opt-in list: {r}",
                       "import-graph-metrics.py / Rule B")

        # CONTROL 3d - a counted but missing script is not silently skipped.
        wf, sc = _plant(tmp / "h4", "present.py", 'print("all good")\n',
                        "python3 scripts/missing.py")
        r = check(wf, sc, advisory={})
        expect_planted(len(r) == 1 and "RULE C" in r[0],
                       f"missing source is reported as unanalysed: {r}",
                       "missing.py / Rule C")

        # PLANTED 4 - a gate hidden behind an executable bundle dispatch is
        # discovered and analysed too.  The commented edge is a control for
        # the same blind spot: prose must not enlarge the reachable set.
        bundle_wf, bundle_sc = _plant(tmp / "h5", "bundle.sh",
                                      'set -e\n'
                                      '# run_step scripts/hidden.py\n'
                                      'run_step scripts/nested.py\n',
                                      "scripts/bundle.sh")
        (bundle_sc / "nested.py").write_text('print("all good")\n')
        r = check(bundle_wf, bundle_sc, advisory={})
        bundle_inventory = gate_inventory(bundle_wf, bundle_sc)
        bundle_names = bundle_inventory["invocations"]
        assert isinstance(bundle_names, dict)
        expect_planted(len(r) == 1 and "RULE B" in r[0]
                       and "nested.py" in r[0],
                       f"bundle dispatch is analysed: {r}",
                       "nested.py / bundled Rule B")
        expect("hidden.py" not in bundle_names,
               "control: commented bundle dispatch is ignored")

        # CONTROL 4 - a stale advisory entry naming nothing is caught.
        wf, sc = _plant(tmp / "i", "check-real.sh", 'set -e\nexit 1\n',
                        "scripts/check-real.sh")
        r = check(wf, sc, advisory={"check-gone.sh": "reason"})
        expect(len(r) == 1 and "stale" in r[0], f"stale advisory entry: {r}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    # ---- the live tree must be clean, or this gate is wrong about itself.
    live = check()
    expect(not live, "live tree clean, got:\n" + "\n".join(live))

    live_inventory = gate_inventory()
    invocations = live_inventory["invocations"]
    direct = live_inventory["direct_invocations"]
    bundled = live_inventory["bundled_invocations"]
    static = live_inventory["static"]
    static_can_fail = live_inventory["static_can_fail"]
    missing = live_inventory["missing"]
    silent = live_inventory["static_silent"]
    assert isinstance(invocations, dict)
    assert isinstance(direct, dict)
    assert isinstance(bundled, dict)
    assert isinstance(static, list)
    assert isinstance(static_can_fail, list)
    assert isinstance(missing, list)
    assert isinstance(silent, list)
    expect(not missing and not silent,
           "live inventory has no unanalysed scripts: "
           f"missing={missing}, silent={silent}")

    if ok:
        print("check-gates-can-fail --self-test: OK ("
              f"direct-invoked={len(direct)}; bundled-only={len(bundled)}; "
              f"reachable={len(invocations)}; static-analysed={len(static)}; "
              f"static-can-fail={len(static_can_fail)}; "
              f"unanalysed=0; plant-proven={planted_passes} synthetic cases; "
              "15 end-to-end assertions (7 planted + 8 controls, incl. both "
              "false accusations the first draft made); "
              "live tree clean)")
        print("  plant-proven detector cases: " + ", ".join(planted_labels))
        return 0
    return 1


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()
    inventory = gate_inventory()
    invocations = inventory["invocations"]
    direct = inventory["direct_invocations"]
    bundled = inventory["bundled_invocations"]
    static = inventory["static"]
    static_can_fail = inventory["static_can_fail"]
    unanalysed = inventory["missing"] + inventory["static_silent"]
    assert isinstance(invocations, dict)
    assert isinstance(direct, dict)
    assert isinstance(bundled, dict)
    assert isinstance(static, list)
    assert isinstance(static_can_fail, list)
    assert isinstance(unanalysed, list)
    problems = check()
    n = len(invocations)
    if problems:
        print(f"check-gates-can-fail: {len(problems)} problem(s); "
              f"direct-invoked={len(direct)}; bundled-only={len(bundled)}; "
              f"reachable={n}; static-analysed={len(static)}; "
              f"static-can-fail={len(static_can_fail)}; "
              f"unanalysed={len(unanalysed)}")
        print("\n".join(problems))
        print(
            "\nA gate that cannot fail is indistinguishable from an absent one, and\n"
            "worse, because the workflow step reads as coverage. Either pass the\n"
            "strictness flag or declare the gate advisory with a reason.",
            file=sys.stderr)
        return 1
    print("check-gates-can-fail: OK ("
          f"direct-invoked={len(direct)}; bundled-only={len(bundled)}; "
          f"reachable={n}; static-analysed={len(static)}; "
          f"static-can-fail={len(static_can_fail)}; unanalysed=0; "
          f"plant-proven=see --self-test ({len(ADVISORY_BY_DESIGN)} declared "
          "advisory strictness exceptions)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
