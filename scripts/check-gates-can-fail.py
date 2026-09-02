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
`.github/workflows/build.yml` and follows executable shell/Python dispatches
(`run_step`, `python3`, `bash`, `sh`, `exec`, and `./scripts`) from those
scripts (and their transitive dispatches).  This keeps
the workflow candidate set closed without depending on the `check-*` filename
convention or an opt-in list, while still seeing gates hidden behind the
parallel bundle.  The normal report distinguishes DIRECTLY INVOKED scripts
from BUNDLE-REACHABLE scripts and from the weaker source-level
STATIC-ANALYSED result, and lists any unanalysed names.  `--self-test` adds a
separate PLANT-PROVEN count for synthetic end-to-end cases; that count is not a
claim that a generic harness exercised every production gate's defect branch.
The live check also compares the direct workflow set with the
`check-build-parallel.sh` closure: every direct-only name needs an exact,
non-empty omission reason, and stale declarations fail.  A small live-tree
floor and required-name assertion prevents the discovery function itself from
quietly seeing no production gates.

Usage:
  scripts/check-gates-can-fail.py              # audit build.yml script invocations
  scripts/check-gates-can-fail.py --self-test  # planted cases + controls
"""
from __future__ import annotations

import ast
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
# Bundle scripts dispatch child gates through `run_step`, while shell wrappers
# invoke their checker implementations with `python3`/`exec`.  Keep the
# patterns anchored to shell command position so Python docstrings and usage
# prose are not mistaken for edges.  The closure below is deliberately
# transitive: a future bundle may delegate to another bundle without reopening
# this blind spot.
RUN_STEP_INVOCATION = re.compile(
    r'^\s*(?:start\s+\S+\s+)?run_step\s+'
    r'(?:\./)?scripts/([A-Za-z0-9._-]+\.(?:sh|py))([^\n|&;)]*)')
SHELL_SCRIPT_INVOCATION = re.compile(
    r'^\s*(?:if\s+!\s+)?(?:exec\s+)?(?:python3?|bash|sh)\s+'
    r'["\']?(?:\$[A-Za-z_][A-Za-z0-9_]*/)?'
    r'(?:\./)?scripts/([A-Za-z0-9._-]+\.(?:sh|py))([^\n|&;)]*)')
EXEC_SCRIPT_INVOCATION = re.compile(
    r'^\s*exec\s+["\']?(?:\$[A-Za-z_][A-Za-z0-9_]*/)?'
    r'(?:\./)?scripts/([A-Za-z0-9._-]+\.(?:sh|py))([^\n|&;)]*)')
DIRECT_SCRIPT_INVOCATION = re.compile(
    r'^\s*(?:if\s+!\s+)?\./scripts/'
    r'([A-Za-z0-9._-]+\.(?:sh|py))([^\n|&;)]*)')

# A `run_step` target is a gate regardless of its spelling (the bundle uses
# `fuzz-arith-diff.sh` and `codegen-stateless-link-check.sh`).  Nested checker
# and audit entry points are gates too; `gen-*` and the named data/code
# generators are helpers whose lack of an explicit failure path must not be
# reported as an inert gate.  Other helper implementations are already covered
# by their shell wrapper and remain non-gate edges in the provenance graph.
GATE_SCRIPT_PREFIXES = ("check-", "audit-")
GENERATOR_SCRIPT_NAMES = frozenset({
    "asm_to_program.py",
    "codegen-eest-stateless-check.sh",
    "drift-report.sh",
    "guest_image_coverage.py",
    "shape-census.py",
    "transcription_queue.py",
})

# ``check-build-parallel.sh`` is a local post-build bundle, not a replacement
# for the workflow's source/build-preparation lanes.  Keep that boundary
# explicit: every direct workflow script which is intentionally *not* a child
# of the bundle is named here with a reason.  The set is checked against the
# live workflow and bundle closure below, so adding a direct CI gate without
# either dispatching it from the bundle or recording why it stays outside is a
# hard failure.  A reason is part of the declaration, not prose for a reviewer
# to remember.
_BUNDLE_ROOT_ONLY = {
    "check-build-parallel.sh":
        "the workflow invokes the bundle entry point itself; it is not its own child",
}
_BUNDLE_SOURCE_CHECK_ONLY = {
    "check-code-preimage-empty-hash.sh",
    "check-artifact-writer-ownership.py",
    "check-correspondence-deps.sh",
    "check-duplicate-decls.py",
    "check-eest-sampler-span.py",
    "check-forbidden-tactics.sh",
    "check-gates-can-fail.py",
    "check-guest-elf-override.sh",
    "check-heartbeats-approved.sh",
    "check-jaloff-closure.sh",
    "check-layering.sh",
    "check-layout-literals.sh",
    "check-mpt-status-vocab.sh",
    "check-naming.sh",
    "check-no-hardcoded-guest-pc.sh",
    "check-opcode-structure.sh",
    "check-phase-entry-pinned.py",
    "check-prog-base-coverage.py",
    "check-registry-crosscheck.sh",
    "check-render-oracle-coverage.py",
    "check-retired-predicates.sh",
    "check-routine-liveness.sh",
    "check-specref-citations.py",
    "check-unimported.sh",
    "check-wrapper-jal-vacuity.py",
    "import-graph-metrics.py",
    "proof-frontier.py",
}
_BUNDLE_BUILD_PHASE_ONLY = {
    "callee-composition-queue.py",
    "check-derived-artifacts.py",
    "check-evidence-ledger.py",
    "check-embedded-counts.sh",
    "check-no-warnings.sh",
    "check-nonvacuity-witnessed.py",
    "check-obligation-blockers.sh",
    "check-obligation-claims.sh",
    "check-registry-tallies.py",
    "check-roundtrip-coverage.sh",
    "check-seam-contract-ledger.py",
    "check-statement-tamper.sh",
    "gen-rv64-shims.py",
}
BUNDLE_DIRECT_ONLY_REASONS = {
    **_BUNDLE_ROOT_ONLY,
    **{
        name: "source-checks job runs this before the post-build bundle and owns its setup"
        for name in _BUNDLE_SOURCE_CHECK_ONLY
    },
    **{
        name: "build job runs this in a phase-specific step whose inputs are not the bundle"
        for name in _BUNDLE_BUILD_PHASE_ONLY
    },
}

# A self-test that only injects miniature workflows can prove that a planted
# defect fires while completely missing a broken production discovery path.
# Keep a small live-tree floor and a few names whose presence is not optional;
# if workflow parsing or bundle traversal goes silent, the meta-gate fails
# loudly instead of printing a reassuring zero-sized inventory.  These values
# are intentionally lower bounds: adding a gate is harmless, while removing a
# known gate requires an explicit review of this assertion.
LIVE_DIRECT_FLOOR = 38
LIVE_BUNDLE_REACHABLE_FLOOR = 31
LIVE_REQUIRED_DIRECT = frozenset({
    "check-build-parallel.sh",
    "check-file-size.sh",
    "check-gates-can-fail.py",
})
LIVE_REQUIRED_BUNDLE = frozenset({
    "check-build-units-link.sh",
    "check-drift.sh",
    "check-file-size.sh",
})


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


def dispatched_invocations(script: Path) -> dict[str, list[tuple[str, str]]]:
    """Return executable shell/Python dispatch edges in one script.

    The source is comment-stripped before matching, so a prose example of a
    dispatch cannot enlarge the gate population.  Missing scripts simply have
    no outgoing edges; their missing-source finding is still emitted by the
    caller that discovered them.  Python command lists are inspected through
    the AST (not raw prose), so a helper's documentation and self-test strings
    cannot become edges merely by mentioning a script.
    """
    if not script.is_file():
        return {}
    found: dict[str, list[tuple[str, str]]] = {}
    if script.suffix == ".sh":
        for raw in strip_comments(script.read_text()).splitlines():
            m = RUN_STEP_INVOCATION.match(raw)
            mode = "run_step"
            if m is None:
                m = SHELL_SCRIPT_INVOCATION.match(raw)
                mode = "shell"
            if m is None:
                m = EXEC_SCRIPT_INVOCATION.match(raw)
                mode = "shell"
            if m is None:
                m = DIRECT_SCRIPT_INVOCATION.match(raw)
                mode = "shell"
            if m is None:
                continue
            name, args = m.group(1), m.group(2)
            found.setdefault(name, []).append((args.strip(), mode))
        return found

    if script.suffix != ".py":
        return found
    try:
        tree = ast.parse(script.read_text(), filename=str(script))
    except SyntaxError:
        return found
    # Only inspect command-running calls.  This avoids treating arbitrary
    # strings in Python source (including docstrings and fixture prose) as
    # dispatches while covering the repository's `run([...])` wrappers and
    # direct subprocess APIs.
    command_calls = {"run", "check_call", "check_output", "Popen"}
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or not node.args:
            continue
        func = node.func
        func_name = func.id if isinstance(func, ast.Name) else (
            func.attr if isinstance(func, ast.Attribute) else "")
        if func_name not in command_calls:
            continue
        for value in ast.walk(node.args[0]):
            if not isinstance(value, ast.Constant) or not isinstance(value.value, str):
                continue
            match = re.search(
                r'(?<![\w/-])(?:\./)?scripts/([A-Za-z0-9._-]+\.(?:sh|py))',
                value.value)
            if match:
                name = match.group(1)
                found.setdefault(name, []).append((value.value, "python"))
    return found


def gate_invocations(workflows: Path | None = None,
                     scripts: Path | None = None) -> tuple[
                         dict[str, list[str]],
                         dict[str, list[str]],
                         dict[str, list[str]],
                         dict[str, list[str]],
                         dict[str, list[str]]]:
    """Return direct, bundle-only, total gates, non-gates, and bundle closure.

    ``workflow_invocations`` remains the direct workflow view used by the
    self-test fixtures.  The total view follows executable shell/Python dispatch
    edges from every reachable script, preserving which names were direct and
    which were found only behind a bundle.  ``bundle_reachable`` is a separate
    closure rooted only at ``check-build-parallel.sh``; unlike
    ``bundled_invocations`` it includes direct names that the bundle itself
    dispatches.  A set of visited parents prevents cycles while still allowing
    a nested bundle to expose its own child gates.
    Generator/helper
    edges are retained separately so they are visible without being graded as
    gates merely because they lack a failure status.
    """
    scripts = scripts or SCRIPTS
    direct = workflow_invocations(workflows)
    all_invocations: dict[str, list[str]] = {
        name: list(args) for name, args in direct.items()
    }
    bundled: dict[str, list[str]] = {}
    non_gate: dict[str, list[str]] = {}
    bundle_reachable: dict[str, list[str]] = {}
    pending = list(direct)
    visited: set[str] = set()
    while pending:
        parent = pending.pop()
        if parent in visited:
            continue
        visited.add(parent)
        for child, edges in dispatched_invocations(scripts / parent).items():
            for args, mode in edges:
                is_gate = (mode == "run_step"
                           or child.startswith(GATE_SCRIPT_PREFIXES))
                if child.startswith("gen-") or child in GENERATOR_SCRIPT_NAMES:
                    is_gate = False
                target = all_invocations if is_gate else non_gate
                target.setdefault(child, []).append(args)
                if is_gate and child not in direct:
                    bundled.setdefault(child, []).append(args)
            if child not in visited:
                pending.append(child)

    # The local post-build bundle is the boundary checked by
    # ``bundle_sync_problems``.  Walk it independently from the all-workflow
    # closure: a direct source/build-preparation script may itself dispatch a
    # helper, but that does not make the helper part of check-build-parallel's
    # contract.  Keep the root out of the closure; it is declared separately as
    # a deliberate root-only omission.
    bundle_pending = []
    if "check-build-parallel.sh" in direct:
        bundle_pending.append("check-build-parallel.sh")
    bundle_visited: set[str] = set()
    while bundle_pending:
        parent = bundle_pending.pop()
        if parent in bundle_visited:
            continue
        bundle_visited.add(parent)
        for child, edges in dispatched_invocations(scripts / parent).items():
            for args, mode in edges:
                is_gate = (mode == "run_step"
                           or child.startswith(GATE_SCRIPT_PREFIXES))
                if child.startswith("gen-") or child in GENERATOR_SCRIPT_NAMES:
                    is_gate = False
                if not is_gate:
                    continue
                bundle_reachable.setdefault(child, []).append(args)
            # Follow helper edges too: a non-gate wrapper may dispatch a gate
            # one level farther down, and the set comparison must not miss it
            # merely because the intermediate basename is not ``check-*``.
            if child not in bundle_visited:
                bundle_pending.append(child)

    return direct, bundled, all_invocations, non_gate, bundle_reachable


def gate_inventory(workflows: Path | None = None,
                   scripts: Path | None = None) -> dict[str, object]:
    """Classify every workflow-reachable script without using its filename.

    ``direct_invocations`` are the closed set named in ``build.yml``;
    ``bundled_invocations`` are executable dispatch descendants found only
    behind a direct invocation, while ``bundle_reachable_invocations`` is the
    closure rooted specifically at ``check-build-parallel.sh``. ``static``
    means the source file was read; ``static_can_fail`` is the weaker
    source-level result from ``CAN_FAIL``. Neither is a dynamic proof that a
    defect reaches the branch. The self-test's planted cases are the separate
    end-to-end evidence class.
    """
    scripts = scripts or SCRIPTS
    direct, bundled, invocations, non_gate, bundle_reachable = gate_invocations(
        workflows, scripts)
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
        "bundle_reachable_invocations": bundle_reachable,
        "non_gate_dispatches": non_gate,
        "static": static,
        "static_can_fail": static_can_fail,
        "static_silent": static_silent,
        "missing": missing,
    }


def bundle_sync_problems(
    inventory: dict[str, object],
    declared: dict[str, str],
) -> list[str]:
    """Check the workflow/bundle boundary as an explicit set relation.

    ``direct_invocations`` is the blocking workflow's set and
    ``bundle_reachable_invocations`` is the set reached from the local
    parallel bundle (including direct names that the bundle dispatches).
    The bundle need not duplicate source/build-preparation lanes, but every
    direct-only name must be declared with a reason.  This turns a silent
    omission into a reviewable manifest entry and catches both directions:
    an unannounced new omission and a stale declaration after a gate is moved
    into the bundle.
    """
    direct = inventory.get("direct_invocations", {})
    bundled = inventory.get("bundle_reachable_invocations", {})
    if not isinstance(direct, dict) or not isinstance(bundled, dict):
        return ["  x bundle sync -- inventory did not expose invocation sets"]
    direct_names = set(direct)
    bundled_names = set(bundled)
    direct_only = direct_names - bundled_names
    declared_names = set(declared)
    problems: list[str] = []

    for name in sorted(direct_only - declared_names):
        problems.append(
            f"  x {name}  BUNDLE SYNC -- direct workflow gate is not reached "
            "by check-build-parallel and has no declared reason; dispatch it "
            "from the bundle or add an explicit omission reason"
        )
    for name in sorted(declared_names - direct_only):
        if name in bundled_names:
            why = "it is now bundled"
        elif name not in direct_names:
            why = "it is not directly invoked by the blocking workflow"
        else:
            why = "its direct/bundle relation changed"
        problems.append(
            f"  x {name}  BUNDLE SYNC -- stale omission declaration: {why}; "
            "remove the declaration or update the bundle"
        )
    for name, reason in sorted(declared.items()):
        if not isinstance(reason, str) or not reason.strip():
            problems.append(
                f"  x {name}  BUNDLE SYNC -- omission declaration has no reason"
            )

    return problems


def live_visibility_problems(inventory: dict[str, object]) -> list[str]:
    """Ensure the production discovery still sees its known gate population.

    Planted self-tests validate the detector's firing behavior, but they cannot
    catch a parser that silently stops finding real workflow entries.  This
    floor is deliberately separate from the direct/bundle boundary manifest:
    it protects the instrument's input population, while the manifest protects
    the relation between the two sets.
    """
    direct = inventory.get("direct_invocations", {})
    bundled = inventory.get("bundle_reachable_invocations", {})
    if not isinstance(direct, dict) or not isinstance(bundled, dict):
        return ["  x LIVE VISIBILITY -- invocation sets are unavailable"]
    direct_names = set(direct)
    bundled_names = set(bundled)
    problems: list[str] = []
    if len(direct_names) < LIVE_DIRECT_FLOOR:
        problems.append(
            f"  x LIVE VISIBILITY -- direct workflow gate count {len(direct_names)} "
            f"is below floor {LIVE_DIRECT_FLOOR}; discovery may have gone silent"
        )
    if len(bundled_names) < LIVE_BUNDLE_REACHABLE_FLOOR:
        problems.append(
            f"  x LIVE VISIBILITY -- bundle-reachable gate count "
            f"{len(bundled_names)} is below floor {LIVE_BUNDLE_REACHABLE_FLOOR}; "
            "bundle traversal may have gone silent"
        )
    for name in sorted(LIVE_REQUIRED_DIRECT - direct_names):
        problems.append(
            f"  x LIVE VISIBILITY -- expected direct gate {name} was not found"
        )
    for name in sorted(LIVE_REQUIRED_BUNDLE - bundled_names):
        problems.append(
            f"  x LIVE VISIBILITY -- expected bundle gate {name} was not found"
        )
    return problems


def check(workflows: Path | None = None, scripts: Path | None = None,
          advisory: dict[str, str] | None = None,
          bundle_direct_only: dict[str, str] | None = None) -> list[str]:
    """Roots are parameters so the self-test can run the WHOLE check over a
    planted tree, rather than only asserting that the regexes match strings.

    #12907 is the cautionary case: a scanner whose `--self-test` proved the gate
    fired but not that the function under test still reached the code it was
    scanning.  A self-test that never calls `check()` has the same hole.
    """
    production = workflows is None and scripts is None
    scripts = scripts or SCRIPTS
    advisory = ADVISORY_BY_DESIGN if advisory is None else advisory
    problems: list[str] = []
    inventory = gate_inventory(workflows, scripts)
    invocations = inventory["invocations"]
    bundled = inventory["bundled_invocations"]
    bundle_reachable = inventory["bundle_reachable_invocations"]
    assert isinstance(invocations, dict)
    assert isinstance(bundled, dict)
    assert isinstance(bundle_reachable, dict)

    # The production invocation uses the checked-in manifest.  Synthetic
    # self-tests opt in explicitly so their tiny workflows do not inherit the
    # live tree's unrelated declarations.
    if bundle_direct_only is not None:
        problems.extend(bundle_sync_problems(inventory, bundle_direct_only))
    elif production:
        problems.extend(bundle_sync_problems(inventory, BUNDLE_DIRECT_ONLY_REASONS))
        problems.extend(live_visibility_problems(inventory))

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
        (bundle_sc / "gen-helper.py").write_text('print("generated")\n')
        (bundle_sc / "bundle.sh").write_text(
            'set -e\n'
            '# run_step scripts/hidden.py\n'
            'run_step scripts/nested.py\n'
            './scripts/check-dot-nested.py\n'
            'python3 scripts/gen-helper.py\n')
        (bundle_sc / "check-dot-nested.py").write_text('print("all good")\n')
        r = check(bundle_wf, bundle_sc, advisory={})
        bundle_inventory = gate_inventory(bundle_wf, bundle_sc)
        bundle_names = bundle_inventory["invocations"]
        bundle_non_gates = bundle_inventory["non_gate_dispatches"]
        assert isinstance(bundle_names, dict)
        assert isinstance(bundle_non_gates, dict)
        expect_planted(len(r) == 2 and all("RULE B" in problem for problem in r)
                       and any("nested.py" in problem for problem in r)
                       and any("check-dot-nested.py" in problem for problem in r),
                       f"bundle dispatch is analysed: {r}",
                       "nested.py + dot-slash / bundled Rule B")
        expect("hidden.py" not in bundle_names,
               "control: commented bundle dispatch is ignored")
        expect("gen-helper.py" not in bundle_names
               and "gen-helper.py" in bundle_non_gates,
               "control: generator dispatch is not graded as a gate")

        # PLANTED 5 - Python command-list dispatch is also part of the closure;
        # AST inspection keeps a prose string in the module from becoming an
        # edge.  The direct wrapper has an explicit status-return path so only
        # the planted child is expected to trigger Rule B.
        py_wf, py_sc = _plant(tmp / "h6", "bundle.py",
                              '"""subprocess.run(["python3", '
                              '"scripts/hidden.py"])"""\n'
                              'import subprocess\n'
                              'def main():\n'
                              '    subprocess.run(["python3", '
                              '"scripts/check-nested.py"])\n'
                              '    return 0\n'
                              'if __name__ == "__main__":\n'
                              '    raise SystemExit(main())\n',
                              "python3 scripts/bundle.py")
        (py_sc / "check-nested.py").write_text('print("all good")\n')
        py_r = check(py_wf, py_sc, advisory={})
        py_inventory = gate_inventory(py_wf, py_sc)
        py_names = py_inventory["invocations"]
        assert isinstance(py_names, dict)
        expect_planted(len(py_r) == 1 and "RULE B" in py_r[0]
                       and "check-nested.py" in py_r[0],
                       f"Python bundle dispatch is analysed: {py_r}",
                       "check-nested.py / Python bundled Rule B")
        expect("hidden.py" not in py_names,
               "control: Python docstring is not a dispatch edge")

        # CONTROL 4 - a stale advisory entry naming nothing is caught.
        wf, sc = _plant(tmp / "i", "check-real.sh", 'set -e\nexit 1\n',
                        "scripts/check-real.sh")
        r = check(wf, sc, advisory={"check-gone.sh": "reason"})
        expect(len(r) == 1 and "stale" in r[0], f"stale advisory entry: {r}")

        # PLANTED 6a - an extra direct workflow gate which the parallel bundle
        # does not dispatch must be declared explicitly.  This is the positive
        # direction of the set-boundary check: a missing declaration is a hard
        # failure, not an omission someone can forget indefinitely.
        wf, sc = _plant(tmp / "j", "check-build-parallel.sh", "set -e\n",
                        "scripts/check-build-parallel.sh")
        (sc / "check-extra.py").write_text("exit 1\n")
        planted = wf / "planted.yml"
        planted.write_text(
            planted.read_text() + "      - name: extra\n"
            "        run: scripts/check-extra.py\n"
        )
        r = check(wf, sc, advisory={},
                  bundle_direct_only={
                      "check-build-parallel.sh": "the bundle root",
                  })
        expect_planted(len(r) == 1 and "BUNDLE SYNC" in r[0]
                       and "check-extra.py" in r[0],
                       f"undeclared direct-only gate is caught: {r}",
                       "check-extra.py / undeclared bundle omission")

        # PLANTED 6b - a declaration for a gate that is no longer direct-only
        # must fail too.  This is the stale direction: moving the child into
        # the bundle (or removing it from the workflow) cannot leave a silently
        # rotting exception in the manifest.
        wf, sc = _plant(tmp / "k", "check-build-parallel.sh",
                        "set -e\n", "scripts/check-build-parallel.sh")
        r = check(wf, sc, advisory={},
                  bundle_direct_only={
                      "check-build-parallel.sh": "the bundle root",
                      "check-gone.py": "stale test declaration",
                  })
        expect_planted(len(r) == 1 and "BUNDLE SYNC" in r[0]
                       and "check-gone.py" in r[0],
                       f"stale bundle omission is caught: {r}",
                       "check-gone.py / stale bundle omission")

        # CONTROL 5 - the same direct workflow/bundle relation is clean when
        # every direct-only name has a non-empty declaration.
        wf, sc = _plant(tmp / "l", "check-build-parallel.sh",
                        "run_step scripts/check-child.py\n",
                        "scripts/check-build-parallel.sh")
        (sc / "check-child.py").write_text("exit 1\n")
        r = check(wf, sc, advisory={},
                  bundle_direct_only={
                      "check-build-parallel.sh": "the bundle root",
                  })
        expect(not any("BUNDLE SYNC" in problem for problem in r),
               f"declared direct/bundle relation is clean: {r}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    # ---- the live tree must be clean, or this gate is wrong about itself.
    live = check()
    expect(not live, "live tree clean, got:\n" + "\n".join(live))

    live_inventory = gate_inventory()
    invocations = live_inventory["invocations"]
    direct = live_inventory["direct_invocations"]
    bundled = live_inventory["bundled_invocations"]
    bundle_reachable = live_inventory["bundle_reachable_invocations"]
    non_gate = live_inventory["non_gate_dispatches"]
    static = live_inventory["static"]
    static_can_fail = live_inventory["static_can_fail"]
    missing = live_inventory["missing"]
    silent = live_inventory["static_silent"]
    assert isinstance(invocations, dict)
    assert isinstance(direct, dict)
    assert isinstance(bundled, dict)
    assert isinstance(bundle_reachable, dict)
    assert isinstance(non_gate, dict)
    assert isinstance(static, list)
    assert isinstance(static_can_fail, list)
    assert isinstance(missing, list)
    assert isinstance(silent, list)
    expect(not missing and not silent,
           "live inventory has no unanalysed scripts: "
           f"missing={missing}, silent={silent}")

    if ok:
        direct_only = set(direct) - set(bundle_reachable)
        print("check-gates-can-fail --self-test: OK ("
              f"direct-invoked={len(direct)}; bundled-only={len(bundled)}; "
              f"bundle-reachable={len(bundle_reachable)}; "
              f"direct-only={len(direct_only)}; "
              f"reachable={len(invocations)}; static-analysed={len(static)}; "
              f"static-can-fail={len(static_can_fail)}; "
              f"non-gate-dispatches={len(non_gate)}; "
              f"unanalysed=0; plant-proven={planted_passes} synthetic cases; "
              "21 end-to-end assertions (10 planted + 11 controls, incl. "
              "bundle-set visibility and both false accusations the first "
              "draft made); live visibility floor and required names clean; "
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
    bundle_reachable = inventory["bundle_reachable_invocations"]
    non_gate = inventory["non_gate_dispatches"]
    static = inventory["static"]
    static_can_fail = inventory["static_can_fail"]
    unanalysed = inventory["missing"] + inventory["static_silent"]
    assert isinstance(invocations, dict)
    assert isinstance(direct, dict)
    assert isinstance(bundled, dict)
    assert isinstance(bundle_reachable, dict)
    assert isinstance(non_gate, dict)
    assert isinstance(static, list)
    assert isinstance(static_can_fail, list)
    assert isinstance(unanalysed, list)
    problems = check()
    n = len(invocations)
    direct_only = set(direct) - set(bundle_reachable)
    if problems:
        print(f"check-gates-can-fail: {len(problems)} problem(s); "
              f"direct-invoked={len(direct)}; bundled-only={len(bundled)}; "
              f"bundle-reachable={len(bundle_reachable)}; "
              f"direct-only={len(direct_only)}; "
              f"reachable={n}; static-analysed={len(static)}; "
              f"static-can-fail={len(static_can_fail)}; "
              f"non-gate-dispatches={len(non_gate)}; "
              f"unanalysed={len(unanalysed)}")
        print("\n".join(problems))
        print(
            "\nA gate that cannot fail is indistinguishable from an absent one, and\n"
            "worse, because the workflow step reads as coverage. Either pass the\n"
            "strictness flag or declare the gate advisory with a reason. The\n"
            "direct workflow/bundle sets must also stay in sync: dispatch each\n"
            "direct-only gate or declare a non-empty omission reason.",
            file=sys.stderr)
        return 1
    print("check-gates-can-fail: OK ("
          f"direct-invoked={len(direct)}; bundled-only={len(bundled)}; "
          f"bundle-reachable={len(bundle_reachable)}; "
          f"direct-only={len(direct_only)}; "
          f"reachable={n}; static-analysed={len(static)}; "
          f"static-can-fail={len(static_can_fail)}; "
          f"non-gate-dispatches={len(non_gate)}; unanalysed=0; "
          f"plant-proven=see --self-test ({len(ADVISORY_BY_DESIGN)} declared "
          "advisory strictness exceptions)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
