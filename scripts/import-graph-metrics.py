#!/usr/bin/env python3
"""Deterministic build-cost metrics over the EvmAsm import graph (GH #12788).

WHAT THIS MEASURES AND WHY IT IS NOT A TIMER
============================================
The thing contributors actually feel is "I edited one proof; how much of the
library re-elaborates?"  That is a pure function of the import graph, so it can
be computed from source in under a second, is bitwise reproducible, and needs no
build and no runner.

The two numbers we already collect cannot serve this role:

  * `lake build` progress lines.  The `(Ns)` in `✔ [n/m] Built X (Ns)` INCLUDES
    time spent waiting on dependencies, not just X's own elaboration.  Proof:
    on one full rebuild the reported times summed to 47583 s while only 16080
    CPU-seconds existed (16 workers x 1005 s).  These lines describe completion
    order, not attribution.
  * wall clock from `benchmark.yml`.  Genuinely noisy on shared runners, which
    is exactly why `docs/benchmark-workflow-design.md` declines to threshold it.

So this gate ratchets the GRAPH, and leaves seconds to the weekly benchmark.

THE SIX SCALARS
===============
  M1  cone[a] for each anchor a   -- modules invalidated by editing a
  M2  sum of cone[m] over all m   -- total invalidation mass of the tree
  M3  depth                       -- longest import chain (serialisation floor)
  M4  olean-weighted cone[a]      -- M1 priced by compiled artifact size
  M5  sum of private_cone[m]      -- M2 under the module system, where a
                                     proof-body edit to a MIGRATED module
                                     re-elaborates only that module (`--private-cone`)
  M6  redundant_edges             -- import edges already implied by a sibling
                                     import.  ADVISORY, never ratcheted.

M5 and M2 are equal while nothing is migrated and diverge, on purpose, as
`module` headers land; their gap is the invalidation mass the migration has
actually insulated.  M6 is the complementary number: it is what the migration
does NOT fix on its own, and what the later `public`/plain import narrowing pass
(`lake shake --add-public`) exists to remove.

M2 exists because M1 alone is gameable in the other direction: a change could
shave a few hundred trivial leaves off one anchor's cone while pushing work into
a hub nobody listed.  M4 exists because M1 counts MODULES, not COST -- 300
trivial `Programs/*` leaves are not worth one `SepLogic`.

M3 is the number with a precedent in this repo: splitting
`EvmAsm/Evm64/DivMod/Compose` took it from 87 s to 55 s, and
`docs/agents/tactics-deep.md` records that the win was critical-path, not CPU.

RATCHET ON INSULATION, NOT ON RAW COUNTS
========================================
`--check` fails only when a number gets WORSE against the committed baseline,
and it always prints the delta.  But the raw cone counts cannot be the
ratcheted quantity, because **the library grows**: a new `.lean` file joins the
cone of everything it transitively imports, so adding one ordinary proof file
raises M2 by ~150 and every hub anchor's M1 by +1, with no import-structure
regression whatsoever.  Ratcheting the raw integers fires on normal work and --
worse -- turns `main` red as soon as any PR merges without refreshing the
baseline.  That happened: #12789 shipped raw-count ratchets, eight ordinary
modules merged behind it, and the gate began failing every PR in the repo.

The fix is to ratchet the COMPLEMENT.  For an anchor a, define

    outside[a] = modules - cone[a]

-- the number of modules an edit to `a` does NOT invalidate.  Adding k new
modules raises `modules` by k and `cone[a]` by at most k, so `outside` NEVER
falls on growth.  It falls only when a module that already existed moves INTO
the cone, which is precisely the regression worth blocking.  No tolerance band
is needed: these are exact integers, and there is no noise to absorb.

The three ratcheted quantities, all "bigger is better":

    depth       longest import chain.  Ratcheted on INCREASE (adding leaves
                does not lengthen a chain, so this one is already growth-proof).
    slack       modules^2 - sum_cone, the tree's total non-invalidation mass.
                Growth-proof: adding k modules moves it by at least n*k > 0,
                since d(modules^2) = 2nk+k^2 while d(sum_cone) <= nk+k^2.
    outside[a]  per anchor, as above; plus bytes_outside[a] =
                total_bytes - cone_bytes[a], growth-proof for the same reason
                (a new module adds its weight to both terms, or to neither).

⚠️ A DELETION can lower `outside` legitimately (drop a module that was outside
the cone and both terms fall by one).  That is the one case where
`--update-baseline` is the right answer to a red gate; say "deleted X" in the
PR body.  Additions never need it.

⚠️ M4 WEIGHTS ARE A PINNED SNAPSHOT, so a module absent from the snapshot has
weight 0 until it is refreshed.  Nobody should read a flat M4 as "this new file
is free"; it means "the snapshot predates it".  Weights are also NOT comparable
across toolchain eras -- `.github/workflows/scripts/oleansize_collect.sh` makes
the same point about its own series.  Refresh deliberately with
`--update-weights` after a toolchain bump, in its own PR.

⚠️ RAW COUNTS ARE STILL PRINTED, and are still the right thing for a reviewer
to read in a PR body.  They are just not what the gate compares.

WHAT THIS DOES NOT CLAIM
========================
Cone size is an upper bound on what Lake re-elaborates, not an exact count:
under the Lean module system a proof-body edit need not invalidate importers at
all.  `--private-cone` reports that alternative accounting side by side.

Read the two columns as the two halves of the edit distribution, NOT as
before/after.  `private_cone` is the cost of an interface-PRESERVING edit -- a
rewritten proof body, which is roughly half of this repo's (commit, file)
touches.  An interface-CHANGING edit (a declaration added, an `@[expose]`d body
altered) still invalidates the full `cone`, and for those `cone` remains the
right number.  Neither column is a timer; see `benchmark.yml` for seconds.

`module_headers` is ratcheted as a monotone FLOOR over surviving modules (a
removed header is a regression, while deleting the whole module is neutral);
`redundant_edges` is reported but deliberately NOT ratcheted, because ordinary
growth can raise it -- see `redundant_edges` for the argument.
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "lib"))
import lean_imports as li  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ANCHORS = os.path.join(REPO, "scripts", "import-metric-anchors.txt")
BASELINE = os.path.join(REPO, "scripts", "import-metrics-baseline.json")
WEIGHTS = os.path.join(REPO, "scripts", "olean-weights.json")
ROOT_DIRS = ["EvmAsm"]


def read_anchors() -> list[str]:
    out = []
    with open(ANCHORS, encoding="utf-8") as fh:
        for line in fh:
            line = line.split("#", 1)[0].strip()
            if line:
                out.append(line)
    return out


def topo_order(graph) -> list[str]:
    """Modules in dependency-before-dependent order.  Iterative for the same
    reason `ImportGraph.depth` is: a genuine cycle must surface as an error, not
    as a RecursionError that looks like a tool bug."""
    order: list[str] = []
    WHITE, GREY, BLACK = 0, 1, 2
    colour = {m: WHITE for m in graph.modules}
    for start in sorted(graph.modules):
        if colour[start] != WHITE:
            continue
        stack = [(start, False)]
        while stack:
            node, expanded = stack.pop()
            if expanded:
                order.append(node)
                colour[node] = BLACK
                continue
            if colour[node] == BLACK:
                continue
            if colour[node] == GREY:
                raise ValueError(f"import cycle through {node}")
            colour[node] = GREY
            stack.append((node, True))
            for e in graph.edges.get(node, ()):
                # A GREY target is an ancestor on the current DFS path, i.e. a
                # back edge.  Detect it HERE, at push time: checking only on pop
                # never fires, because a GREY node is never pushed.
                c = colour.get(e.target, WHITE)
                if c == GREY:
                    raise ValueError(f"import cycle through {e.target}")
                if c == WHITE:
                    stack.append((e.target, False))
    return order


def redundant_edges(graph) -> int:
    """Import edges already IMPLIED by a sibling import of the same module.

    `import A` alongside `import B` where B transitively imports A: the edge to
    A states nothing the edge to B did not already provide.  This is the
    headroom figure for the narrowing phase -- it is what `lake shake` and the
    `public`/plain import distinction exist to remove -- and it is the one
    build-cost number that a `module` header alone does NOT improve.

    ADVISORY, NEVER RATCHETED.  Ordinary growth can raise it legitimately (a new
    file importing both a hub and one of the hub's own dependencies), so
    ratcheting it would reproduce exactly the #12789 defect the header warns
    about.  There is no growth-proof complement here either: `edges - redundant`
    can sit flat while redundancy climbs.  Report it, do not gate it.

    Reachability is carried as one big-int bitmask per module, and the
    sibling test uses prefix/suffix unions so a 738-import module costs O(k)
    mask ORs rather than O(k^2).
    """
    idx = {m: i for i, m in enumerate(sorted(graph.modules))}
    reach: dict[str, int] = {}
    for m in topo_order(graph):
        acc = 0
        for e in graph.edges.get(m, ()):
            if e.target in idx:
                acc |= (1 << idx[e.target]) | reach.get(e.target, 0)
        reach[m] = acc

    total = 0
    for m in graph.modules:
        targets = [e.target for e in graph.edges.get(m, ()) if e.target in idx]
        k = len(targets)
        if k < 2:
            continue
        pre = [0] * (k + 1)
        suf = [0] * (k + 1)
        for i, t in enumerate(targets):
            pre[i + 1] = pre[i] | reach.get(t, 0)
        for i in range(k - 1, -1, -1):
            suf[i] = suf[i + 1] | reach.get(targets[i], 0)
        for i, t in enumerate(targets):
            if ((pre[i] | suf[i + 1]) >> idx[t]) & 1:
                total += 1
    return total


def load_weights() -> dict[str, int]:
    if not os.path.exists(WEIGHTS):
        return {}
    with open(WEIGHTS, encoding="utf-8") as fh:
        return json.load(fh).get("bytes", {})


def measure(tree: str = REPO) -> dict:
    graph = li.ImportGraph(tree, ROOT_DIRS)
    rev = graph.importers()
    weights = load_weights()
    anchors = read_anchors()

    missing = [a for a in anchors if a not in graph.modules]
    if missing:
        sys.exit(
            "import-graph-metrics: anchor(s) not in the tree: "
            + ", ".join(missing)
            + "\nAn anchor naming a deleted or renamed module would silently "
            "stop measuring anything. Fix scripts/import-metric-anchors.txt."
        )

    cones = {m: graph.cone(m, rev) for m in graph.modules}
    depth, path = graph.depth()

    # Interface-invalidation accounting (see `render_private`): a migrated
    # module's proof-body edit re-elaborates only itself.
    def private(m: str) -> set[str]:
        return {m} if graph.module_header.get(m) else cones[m]

    return {
        "modules": len(graph.modules),
        "edges": sum(len(v) for v in graph.edges.values()),
        "redundant_edges": redundant_edges(graph),
        "total_bytes": sum(weights.get(m, 0) for m in graph.modules),
        "depth": depth,
        "depth_path_head": path[:8],
        "sum_cone": sum(len(c) for c in cones.values()),
        "sum_private_cone": sum(len(private(m)) for m in graph.modules),
        "module_headers": sum(graph.module_header.values()),
        # The count alone cannot distinguish a surviving module that lost its
        # header from a headered module that was deleted.  Persist the identity
        # set so compare() can restrict the floor to modules present in both
        # snapshots.
        "module_header_names": sorted(
            m for m, has_header in graph.module_header.items() if has_header),
        "module_names": sorted(graph.modules),
        "anchors": {
            a: {
                "cone": len(cones[a]),
                "cone_bytes": sum(weights.get(m, 0) for m in cones[a]),
                "private_cone": len(private(a)),
                "private_cone_bytes": sum(weights.get(m, 0) for m in private(a)),
                # Full cone member set.  Needed by the cone-migration ratchet
                # (see `compare`): to tell a deletion from a structural
                # regression we must know WHICH modules are in the cone, not
                # just how many.  Stored for the curated anchor set only.
                "cone_modules": sorted(cones[a]),
            }
            for a in anchors
        },
    }


def insulation(m: dict) -> dict:
    """Advisory complements of the raw cone metrics, plus their scale-invariant
    ratios.  Advisory ONLY -- NOT ratcheted.  Every member of this dict is a
    function of the module count `n`, so it moves whenever the tree grows or
    shrinks, even when nothing structural changed; ratcheting it would fire on
    every deletion and every module fold (see #12962).  The ratcheted signal is
    the cone-migration count in `compare`, which is neutral to such churn."""
    n = m.get("modules") or 0
    tb = m.get("total_bytes") or 0
    out = {"slack": n * n - m.get("sum_cone", 0)}
    if n:
        out["slack_ratio"] = out["slack"] / (n * n)
    for a, v in m.get("anchors", {}).items():
        out[f"outside {a}"] = n - v["cone"]
        if n:
            out[f"outside_ratio {a}"] = out[f"outside {a}"] / n
        if tb:
            out[f"bytes_outside {a}"] = tb - v["cone_bytes"]
    return out


def compare(cur: dict, base: dict) -> tuple[list[str], list[str]]:
    """Return (regressions, notes).

    `depth` ratchets on increase; `module_headers` is a floor over the
    headered modules present in BOTH snapshots; and the cone metric ratchets
    on the cone-MIGRATION count (a pre-existing module moving INTO an anchor's
    cone), which is neutral to additions and deletions.  See `cone-migration`
    below for the #12962 fix.
    """
    regressions, notes = [], []

    c, b = cur["depth"], base.get("depth")
    if b is None:
        notes.append(f"depth: {c} (no baseline)")
    else:
        (regressions if c > b else notes).append(f"depth: {b} -> {c} ({c - b:+d})")

    # `module_headers` is a floor over SURVIVING modules.  A NEW unmigrated
    # file is absent from the baseline set and cannot lower the value; a
    # DELETED headered file is absent from the current set and is neutral.  A
    # surviving module that loses its `module` header remains in the shared set
    # and is the regression this backstop must catch.
    c, b = cur.get("module_headers"), base.get("module_headers")
    if b is None or c is None:
        notes.append(f"module_headers: {c}/{cur.get('modules')} (no baseline)")
    elif (not isinstance(cur.get("module_header_names"), list)
          or not isinstance(base.get("module_header_names"), list)
          or not isinstance(cur.get("module_names"), list)
          or not isinstance(base.get("module_names"), list)):
        regressions.append(
            "module_headers: baseline/current snapshot lacks module/header name sets; "
            "regenerate the baseline before trusting this floor")
    else:
        cur_modules = set(cur.get("module_names") or ())
        base_modules = set(base.get("module_names") or ())
        shared_modules = cur_modules & base_modules
        cur_shared_headers = (set(cur["module_header_names"]) & shared_modules)
        base_shared_headers = (set(base["module_header_names"]) & shared_modules)
        line = (
            f"module_headers: {len(base_shared_headers)} -> "
            f"{len(cur_shared_headers)} "
            f"({len(cur_shared_headers) - len(base_shared_headers):+d}) "
            f"of {len(shared_modules)} surviving"
        )
        (regressions if len(cur_shared_headers) < len(base_shared_headers)
         else notes).append(line)

    # Advisory only -- see `redundant_edges` for why this must not be ratcheted.
    if cur.get("redundant_edges") is not None:
        rb = base.get("redundant_edges")
        delta = f" ({cur['redundant_edges'] - rb:+d})" if rb is not None else ""
        notes.append(
            f"redundant_edges: {cur['redundant_edges']}/{cur['edges']}{delta} "
            "[advisory, not ratcheted]"
        )

    # ---- CONE-MIGRATION ratchet (#12962). --------------------------------
    #
    # The regression this gate exists to catch is a STRUCTURAL one: a module
    # that already existed pulling into an anchor's cone, so that editing the
    # anchor re-elaborates more of the library than before.  Additions and
    # deletions are NOT regressions and must be neutral:
    #
    #   * a NEW module was not in the baseline tree, so it cannot be a
    #     "pre-existing module that moved into a cone";
    #   * a DELETED module is not in the current tree, so it is not "in a cone".
    #
    # The old ratchet instead compared `outside[a] = n - cone[a]` (and the
    # global `slack`), which are functions of the module count `n`: deleting a
    # module that sits OUTSIDE a cone lowers `n` without touching `cone[a]`, so
    # `outside[a]` fell even though nothing structural changed.  #12961 tripped
    # exactly this, and two workstreams (dead-probe removal, module folding)
    # make such shrinkage routine -- so re-baselining every time trained people
    # to re-baseline, the failure family #12907/#12938/#12960 rejected.
    #
    # A scale-invariant RATIO (`outside/n`) is not quite neutral either: an
    # out-of-cone deletion moves `outside` and `n` together by 1, so
    # `outside/n` still drifts by ~cone/n^2 per deletion -- a real, if tiny,
    # drop that the exact-integer ratchet would fire on for every 7-20-file
    # dead-probe batch.  The migration count is neutral BY CONSTRUCTION: it
    # counts only modules present at BOTH baseline and current, so any change
    # in the module set is invisible to it.
    #
    # A module is "in cone[a]" if it is in the baseline AND current cone sets.
    # The ratcheted quantity is how many such surviving modules moved INTO
    # cone[a]; it must stay at the baseline value (0 after a re-baseline).
    cur_mods = set(cur.get("module_names") or ())
    base_mods = set(base.get("module_names") or ())
    shared = cur_mods & base_mods
    weights = load_weights()
    for a in cur.get("anchors", {}):
        cur_cone = set(cur["anchors"][a].get("cone_modules") or ()) & shared
        base_cone = set(base["anchors"][a].get("cone_modules") or ()) & shared
        moved = sorted(cur_cone - base_cone)
        c_n, b_n = len(cur_cone), len(base_cone)
        if moved:
            mb = sum(weights.get(m, 0) for m in moved)
            names = ", ".join(moved[:8]) + (" ..." if len(moved) > 8 else "")
            regressions.append(
                f"cone {a}: {len(moved)} pre-existing module(s) moved INTO this "
                f"cone (shared in-cone {b_n} -> {c_n}): {names} [+{mb} bytes]"
            )
        else:
            notes.append(
                f"cone {a}: shared in-cone count {b_n} -> {c_n} ({c_n - b_n:+d})"
            )

    # ---- Advisory raw / ratio context (NOT ratcheted). ---------------------
    # These are the numbers the #12962 discussion quoted; keep printing them so
    # a reviewer can see the size-related movement alongside the migration
    # verdict.  Bigger `outside`/`slack`/ratios are better; they may move with
    # the module count in either direction without being a regression.
    cur_i, base_i = insulation(cur), insulation(base)
    raw = {"slack": (base.get("sum_cone"), cur.get("sum_cone"))}
    for a in cur.get("anchors", {}):
        raw[f"outside {a}"] = (base.get("anchors", {}).get(a, {}).get("cone"),
                               cur["anchors"][a]["cone"])
    for key in ("slack", "slack_ratio"):
        c = cur_i.get(key)
        b = base_i.get(key)
        if b is None:
            notes.append(f"{key}: {c} (no baseline)")
            continue
        notes.append(f"{key}: {b} -> {c} ({c - b:+.1f}) [advisory]")
    for a in cur.get("anchors", {}):
        for key in (f"outside {a}", f"outside_ratio {a}",
                    f"bytes_outside {a}"):
            c = cur_i.get(key)
            b = base_i.get(key)
            if b is None:
                continue
            base_v = base.get("anchors", {}).get(a, {})
            cur_v = cur["anchors"][a]
            line = f"{key}: {b:.6g} -> {c:.6g} ({c - b:+.6g}) [advisory"
            if key == f"outside {a}":
                line += (f"; raw cone {base_v.get('cone')} -> {cur_v['cone']}, "
                         f"modules {base.get('modules')} -> {cur.get('modules')}")
            line += "]"
            notes.append(line)
    return regressions, notes


def render(m: dict) -> str:
    red = m.get("redundant_edges")
    red_s = f" redundant={red} ({red / m['edges'] * 100:.1f}%)" if red else ""
    lines = [
        f"modules={m['modules']} edges={m['edges']}{red_s} "
        f"module_headers={m['module_headers']}/{m['modules']}",
        f"M3 depth={m['depth']}  tail: {' -> '.join(m['depth_path_head'][:6])}",
        f"M2 sum_cone={m['sum_cone']}",
        "M1/M4 anchors:",
    ]
    if m.get("sum_private_cone") is not None:
        lines.insert(3, f"M5 sum_private_cone={m['sum_private_cone']}"
                        f"  (insulated {m['sum_cone'] - m['sum_private_cone']})")
    width = max((len(a) for a in m["anchors"]), default=0)
    for a, v in m["anchors"].items():
        mb = v["cone_bytes"] / 1048576
        lines.append(f"  {a:<{width}}  cone={v['cone']:>5}  cone_bytes={mb:>8.1f} MiB")
    return "\n".join(lines)


def render_private(m: dict) -> str:
    """`--private-cone`: the conservative cone beside the interface-invalidation
    cone, which is what Lake actually re-elaborates for the dominant edit.

    Under the module system a public theorem's PROOF TERM is not part of the
    interface -- three different proofs of one statement produce a byte-identical
    `.olean` -- so editing a proof body in a migrated module re-elaborates that
    module and nothing else.  `cone` is therefore an upper bound that is tight
    only while a module is unmigrated; these two columns are equal today and
    diverge, on purpose, as waves land.

    This does NOT model an interface-CHANGING edit (adding a declaration,
    changing an `@[expose]`d body).  That still invalidates the full cone, and
    the `cone` column stays the right number to read for it.  Roughly half of
    this repo's (commit, file) touches are the first kind and half the second,
    so read the two columns as the two halves, not as before/after.
    """
    n, sc, sp = m["modules"], m["sum_cone"], m["sum_private_cone"]
    lines = [
        f"module_headers={m['module_headers']}/{n} migrated",
        f"sum_cone={sc}  sum_private_cone={sp}  "
        f"insulated={sc - sp} ({(sc - sp) / sc * 100:.1f}% of invalidation mass)",
        "",
        f"  {'anchor':<44} {'cone':>6} {'private':>8}  migrated",
    ]
    for a, v in m["anchors"].items():
        pc = v.get("private_cone", v["cone"])
        mig = "yes" if pc != v["cone"] or v["cone"] == 1 else "no"
        lines.append(f"  {a:<44} {v['cone']:>6} {pc:>8}  {mig}")
    return "\n".join(lines)


# ---------------------------------------------------------------- self-test

FIXTURES = [
    ("import A.B", [("A.B", False, False, False)], False),
    ("public import A.B", [("A.B", True, False, False)], False),
    ("meta import A.B", [("A.B", False, True, False)], False),
    ("public meta import A.B", [("A.B", True, True, False)], False),
    ("import all A.B", [("A.B", False, False, True)], False),
    ("public import all A.B", [("A.B", True, False, True)], False),
    ("import A.B -- shake: keep", [("A.B", False, False, False)], False),
    ("  import A.B", [("A.B", False, False, False)], False),
    ("module\nimport A.B", [("A.B", False, False, False)], True),
    ("module -- shake: keep-all\nimport A.B", [("A.B", False, False, False)], True),
    ("/-\n banner\n-/\nimport A.B", [("A.B", False, False, False)], False),
    ("/- one -/\nimport A.B\n/- two -/\nimport C.D",
     [("A.B", False, False, False), ("C.D", False, False, False)], False),
    ("import A.B\n\ntheorem t : True := trivial\nimport NOPE",
     [("A.B", False, False, False)], False),
    ("-- lead\nimport A.B", [("A.B", False, False, False)], False),
]


def self_test() -> int:
    failures = []
    for src, want_edges, want_header in FIXTURES:
        edges, header = li.parse_text(src)
        got = [(e.target, e.is_public, e.is_meta, e.is_all) for e in edges]
        if got != want_edges or header != want_header:
            failures.append(
                f"  {src!r}\n    want {want_edges} header={want_header}\n"
                f"    got  {got} header={header}"
            )

    # A hand-computed graph. b and c both import a; d imports b.
    #   cone(a)={a,b,c,d}=4  cone(b)={b,d}=2  cone(c)={c}=1  cone(d)={d}=1
    #   sum=8   depth: d->b->a = 3
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, "L"))
        open(os.path.join(td, "L", "a.lean"), "w").write("/- x -/\n")
        open(os.path.join(td, "L", "b.lean"), "w").write("import L.a\n")
        open(os.path.join(td, "L", "c.lean"), "w").write("public import L.a\n")
        open(os.path.join(td, "L", "d.lean"), "w").write("import L.b -- keep\n")
        g = li.ImportGraph(td, ["L"])
        rev = g.importers()
        want = {"L.a": 4, "L.b": 2, "L.c": 1, "L.d": 1}
        for mod, n in want.items():
            got = len(g.cone(mod, rev))
            if got != n:
                failures.append(f"  cone({mod}): want {n}, got {got}")
        total = sum(len(g.cone(m, rev)) for m in g.modules)
        if total != 8:
            failures.append(f"  sum_cone: want 8, got {total}")
        d, _ = g.depth()
        if d != 3:
            failures.append(f"  depth: want 3, got {d}")

    # Regression pin: a leading `/-` banner must not truncate the import block.
    # An earlier draft broke here and recovered 392 of 14219 real edges.
    edges, _ = li.parse_text("/-\n  Mod\n-/\n\nimport A\nimport B\nimport C\n")
    if len(edges) != 3:
        failures.append(f"  banner regression: want 3 edges, got {len(edges)}")

    # Ratchet direction, both ways. A gate that cannot fail proves nothing, and
    # one that fails on an IMPROVEMENT would block exactly the PRs we want.
    # Ratchet fixtures at repo scale.  The cone fixtures carry the full module
    # set so the cone-migration ratchet can tell a deletion from a structural
    # change; `n_mods` names the module set of size `modules`.
    def snap(modules, sum_cone, depth, cone, cone_bytes, total_bytes,
             n_mods=None, cone_mods=None):
        if n_mods is None:
            n_mods = [f"m{i}" for i in range(modules)]
        if cone_mods is None:
            cone_mods = n_mods[:cone]
        return {"modules": modules, "sum_cone": sum_cone, "depth": depth,
                "total_bytes": total_bytes, "module_names": n_mods,
                "anchors": {"X": {"cone": len(cone_mods),
                                  "cone_bytes": cone_bytes,
                                  "cone_modules": sorted(cone_mods)}}}

    base = snap(3000, 340_000, 69, 2850, 2_300_000_000, 2_400_000_000)
    # depth is ratcheted absolutely: one extra chain link is a regression.
    depth_rise = snap(3000, 340_000, 70, 2850, 2_300_000_000, 2_400_000_000)
    # A genuine fan-in regression: 100 PRE-EXISTING modules pulled into X's
    # cone, tree size unchanged.  Must be caught (positive control).
    fanin = snap(3000, 350_000, 69, 2950, 2_380_000_000, 2_400_000_000,
                 cone_mods=[f"m{i}" for i in range(2950)])
    # THE REGRESSION PIN FOR #12789's OWN BUG.  Eight ordinary proof files land,
    # each joining X's cone.  They are NEW modules (absent from the baseline), so
    # the cone-migration ratchet -- which counts only PRE-EXISTING modules --
    # must be CLEAN here.  (The old integer ratchet failed on exactly this
    # growth, turning `main` red and blocking every PR.)
    growth = snap(3008, 341_200, 69, 2858, 2_301_800_000, 2_401_800_000,
                  n_mods=[f"m{i}" for i in range(3008)],
                  cone_mods=[f"m{i}" for i in range(2850)] +
                           [f"m{i}" for i in range(3000, 3008)])
    # A real improvement plus growth: must not be reported as a regression.
    better = snap(3008, 300_000, 68, 2400, 2_000_000_000, 2_401_800_000,
                  n_mods=[f"m{i}" for i in range(3008)],
                  cone_mods=[f"m{i}" for i in range(2400)])

    if not compare(depth_rise, base)[0]:
        failures.append("  ratchet: a depth RISE was not reported as a regression")
    if not compare(fanin, base)[0]:
        failures.append("  ratchet: a fan-in regression (100 pre-existing "
                        "modules pulled into X's cone) was not reported")
    if compare(growth, base)[0]:
        failures.append(
            "  ratchet: ordinary library growth (8 NEW modules joined X's cone) "
            "was reported as a regression -- this is exactly the #12789 defect "
            "that turned `main` red; the cone-migration ratchet must ignore "
            "new modules")
    if compare(better, base)[0]:
        failures.append("  ratchet: an IMPROVEMENT was reported as a regression")

    # ---- #12962: the cone-migration ratchet must be NEUTRAL to deletions. ----
    # Deleting a module that sits OUTSIDE X's cone used to lower `outside`
    # (n - cone) and fire -- the bug that tripped #12961 and this PR fixes.
    # A deleted module is absent from the current tree, so it is not "in a
    # cone"; the migration count over surviving modules must stay 0.
    del_out = snap(2999, 340_000, 69, 2850, 2_300_000_000, 2_400_000_000,
                   n_mods=[f"m{i}" for i in range(2999)])  # drop m2999 (outside cone)
    if compare(del_out, base)[0]:
        failures.append("  #12962: deleting an OUT-OF-CONE module was reported "
                        "as a regression -- this is the exact defect the "
                        "migration ratchet must not fire on")
    # Deleting a module that sits INSIDE X's cone is also neutral: it leaves the
    # surviving in-cone set unchanged, so nothing "moved into" the cone.
    del_in = snap(2999, 339_000, 69, 2849, 2_299_000_000, 2_400_000_000,
                  n_mods=[f"m{i}" for i in range(1, 3000)],
                  cone_mods=[f"m{i}" for i in range(1, 2850)])  # drop m0 (in cone)
    if compare(del_in, base)[0]:
        failures.append("  #12962: deleting an IN-CONE module was reported as a "
                        "regression")
    if compare(base, base)[0]:
        failures.append("  ratchet: an unchanged tree was reported as a regression")

    # ---------------- redundant edges, with a negative control -------------
    # A gate number that only ever fires is as useless as one that never does,
    # so pin BOTH directions on the same hand-built tree.
    #   a <- b <- e   and   a <- e
    # e's edge to `a` is implied by its edge to `b`; nothing else is implied.
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, "L"))
        open(os.path.join(td, "L", "a.lean"), "w").write("/- x -/\n")
        open(os.path.join(td, "L", "b.lean"), "w").write("import L.a\n")
        # NEGATIVE CONTROL: e imports only b, so no edge is implied by a sibling.
        open(os.path.join(td, "L", "e.lean"), "w").write("import L.b\n")
        clean = redundant_edges(li.ImportGraph(td, ["L"]))
        if clean != 0:
            failures.append(
                f"  redundant_edges: a tree with NO implied edge reported "
                f"{clean}; the measure fires on something it should not")
        # Now add the implied edge and nothing else.  Exactly one appears.
        open(os.path.join(td, "L", "e.lean"), "w").write("import L.a\nimport L.b\n")
        dirty = redundant_edges(li.ImportGraph(td, ["L"]))
        if dirty != 1:
            failures.append(
                f"  redundant_edges: `import L.a` alongside `import L.b` (b "
                f"imports a) should count 1 implied edge, got {dirty}")
        # Depth-2 implication: the sibling reaches the target transitively, not
        # directly.  A one-hop-only implementation passes the case above and
        # fails this one.
        open(os.path.join(td, "L", "c.lean"), "w").write("import L.b\n")
        open(os.path.join(td, "L", "e.lean"), "w").write("import L.a\nimport L.c\n")
        deep = redundant_edges(li.ImportGraph(td, ["L"]))
        if deep != 1:
            failures.append(
                f"  redundant_edges: a TRANSITIVELY implied edge (e->a via "
                f"e->c->b->a) should count 1, got {deep}")

    # A cycle must raise, not loop forever or return a plausible number.
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, "L"))
        open(os.path.join(td, "L", "x.lean"), "w").write("import L.y\n")
        open(os.path.join(td, "L", "y.lean"), "w").write("import L.x\n")
        try:
            topo_order(li.ImportGraph(td, ["L"]))
            failures.append("  topo_order: an import cycle did not raise")
        except ValueError:
            pass

    # ---------------- module_headers floor, all required directions --------
    def hdr(modules, headers, header_names=None, module_names=None,
            cone_names=None):
        names = ([f"m{i}" for i in range(modules)]
                 if module_names is None else module_names)
        if header_names is None:
            header_names = names[:headers]
        if cone_names is None:
            cone_names = names[:2850]
        return {"modules": modules, "module_headers": headers, "sum_cone": 340_000,
                "depth": 69, "total_bytes": 2_400_000_000,
                "module_names": names, "module_header_names": header_names,
                "anchors": {"X": {"cone": len(cone_names), "cone_bytes": 2_300_000_000,
                                  "cone_modules": cone_names}}}

    hbase = hdr(3000, 1500)
    # A header REMOVED from a SURVIVING module: it silently rejoins the
    # invalidate-everything regime.  This is the whole point of the ratchet.
    if not compare(hdr(3000, 1499), hbase)[0]:
        failures.append("  module_headers: a REMOVED header was not reported")
    # A headered module DELETED altogether: it is absent from the shared set,
    # so the surviving-module floor must remain neutral.
    del_headered_modules = ([f"m{i}" for i in range(1499)] +
                            [f"m{i}" for i in range(1500, 3000)])
    del_headered_names = [f"m{i}" for i in range(1499)]
    del_headered_cone = [f"m{i}" for i in range(1499)] + [
        f"m{i}" for i in range(1500, 2850)]
    if compare(hdr(2999, 1499, del_headered_names,
                  del_headered_modules, del_headered_cone), hbase)[0]:
        failures.append("  module_headers: deleting a HEADERED module was "
                        "reported as a regression")
    # A wave lands.  Must be clean.
    if compare(hdr(3000, 1750), hbase)[0]:
        failures.append("  module_headers: a migration wave was reported as a "
                        "regression")
    # POSITIVE PIN THAT ORDINARY GROWTH IS SILENT: 8 new UNMIGRATED files land.
    # The count stays flat while `modules` rises -- the exact shape that broke
    # the raw-cone ratchet in #12789.  A percentage-based floor would fire here.
    if compare(hdr(3008, 1500), hbase)[0]:
        failures.append("  module_headers: 8 new unmigrated modules (count flat,"
                        " `modules` up) fired the floor -- this is the #12789"
                        " defect shape; the floor must be on the COUNT, never"
                        " on a ratio")
    if compare(hbase, hbase)[0]:
        failures.append("  module_headers: an unchanged tree was reported")
    legacy_hbase = dict(hbase)
    legacy_hbase.pop("module_header_names")
    if not compare(hbase, legacy_hbase)[0]:
        failures.append("  module_headers: a baseline without header identity "
                        "was accepted")

    # ---------------- private-cone accounting ------------------------------
    # Equal to `cone` while unmigrated; collapses to 1 once the header lands.
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, "L"))
        open(os.path.join(td, "L", "a.lean"), "w").write("/- x -/\n")
        open(os.path.join(td, "L", "b.lean"), "w").write("import L.a\n")
        open(os.path.join(td, "L", "c.lean"), "w").write("import L.b\n")
        g = li.ImportGraph(td, ["L"])
        rev = g.importers()
        plain = sum(len({m} if g.module_header.get(m) else g.cone(m, rev))
                    for m in g.modules)
        if plain != 6:  # cone(a)=3, cone(b)=2, cone(c)=1
            failures.append(f"  private cone: unmigrated tree should equal "
                            f"sum_cone (6), got {plain}")
        open(os.path.join(td, "L", "a.lean"), "w").write("module\n")
        g = li.ImportGraph(td, ["L"])
        rev = g.importers()
        migrated = sum(len({m} if g.module_header.get(m) else g.cone(m, rev))
                       for m in g.modules)
        if migrated != 4:  # a collapses 3 -> 1
            failures.append(f"  private cone: migrating the root should drop "
                            f"sum_private_cone from 6 to 4, got {migrated}")

    if failures:
        print("import-graph-metrics --self-test: FAIL")
        print("\n".join(failures))
        return 1
    print(f"import-graph-metrics --self-test: OK ({len(FIXTURES)} grammar "
          "fixtures, 1 hand-computed graph, 1 regression pin, 6 ratchet-direction "
          "cases, 3 redundant-edge cases + 1 cycle pin, 6 module_headers-floor "
          "cases, 2 private-cone cases)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="ratchet against baseline")
    ap.add_argument("--update-baseline", action="store_true")
    ap.add_argument("--update-weights", action="store_true",
                    help="rebuild olean-weights.json from .lake/build (needs a build)")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--private-cone", action="store_true",
                    help="conservative cone beside the interface-invalidation "
                         "cone (the migration progress meter)")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    if args.update_weights:
        libdir = os.path.join(REPO, ".lake", "build", "lib", "lean")
        if not os.path.isdir(libdir):
            sys.exit("--update-weights needs .lake/build/lib/lean (run `lake build`)")
        sizes = {}
        for dirpath, _d, files in os.walk(libdir):
            for f in files:
                if f.endswith(".olean"):
                    full = os.path.join(dirpath, f)
                    mod = li.path_to_module(os.path.relpath(full, libdir))
                    sizes[mod] = os.path.getsize(full)
        toolchain = open(os.path.join(REPO, "lean-toolchain")).read().strip()
        with open(WEIGHTS, "w", encoding="utf-8") as fh:
            json.dump({"toolchain": toolchain, "count": len(sizes),
                       "bytes": dict(sorted(sizes.items()))}, fh, indent=1)
            fh.write("\n")
        print(f"wrote {WEIGHTS}: {len(sizes)} modules, toolchain {toolchain}")
        return 0

    cur = measure()

    if args.private_cone:
        print(render_private(cur))
        return 0

    if args.json:
        print(json.dumps(cur, indent=2))
        return 0

    if args.update_baseline:
        with open(BASELINE, "w", encoding="utf-8") as fh:
            json.dump(cur, fh, indent=1)
            fh.write("\n")
        print(f"wrote {BASELINE}")
        print(render(cur))
        return 0

    print(render(cur))

    if not args.check:
        return 0

    if not os.path.exists(BASELINE):
        sys.exit(f"import-graph-metrics: no baseline at {BASELINE}")
    with open(BASELINE, encoding="utf-8") as fh:
        base = json.load(fh)
    regressions, notes = compare(cur, base)
    print()
    for n in notes:
        print(f"  ok   {n}")
    for r in regressions:
        print(f"  WORSE {r}")
    if regressions:
        print(
            "\nimport-graph-metrics: FAIL — build-cost insulation DROPPED.\n"
            "`outside`/`slack` falling means a module that ALREADY EXISTED\n"
            "moved into a cone: editing that anchor now rebuilds more of the\n"
            "library than before. Adding new modules cannot cause this (see\n"
            "the monotonicity argument in the header), so the usual cause is a\n"
            "new import edge. Find it with:\n"
            "  git diff <base> -- '*.lean' | grep '^[+-].*^import'\n"
            "If the new edge is intended, rerun with --update-baseline and name\n"
            "the edge and the modules it pulled in, in the PR body. Deleting an\n"
            "out-of-cone module also lowers `outside` legitimately; say so."
        )
        return 1
    print("\nimport-graph-metrics: OK (no build-cost insulation dropped)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
