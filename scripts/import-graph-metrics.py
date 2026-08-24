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

THE FOUR SCALARS
================
  M1  cone[a] for each anchor a   -- modules invalidated by editing a
  M2  sum of cone[m] over all m   -- total invalidation mass of the tree
  M3  depth                       -- longest import chain (serialisation floor)
  M4  olean-weighted cone[a]      -- M1 priced by compiled artifact size

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
under the Lean module system a private-body edit need not invalidate importers
at all.  Nothing in the tree carries a `module` header today (0 of 3014), so the
bound is currently tight.  When migration starts, `--private-cone` reports the
alternative accounting and the two numbers diverge on purpose.
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
    return {
        "modules": len(graph.modules),
        "edges": sum(len(v) for v in graph.edges.values()),
        "total_bytes": sum(weights.get(m, 0) for m in graph.modules),
        "depth": depth,
        "depth_path_head": path[:8],
        "sum_cone": sum(len(c) for c in cones.values()),
        "module_headers": sum(graph.module_header.values()),
        "anchors": {
            a: {
                "cone": len(cones[a]),
                "cone_bytes": sum(weights.get(m, 0) for m in cones[a]),
            }
            for a in anchors
        },
    }


def insulation(m: dict) -> dict:
    """Growth-proof complements of the raw cone metrics.  Bigger is better; the
    ratchet fails on a DROP.  See the header for the monotonicity argument."""
    n = m.get("modules") or 0
    tb = m.get("total_bytes") or 0
    out = {"slack": n * n - m.get("sum_cone", 0)}
    for a, v in m.get("anchors", {}).items():
        out[f"outside {a}"] = n - v["cone"]
        if tb:
            out[f"bytes_outside {a}"] = tb - v["cone_bytes"]
    return out


def compare(cur: dict, base: dict) -> tuple[list[str], list[str]]:
    """Return (regressions, notes).  `depth` ratchets on increase; every cone
    metric ratchets as its growth-proof complement, on decrease."""
    regressions, notes = [], []

    c, b = cur["depth"], base.get("depth")
    if b is None:
        notes.append(f"depth: {c} (no baseline)")
    else:
        (regressions if c > b else notes).append(f"depth: {b} -> {c} ({c - b:+d})")

    cur_i, base_i = insulation(cur), insulation(base)
    raw = {"slack": (base.get("sum_cone"), cur.get("sum_cone"))}
    for a in cur.get("anchors", {}):
        raw[f"outside {a}"] = (base.get("anchors", {}).get(a, {}).get("cone"),
                               cur["anchors"][a]["cone"])
    for key, c in cur_i.items():
        b = base_i.get(key)
        if b is None:
            notes.append(f"{key}: {c} (no baseline)")
            continue
        line = f"{key}: {b} -> {c} ({c - b:+d})"
        if key in raw and raw[key][0] is not None:
            line += f"   [raw cone {raw[key][0]} -> {raw[key][1]}, "
            line += f"modules {base.get('modules')} -> {cur.get('modules')}]"
        (regressions if c < b else notes).append(line)
    return regressions, notes


def render(m: dict) -> str:
    lines = [
        f"modules={m['modules']} edges={m['edges']} "
        f"module_headers={m['module_headers']}/{m['modules']}",
        f"M3 depth={m['depth']}  tail: {' -> '.join(m['depth_path_head'][:6])}",
        f"M2 sum_cone={m['sum_cone']}",
        "M1/M4 anchors:",
    ]
    width = max((len(a) for a in m["anchors"]), default=0)
    for a, v in m["anchors"].items():
        mb = v["cone_bytes"] / 1048576
        lines.append(f"  {a:<{width}}  cone={v['cone']:>5}  cone_bytes={mb:>8.1f} MiB")
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
    # Ratchet fixtures at repo scale.
    def snap(modules, sum_cone, depth, cone, cone_bytes, total_bytes):
        return {"modules": modules, "sum_cone": sum_cone, "depth": depth,
                "total_bytes": total_bytes,
                "anchors": {"X": {"cone": cone, "cone_bytes": cone_bytes}}}

    base = snap(3000, 340_000, 69, 2850, 2_300_000_000, 2_400_000_000)
    # depth is ratcheted absolutely: one extra chain link is a regression.
    depth_rise = snap(3000, 340_000, 70, 2850, 2_300_000_000, 2_400_000_000)
    # A genuine fan-in regression: 100 modules pulled into X's cone, tree size
    # unchanged.  Must be caught.
    fanin = snap(3000, 350_000, 69, 2950, 2_380_000_000, 2_400_000_000)
    # THE REGRESSION PIN FOR #12789's OWN BUG.  Eight ordinary proof files land;
    # each joins X's cone and adds ~150 to sum_cone.  Raw counts all rise, so
    # the old integer ratchet failed here -- and did, on `main`, blocking every
    # PR in the repo.  Growth-normalised, this must be CLEAN.
    growth = snap(3008, 341_200, 69, 2858, 2_301_800_000, 2_401_800_000)
    # A real improvement plus growth: must not be reported as a regression.
    better = snap(3008, 300_000, 68, 2400, 2_000_000_000, 2_401_800_000)

    if not compare(depth_rise, base)[0]:
        failures.append("  ratchet: a depth RISE was not reported as a regression")
    if not compare(fanin, base)[0]:
        failures.append("  ratchet: a fan-in regression (cone +100 at fixed "
                        "module count) was not reported")
    if compare(growth, base)[0]:
        failures.append(
            "  ratchet: ordinary library growth (8 added modules) was reported "
            "as a regression -- this is exactly the #12789 defect that turned "
            "`main` red; the ratchet must be growth-normalised")
    if compare(better, base)[0]:
        failures.append("  ratchet: an IMPROVEMENT was reported as a regression")
    # A deletion outside the cone is the documented false-positive; pin that it
    # really does fire, so the header's `--update-baseline` advice stays true.
    deletion = snap(2999, 340_000, 69, 2850, 2_300_000_000, 2_400_000_000)
    if not compare(deletion, base)[0]:
        failures.append("  ratchet: deleting an out-of-cone module should lower "
                        "`outside` and be reported (documented false positive)")
    if compare(base, base)[0]:
        failures.append("  ratchet: an unchanged tree was reported as a regression")

    if failures:
        print("import-graph-metrics --self-test: FAIL")
        print("\n".join(failures))
        return 1
    print(f"import-graph-metrics --self-test: OK ({len(FIXTURES)} grammar "
          "fixtures, 1 hand-computed graph, 1 regression pin, 6 ratchet-direction "
          "cases)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="ratchet against baseline")
    ap.add_argument("--update-baseline", action="store_true")
    ap.add_argument("--update-weights", action="store_true",
                    help="rebuild olean-weights.json from .lake/build (needs a build)")
    ap.add_argument("--json", action="store_true")
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
