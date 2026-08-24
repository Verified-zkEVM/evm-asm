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

RATCHET, NOT THRESHOLD
======================
`--check` fails only when a number goes UP against the committed baseline.  It
always prints the delta.  There is no tolerance band because there is no noise
to absorb: same tree in, same integers out.  This is the shape
`scripts/duplication-baseline.txt` already established here.

⚠️ EVERY NEW `.lean` FILE RAISES M2.  A new module is imported by something, so
it joins that thing's cone and adds its own.  `--update-baseline` in the same PR
is the NORMAL companion to adding a file, not a workaround.  Reviewers should
look at whether M1 on the anchors moved, not at M2 in isolation.

⚠️ M4 WEIGHTS ARE A PINNED SNAPSHOT, so a module absent from the snapshot has
weight 0 until it is refreshed.  Nobody should read a flat M4 as "this new file
is free"; it means "the snapshot predates it".  Weights are also NOT comparable
across toolchain eras -- `.github/workflows/scripts/oleansize_collect.sh` makes
the same point about its own series.  Refresh deliberately with
`--update-weights` after a toolchain bump, in its own PR.

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


RATCHETED = ("depth", "sum_cone")


def compare(cur: dict, base: dict) -> tuple[list[str], list[str]]:
    regressions, notes = [], []
    for key in RATCHETED:
        c, b = cur[key], base.get(key)
        if b is None:
            notes.append(f"{key}: {c} (no baseline)")
            continue
        delta = c - b
        line = f"{key}: {b} -> {c} ({delta:+d})"
        (regressions if delta > 0 else notes).append(line)
    for a, cv in cur["anchors"].items():
        bv = base.get("anchors", {}).get(a)
        if bv is None:
            notes.append(f"anchor {a}: cone={cv['cone']} (new anchor)")
            continue
        d_cone = cv["cone"] - bv["cone"]
        d_bytes = cv["cone_bytes"] - bv["cone_bytes"]
        line = (
            f"anchor {a}: cone {bv['cone']} -> {cv['cone']} ({d_cone:+d}), "
            f"bytes {bv['cone_bytes']} -> {cv['cone_bytes']} ({d_bytes:+d})"
        )
        (regressions if d_cone > 0 else notes).append(line)
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
    base = {"depth": 10, "sum_cone": 100,
            "anchors": {"X": {"cone": 5, "cone_bytes": 500}}}
    rise = {"depth": 11, "sum_cone": 100,
            "anchors": {"X": {"cone": 5, "cone_bytes": 500}}}
    fall = {"depth": 9, "sum_cone": 90,
            "anchors": {"X": {"cone": 4, "cone_bytes": 400}}}
    cone_rise = {"depth": 10, "sum_cone": 100,
                 "anchors": {"X": {"cone": 6, "cone_bytes": 500}}}
    if not compare(rise, base)[0]:
        failures.append("  ratchet: a depth RISE was not reported as a regression")
    if not compare(cone_rise, base)[0]:
        failures.append("  ratchet: an anchor cone RISE was not reported")
    if compare(fall, base)[0]:
        failures.append("  ratchet: an IMPROVEMENT was reported as a regression")
    if compare(base, base)[0]:
        failures.append("  ratchet: an unchanged tree was reported as a regression")

    if failures:
        print("import-graph-metrics --self-test: FAIL")
        print("\n".join(failures))
        return 1
    print(f"import-graph-metrics --self-test: OK ({len(FIXTURES)} grammar "
          "fixtures, 1 hand-computed graph, 1 regression pin, 4 ratchet-direction "
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
        print(f"  RISE {r}")
    if regressions:
        print(
            "\nimport-graph-metrics: FAIL — a build-cost number went UP.\n"
            "If the rise is intended (e.g. you added a module, which always\n"
            "raises sum_cone), rerun with --update-baseline and say why in the\n"
            "PR body. Do not update the baseline to silence an anchor rise you\n"
            "have not explained: an anchor cone rising means every edit to that\n"
            "file now rebuilds more of the library than before."
        )
        return 1
    print("\nimport-graph-metrics: OK (no build-cost number increased)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
