#!/usr/bin/env python3
"""Single source of truth for parsing Lean `import` lines in this repo.

WHY THIS EXISTS: several blocking gates each re-implement import extraction with
their own anchored regex, and they disagree with each other about what an import
line may look like.  Three of them are wrong in ways that matter:

  * `scripts/check-unimported.sh`      awk `/^\\s*import\\s+EvmAsm(\\.[A-Za-z0-9_]+)*\\s*$/`
  * `scripts/check-layering.sh`        grep `^import[[:space:]]+EvmAsm\\.Codegen(\\.|[[:space:]]|$)`
  * `scripts/check-correspondence-deps.sh`  grep `-E '^import '`

All three anchor on end-of-line and none of them know about the Lean module
system.  Consequences, in ascending order of danger:

  * `public import X` is invisible -> `check-unimported.sh` reports a wired
    module as an orphan (false RED: noisy, but it fails loudly).
  * `public import EvmAsm.Codegen.X` from a verified-core file matches none of
    `check-layering.sh`'s patterns, so the script prints `(clean)` and exits 0
    while the L1 violation stands.  A soundness-boundary gate reporting a
    FALSE GREEN is strictly worse than one reporting a false red.
  * `check-correspondence-deps.sh` undercounts the closure, so `MAX_CLOSURE`
    silently stops binding.

Measured truth table — which forms each ORIGINAL pattern actually sees:

    form                          unimported  layering  corr-deps
    import X                      sees        sees      sees
    public import X               MISSES      MISSES    MISSES
    import X -- shake: keep       MISSES      sees      sees
    meta import X                 MISSES      MISSES    MISSES
    import all X                  MISSES      MISSES    sees

`public import` and `meta import` defeat all three. The trailing-comment case
defeats only `check-unimported.sh`, whose awk pattern is the one anchored with
`[[:space:]]*$`; the other two are unanchored at the end and tolerate it. (An
earlier draft of this file claimed trailing comments broke all three. They do
not — the claim is corrected here rather than quietly dropped.)

That last row is not purely forward-looking: `lake shake`, built into Lake as of
v4.33.0 (replacing Mathlib's dropped `lake exe shake`), steers itself with
`import X -- shake: keep` annotations.

WHAT COUNTS AS AN IMPORT LINE.  Lean 4.33 accepts, and this module recognises:

    import A.B                     ordinary (private, under the module system)
    public import A.B              re-exported to downstream importers
    meta import A.B                needed only at elaboration time
    public meta import A.B
    import all A.B                 imports private scope too
    public import all A.B
    module                         bare header: this file opts into the module
                                   system.  NOT an import.

...each optionally followed by a `--` line comment.  Leading whitespace is
allowed (and ignored).  A `/-` block comment on an import line is NOT handled;
no file in the tree does that, and pretending otherwise would be false comfort.

BLOCK COMMENTS ARE THE NORM, NOT AN EDGE CASE.  Essentially every file in this
tree opens with a `/- ... -/` banner naming the module, and many interleave
`/- ... -/` prose between import groups.  So `parse_text` tracks `/-` / `-/`
nesting and skips commented content rather than treating it as the end of the
import block.  (An earlier draft of this file broke on the first `/-` and
recovered only 392 of ~14000 edges — the tell was a reported DAG depth of 10
against a known 68.  `--self-test` pins that case.)

⚠️ DELIBERATE NON-GOAL: this is still a line-oriented lexer, not a Lean parser.
It does not handle an import and a block-comment delimiter sharing a line in
pathological ways (`import A /- c -/ import B`).  Nothing in the tree does that;
`scan_stop_reason` reports where scanning stopped so a future file that trips
this is visible rather than silently mis-parsed.
"""

from __future__ import annotations

import os
import re
import sys
from collections import deque
from dataclasses import dataclass

# Anchored on the line start; `all` and the modifiers are optional; a trailing
# `--` comment is permitted.  Kept as ONE regex so the accepted grammar lives in
# a single place that the self-tests can enumerate.
IMPORT_RE = re.compile(
    r"""^[ \t]*
        (?P<public>public[ \t]+)?
        (?P<meta>meta[ \t]+)?
        import[ \t]+
        (?P<all>all[ \t]+)?
        (?P<module>[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)
        [ \t]*
        (?:--.*)?$
    """,
    re.VERBOSE,
)

MODULE_HEADER_RE = re.compile(r"^[ \t]*module[ \t]*(?:--.*)?$")


@dataclass(frozen=True)
class Edge:
    """One import edge out of a module."""

    target: str
    is_public: bool
    is_meta: bool
    is_all: bool


def parse_text(text: str) -> tuple[list[Edge], bool]:
    """Return (edges, declares_module_header) for one file's source text."""
    edges, has_module_header, _ = _scan(text)
    return edges, has_module_header


def scan_stop_reason(text: str) -> str:
    """The line that ended the import block — for diagnosing a mis-parse."""
    return _scan(text)[2]


def _scan(text: str) -> tuple[list[Edge], bool, str]:
    edges: list[Edge] = []
    has_module_header = False
    comment_depth = 0
    for raw in text.splitlines():
        line = raw.rstrip()
        stripped = line.strip()

        if comment_depth > 0:
            comment_depth += stripped.count("/-") - stripped.count("-/")
            comment_depth = max(comment_depth, 0)
            continue
        if not stripped:
            continue
        if stripped.startswith("--"):
            continue
        if stripped.startswith("/-"):
            comment_depth = stripped.count("/-") - stripped.count("-/")
            comment_depth = max(comment_depth, 0)
            continue
        if MODULE_HEADER_RE.match(line):
            has_module_header = True
            continue
        m = IMPORT_RE.match(line)
        if m:
            edges.append(
                Edge(
                    target=m.group("module"),
                    is_public=bool(m.group("public")),
                    is_meta=bool(m.group("meta")),
                    is_all=bool(m.group("all")),
                )
            )
            continue
        # First real declaration outside a comment: the import block is over.
        # Lean requires imports to precede all declarations, so stopping here
        # is sound and keeps us off 4000-line bodies (and off the word
        # "import" appearing inside a docstring further down).
        return edges, has_module_header, stripped[:60]
    return edges, has_module_header, "<eof>"


def parse_file(path: str) -> tuple[list[Edge], bool]:
    with open(path, encoding="utf-8") as fh:
        return parse_text(fh.read())


def module_to_path(module: str, root: str = ".") -> str | None:
    """`EvmAsm.Foo.Bar` -> `EvmAsm/Foo/Bar.lean` if that file exists."""
    candidate = os.path.join(root, module.replace(".", os.sep) + ".lean")
    return candidate if os.path.exists(candidate) else None


def path_to_module(path: str) -> str:
    return os.path.splitext(os.path.normpath(path))[0].replace(os.sep, ".")


class ImportGraph:
    """In-tree import graph rooted at one or more top-level Lean libraries.

    `edges[m]` holds only edges whose target resolves to a file on disk, so
    Mathlib / Lean / Init / Out targets are recorded in `external` and excluded
    from every graph metric.  Rebuild cost is what we are measuring, and an
    external package is not rebuilt by our edits.
    """

    def __init__(self, tree: str, root_dirs: list[str]):
        self.tree = tree
        self.modules: set[str] = set()
        self.edges: dict[str, list[Edge]] = {}
        self.module_header: dict[str, bool] = {}
        self.external: dict[str, set[str]] = {}
        self._discover(root_dirs)

    def _discover(self, root_dirs: list[str]) -> None:
        for root_dir in root_dirs:
            base = os.path.join(self.tree, root_dir)
            if os.path.isfile(base + ".lean"):
                self._add(root_dir + ".lean")
            for dirpath, _dirnames, filenames in os.walk(base):
                for name in sorted(filenames):
                    if name.endswith(".lean"):
                        full = os.path.join(dirpath, name)
                        self._add(os.path.relpath(full, self.tree))

    def _add(self, rel: str) -> None:
        module = path_to_module(rel)
        self.modules.add(module)
        edges, has_header = parse_file(os.path.join(self.tree, rel))
        self.module_header[module] = has_header
        kept: list[Edge] = []
        ext: set[str] = set()
        for e in edges:
            if module_to_path(e.target, self.tree):
                kept.append(e)
            else:
                ext.add(e.target.split(".")[0])
        self.edges[module] = kept
        self.external[module] = ext

    def importers(self) -> dict[str, list[str]]:
        """Reverse adjacency: importers[t] lists modules that import t."""
        rev: dict[str, list[str]] = {m: [] for m in self.modules}
        for m, es in self.edges.items():
            for e in es:
                if e.target in rev:
                    rev[e.target].append(m)
        return rev

    def cone(self, module: str, rev: dict[str, list[str]] | None = None) -> set[str]:
        """Modules that must re-elaborate if `module` changes, including itself."""
        rev = rev if rev is not None else self.importers()
        seen = {module}
        queue = deque([module])
        while queue:
            cur = queue.popleft()
            for up in rev.get(cur, ()):
                if up not in seen:
                    seen.add(up)
                    queue.append(up)
        return seen

    def depth(self) -> tuple[int, list[str]]:
        """Longest chain in the import DAG, as (module count, one witness path).

        Iterative longest-path over a DAG via memoised DFS on an explicit stack
        (the graph is ~3000 nodes and 14000 edges; recursion would need a raised
        limit and would obscure a genuine cycle).
        """
        best: dict[str, int] = {}
        nxt: dict[str, str | None] = {}
        WHITE, GREY, BLACK = 0, 1, 2
        colour: dict[str, int] = {m: WHITE for m in self.modules}
        for start in sorted(self.modules):
            if colour[start] != WHITE:
                continue
            stack = [(start, False)]
            while stack:
                node, expanded = stack.pop()
                if expanded:
                    length, follow = 1, None
                    for e in self.edges.get(node, ()):
                        cand = best.get(e.target, 0) + 1
                        if cand > length:
                            length, follow = cand, e.target
                    best[node], nxt[node] = length, follow
                    colour[node] = BLACK
                    continue
                if colour[node] == BLACK:
                    continue
                if colour[node] == GREY:
                    raise ValueError(f"import cycle through {node}")
                colour[node] = GREY
                stack.append((node, True))
                for e in self.edges.get(node, ()):
                    # Back edge = a target that is GREY, i.e. still on the
                    # current DFS path.  This must be checked at PUSH time: the
                    # GREY branch on pop above cannot fire, because a GREY node
                    # is never pushed, so without this the documented cycle
                    # detection silently returned a bogus "longest chain".
                    c = colour.get(e.target, WHITE)
                    if c == GREY:
                        raise ValueError(f"import cycle through {e.target}")
                    if c == WHITE:
                        stack.append((e.target, False))
        if not best:
            return 0, []
        head = max(best, key=lambda m: (best[m], m))
        path, cur = [], head
        while cur is not None:
            path.append(cur)
            cur = nxt.get(cur)
        return best[head], path


# --------------------------------------------------------------- CLI
# Shell gates consume this. ONE invocation emits every import edge in the files
# it is given, so a gate does a single fork instead of one per file per BFS hop
# (`check-unimported.sh` spent 54 s in CI doing the latter).
#
# Output is TSV, one row per import line:
#
#     path <TAB> lineno <TAB> public <TAB> meta <TAB> all <TAB> target <TAB> raw
#
# `public`/`meta`/`all` are 0/1. `raw` is the source line, so a gate can quote it
# verbatim in a violation message. Fields never contain a tab: Lean module names
# cannot, and `raw` is the last field.

def _cli(argv: list[str]) -> int:
    import argparse

    ap = argparse.ArgumentParser(
        description="Emit Lean import edges as TSV (see module docstring)."
    )
    ap.add_argument("--edges", action="store_true", help="emit TSV edge rows")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("files", nargs="*")
    args = ap.parse_args(argv)

    if args.self_test:
        cases = [
            ("import EvmAsm.A", ("EvmAsm.A", 0, 0, 0)),
            ("public import EvmAsm.A", ("EvmAsm.A", 1, 0, 0)),
            ("meta import EvmAsm.A", ("EvmAsm.A", 0, 1, 0)),
            ("public meta import EvmAsm.A", ("EvmAsm.A", 1, 1, 0)),
            ("import all EvmAsm.A", ("EvmAsm.A", 0, 0, 1)),
            ("import EvmAsm.A -- shake: keep", ("EvmAsm.A", 0, 0, 0)),
            ("  import EvmAsm.A", ("EvmAsm.A", 0, 0, 0)),
        ]
        bad = []
        for src, want in cases:
            es, _ = parse_text(src)
            if len(es) != 1:
                bad.append(f"{src!r}: expected 1 edge, got {len(es)}")
                continue
            e = es[0]
            got = (e.target, int(e.is_public), int(e.is_meta), int(e.is_all))
            if got != want:
                bad.append(f"{src!r}: want {want}, got {got}")
        # A `module` header is not an import.
        es, hdr = parse_text("module\nimport EvmAsm.A")
        if len(es) != 1 or not hdr:
            bad.append("module header mis-parsed")
        # A leading banner must not truncate the import block.
        es, _ = parse_text("/-\n b\n-/\nimport EvmAsm.A\nimport EvmAsm.B")
        if len(es) != 2:
            bad.append(f"leading banner truncated the block: {len(es)} edges")
        # `depth()` documents that a genuine cycle surfaces as an error rather
        # than as a plausible number.  Pin it: the check used to live only on
        # the pop path, where it could never fire, so `depth()` silently
        # returned a bogus longest chain for a cyclic graph.  Both directions
        # are pinned -- an acyclic graph must NOT raise.
        import tempfile as _tf

        with _tf.TemporaryDirectory() as td:
            os.makedirs(os.path.join(td, "L"))
            open(os.path.join(td, "L", "x.lean"), "w").write("import L.y\n")
            open(os.path.join(td, "L", "y.lean"), "w").write("import L.x\n")
            try:
                ImportGraph(td, ["L"]).depth()
                bad.append("depth(): an import cycle did not raise")
            except ValueError:
                pass
            # NEGATIVE CONTROL: break the cycle, and the same graph must
            # measure cleanly rather than raising on any repeated visit.
            open(os.path.join(td, "L", "y.lean"), "w").write("/- leaf -/\n")
            got, _ = ImportGraph(td, ["L"]).depth()
            if got != 2:
                bad.append(f"depth(): acyclic x->y should be 2, got {got}")

        if bad:
            print("lean-imports --self-test: FAIL")
            for b in bad:
                print(f"  {b}")
            return 1
        print(f"lean-imports --self-test: OK ({len(cases)} forms + header + "
              "banner + cycle pin)")
        return 0

    if not args.edges:
        ap.error("nothing to do: pass --edges or --self-test")

    out = []
    for path in args.files:
        try:
            with open(path, encoding="utf-8") as fh:
                text = fh.read()
        except OSError:
            continue
        # Re-scan with line numbers. parse_text does not carry them, and a
        # violation message that cannot cite a line is not actionable.
        depth = 0
        for lineno, raw in enumerate(text.splitlines(), 1):
            stripped = raw.strip()
            if depth > 0:
                depth = max(depth + stripped.count("/-") - stripped.count("-/"), 0)
                continue
            if not stripped or stripped.startswith("--"):
                continue
            if stripped.startswith("/-"):
                depth = max(stripped.count("/-") - stripped.count("-/"), 0)
                continue
            if MODULE_HEADER_RE.match(raw):
                continue
            m = IMPORT_RE.match(raw)
            if m:
                out.append(
                    "\t".join([
                        path, str(lineno),
                        "1" if m.group("public") else "0",
                        "1" if m.group("meta") else "0",
                        "1" if m.group("all") else "0",
                        m.group("module"), raw.rstrip(),
                    ])
                )
                continue
            break
    sys.stdout.write("\n".join(out) + ("\n" if out else ""))
    return 0


if __name__ == "__main__":
    sys.exit(_cli(sys.argv[1:]))
