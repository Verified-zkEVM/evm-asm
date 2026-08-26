#!/usr/bin/env python3
"""Mechanical conversion of EvmAsm sources to the Lean 4.33 module system.

WHAT THIS EMITS AND WHY THAT EXACT SHAPE
========================================
Per file, immediately after the existing banner:

    module

    public import <every original dep, in its original position>
    meta import <every original dep>          -- iff this file has a meta trigger

    @[expose] public section

This is the shape Mathlib itself uses (see `Mathlib/Logic/Basic.lean` for the
plain case and `Mathlib/Order/Interval/Lex.lean` for the dual public+meta case,
which carries `meta import Mathlib.Order.Interval.Basic` alongside the public
import of the same module, for `#eval`).  It is deliberately the DULLEST correct
transform:

  * `public import` for everything preserves today's re-export behaviour
    exactly.  Deciding which imports could be demoted to plain `import` is the
    narrowing pass, and it is NOT this script's job -- `lake shake
    --add-public` computes it later, against a tree that already builds.

  * `@[expose] public section` preserves today's DEFINITIONAL visibility.  This
    tree relies on it heavily: ~1200 `@[irreducible]`, ~8400 `unfold`, and
    ~13000 `simp only [<def>]` sites all see through definitions today.
    Dropping `@[expose]` is a real semantic change that breaks proofs, so it is
    a separate, later, measured pass.  The build-time win does NOT depend on it:
    a public theorem's PROOF TERM is not part of the interface either way,
    which is what makes proof-body edits stop invalidating importers.

THE MIGRATED SET MUST BE DOWNWARD-CLOSED
========================================
A `module` file cannot import a non-`module` file -- the same error for plain
`import`, `public import`, `meta import`, and `import all`.  The reverse is
fine.  So migration runs bottom-up, and a wave must contain every in-tree
dependency of its members.  `--check-closed` verifies that before you build.

WHY META IMPORTS ARE EMITTED BLANKET
====================================
Two opposing constraints, both measured:

  * `public meta import X` re-exports X's declarations AS META, which breaks any
    ordinary downstream consumer ("may not access declaration `step` imported as
    `meta`").  So the public import must stay plain-public.
  * A `meta` definition in the file cannot see X AT ALL unless X is also
    imported at meta level ("Invalid `meta` definition, `instBEqReg` is not
    accessible here").

Emitting both lines satisfies both.  Which of a file's imports the meta code
actually needs is not decidable by a regex, so every import is mirrored when the
file has any meta trigger.  Over-approximating is SAFE (a plain `meta import` is
local-only and re-exports nothing) and it is exactly what `lake shake` prunes
later, so no `shake: keep` annotation is attached.

Under-detecting a meta trigger, by contrast, breaks the build.  So the trigger
list is deliberately generous.

WHAT THIS SCRIPT WILL NOT DO
============================
Files that MIX ordinary definitions with metaprogramming cannot be fixed by any
whole-file transform: tagging the file `meta` makes its data structures meta
too, and `private def ... : MetaM` helpers stop being visible at an `elab` site
in the same file.  Those need per-DECLARATION `meta` and must be hand-fixed.
This script converts them like any other file and lets the build point at them;
that is the intended workflow, not a gap.

IDEMPOTENCE IS A REQUIREMENT, NOT A NICETY
==========================================
`main` moves fast enough that rebasing a wave is worse than regenerating it.  A
file that already carries a `module` header is left untouched, so the conflict
resolution for a wave PR is "re-run the script", not "resolve 230 conflicts".
"""

from __future__ import annotations

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "lib"))
import lean_imports as li  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT_DIRS = ["EvmAsm"]
DEFERRED = os.path.join(REPO, "scripts", "module-system-deferred.txt")

# Anything here means the file needs its imports mirrored at meta level.  Being
# generous is free (an unused `meta import` re-exports nothing and shake prunes
# it); being stingy breaks the build.  `#guard`/`#eval` are the obvious ones and
# by far the most common here, but they are nowhere near the whole list.
META_TRIGGERS = [
    r"#guard\b", r"#eval\b", r"#print\b", r"#reduce\b", r"#check\b",
    r"#guard_msgs\b",
    r"^\s*initialize\b", r"^\s*builtin_initialize\b",
    r"^\s*open\s+Lean\b", r"\bLean\.Meta\b", r"\bLean\.Elab\b",
    r"\bMetaM\b", r"\bTacticM\b", r"\bCommandElabM\b", r"\bTermElabM\b",
    r"\bCoreM\b", r"\bSimpM\b",
    r"^\s*(scoped\s+|local\s+)?(syntax|macro|macro_rules|elab|elab_rules)\b",
    r"\bregister_simp_attr\b", r"\bregisterSimpAttr\b",
    r"\brun_cmd\b", r"\bQq\b", r"\bmkSimpAttr\b",
    # Applying a user-defined attribute needs it at META level, exactly like a
    # meta definition does. Missed at wave 10 by
    # `EvmAsm/Rv64/RLP/ValidatingExactArity.lean`, which carries
    # `attribute [rv64_wp_cert] ...` and imported its declaring module
    # (`Rv64.Tactics.WPAttr`) publicly but not at meta level:
    #     error: Unknown attribute `[rv64_wp_cert]`
    # The symptom names the attribute, not the import, so it does not read as a
    # missing `meta import` at all.
    r"^\s*attribute\s*\[",
]
META_RE = re.compile("|".join(META_TRIGGERS), re.MULTILINE)

# `initialize ... registerSimpAttr` additionally needs the attribute module
# itself available at meta level; it is usually NOT among the file's imports.
SIMP_ATTR_RE = re.compile(r"register_simp_attr|registerSimpAttr")
SIMP_ATTR_MODULE = "Lean.Meta.Tactic.Simp.Attr"

IMPORT_RE = re.compile(
    r"^(?P<indent>\s*)(?P<kw>(?:public\s+)?(?:meta\s+)?import(?:\s+all)?)\s+"
    r"(?P<target>[A-Za-z_][A-Za-z0-9_.₁-₉']*)\s*(?P<tail>--.*)?$"
)


def _comment_delta(line: str) -> int:
    """Net block-comment nesting change contributed by one line.

    Scans two characters at a time so OVERLAPPING delimiters cannot both count.
    `str.count` gets this wrong on a real banner in this tree,
    `EvmAsm/Codegen/Programs/AmsterdamBlobGasPriceBody2Spec.lean`, which opens

        /-/

    Here the `/-` at offset 0 and the `-/` at offset 1 SHARE the `-`. Counting
    both yields a net depth of 0, so an open banner reads as closed, every
    subsequent `import` looks like it sits after the header, and the converter
    emits `@[expose] public section` ABOVE the file's real imports -- which is
    a hard build error, not a cosmetic one.

    Lean tokenises left to right: `/-/` is `/-` followed by `/`, i.e. one
    opener and no closer. This does the same.
    """
    depth = 0
    i = 0
    n = len(line)
    while i < n - 1:
        pair = line[i:i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif pair == "-/":
            depth -= 1
            i += 2
        else:
            i += 1
    return depth


def needs_meta(text: str) -> bool:
    return META_RE.search(text) is not None


def classify_lines(lines: list[str]) -> tuple[list[int], int]:
    """Return (indices of import lines, index where `module` must go).

    The `module` keyword must precede the first import.  With no imports at all
    it goes after the leading comment block, which is why the block-comment
    depth is tracked here rather than assumed to be one banner.

    Block comments are the norm in this tree, not an edge case: essentially
    every file opens with a `/- ... -/` banner and many interleave `/- ... -/`
    prose BETWEEN import groups, so this must not stop at the first one.
    """
    imports: list[int] = []
    depth = 0
    first_code = None
    for i, raw in enumerate(lines):
        line = raw.strip()
        if depth:
            depth += _comment_delta(line)
            continue
        if line.startswith("/-"):
            depth += _comment_delta(line)
            continue
        if not line or line.startswith("--"):
            continue
        if IMPORT_RE.match(raw):
            imports.append(i)
            continue
        if first_code is None:
            first_code = i
        # Imports may not follow a non-import command, so once real code starts
        # the import block is over.  (`parse_text` stops here for the same
        # reason; a later `import` line is not one.)
        break
    module_at = imports[0] if imports else (first_code if first_code is not None else len(lines))
    return imports, module_at


# `open private A B from M`, with the names free to wrap across lines.
OPEN_PRIVATE_RE = re.compile(
    r"^[ \t]*open private (?:[A-Za-z0-9_.'?!]+|\s)+?\s+from\s+([A-Za-z0-9_.'?!]+)\s*$",
    re.MULTILINE)


def open_private_sources(text: str) -> list[str]:
    """Modules this file reads the private half of, in first-seen order."""
    seen: list[str] = []
    for m in OPEN_PRIVATE_RE.findall(text):
        if m not in seen:
            seen.append(m)
    return seen


def convert(text: str) -> tuple[str, dict]:
    """Return (new_text, stats).  Idempotent: an already-migrated file is
    returned byte-identical, so re-running the script IS the merge strategy."""
    lines = text.splitlines()
    _edges, has_header = li.parse_text(text)
    if has_header:
        return text, {"skipped": "already migrated"}

    imports, module_at = classify_lines(lines)
    meta = needs_meta(text)

    targets: list[str] = []
    out: list[str] = []
    # The insertion point is tracked WHILE emitting, never computed from the
    # original line numbers: once one source line emits more than one output
    # line every precomputed offset is wrong, and the classic symptom is
    # `@[expose] public section` landing INSIDE the import block
    # ("invalid 'import' command, it must be used in the beginning of the file").
    last_import_out = None
    module_out = None

    for i, raw in enumerate(lines):
        if i == module_at:
            module_out = len(out)
            out.append("module")
            out.append("")
        m = IMPORT_RE.match(raw)
        if m and i in imports:
            kw = re.sub(r"\s+", " ", m.group("kw")).strip()
            if not kw.startswith("public"):
                kw = "public " + kw
            tail = (" " + m.group("tail")) if m.group("tail") else ""
            out.append(f"{kw} {m.group('target')}{tail}")
            targets.append(m.group("target"))
            last_import_out = len(out) - 1
            continue
        out.append(raw)

    extra: list[str] = []
    if meta:
        for t in targets:
            extra.append(f"meta import {t}")
        if SIMP_ATTR_RE.search(text) and SIMP_ATTR_MODULE not in targets:
            # `initialize registerSimpAttr` cannot see the attribute machinery
            # through an ordinary import.
            extra.append(f"public meta import {SIMP_ATTR_MODULE}")
    # `open private f from M` reaches M's PRIVATE half, which lives in a separate
    # `.olean.private` that a plain or `public import` does not carry.  Without
    # `import all M` the command fails with a mangled name that looks like a
    # missing declaration rather than a missing import form:
    #
    #   Unknown constant `_private.….BlocksRlp.0.….rlpTestHeader`
    #
    # M is necessarily already a dependency (you cannot open private from a
    # module you do not import), so this adds an import FORM, not an edge to
    # anywhere new.  Emitting it here rather than fixing it per build keeps the
    # failure out of waves entirely -- it is invisible until the *consumer* is
    # migrated, which is one wave later than the module whose privates it reads.
    indirect_private: list[str] = []
    for t in open_private_sources(text):
        if t in targets:
            extra.append(f"import all {t}")
        else:
            # M reaches this file only TRANSITIVELY.  `import all M` would work
            # but adds a direct edge that was not there before, so the converter
            # will not invent it silently -- it is reported for a human instead.
            indirect_private.append(t)
    if last_import_out is not None:
        extra.append("")
    # With no imports the converter has already emitted a blank after `module`,
    # so a second one would sit OUTSIDE the discounted span and leave the file
    # one line longer for the size gate.  See `lean_imports.header_lines`.
    extra.append("@[expose] public section")

    if module_out is None:
        # `module_at` can sit at EOF: a file that is nothing but a banner has no
        # imports AND no code, so the loop never reaches the insertion index.
        # (Real case in this tree -- umbrella and placeholder files.)
        module_out = len(out)
        out.append("module")
        out.append("")

    if last_import_out is None:
        # No imports: the section goes straight after `module`.  The anchor is
        # the tracked OUTPUT index, never a search for the string "module" --
        # a file can legitimately contain that word on another line.
        # +2, not +1: the blank line already emitted after `module` must stay
        # INSIDE the discounted span, or the file is one line longer for the
        # size gate.  See `lean_imports.header_lines`.
        anchor = module_out + 2
        out[anchor:anchor] = extra
    else:
        out[last_import_out + 1:last_import_out + 1] = extra

    new = "\n".join(out)
    # Preserve the original's trailing-newline habit -- except for an EMPTY
    # input, which has none and would otherwise yield a file whose last line has
    # no terminator, i.e. one fewer line by `wc -l` than it has content.
    # `EvmAsm/EL/Conformance/All.lean` is a real 0-line placeholder in this tree.
    if text.endswith("\n") or not text.strip():
        new += "\n"
    return new, {
        "imports": len(targets),
        "meta": meta,
        "simp_attr": bool(meta and SIMP_ATTR_RE.search(text)),
        "indirect_private": indirect_private,
    }


def verify(before: str, after: str) -> list[str]:
    """Cross-check the transform with the repo's blessed import parser.

    Cheap and worth it: the one thing a header rewrite must never do is change
    which modules a file depends on, and `lean_imports` is the parser every gate
    in this repo already trusts to answer that.
    """
    problems = []
    b_edges, _ = li.parse_text(before)
    a_edges, a_hdr = li.parse_text(after)
    if not a_hdr:
        problems.append("no `module` header in the output")
    b_targets = [e.target for e in b_edges]
    # `registerSimpAttr` needs the attribute module at meta level and it is
    # added deliberately, so it is the one permitted addition to the public set.
    a_public = [e.target for e in a_edges
                if e.is_public and e.target != SIMP_ATTR_MODULE]
    if a_public != b_targets:
        problems.append(f"public imports {a_public} != original imports {b_targets}")
    # Meta imports mirror the public ones, so they must never introduce a
    # dependency the file did not already have (bar the simp-attr module, which
    # is added deliberately).
    stray = ({e.target for e in a_edges if e.is_meta}
             - set(b_targets) - {SIMP_ATTR_MODULE})
    if stray:
        problems.append(f"meta imports introduced new dependencies: {sorted(stray)}")
    if "@[expose] public section" not in after:
        problems.append("no `@[expose] public section` in the output")
        return problems

    # The section must come AFTER every import, or the file does not parse
    # ("invalid 'import' command, it must be used in the beginning of the file").
    #
    # This must be BLOCK-COMMENT AWARE.  A raw regex over the text reports four
    # false positives in this tree, because several banners contain prose that
    # begins a line with the word "import" -- e.g. ArenaCapacities.lean's
    # "import (the dependency runs the other way)".  Track comment depth the
    # same way `classify_lines` does rather than pattern-matching the source.
    lines = after.splitlines()
    depth = 0
    last_import = -1
    section = None
    for i, raw in enumerate(lines):
        line = raw.strip()
        if depth:
            depth += _comment_delta(line)
            continue
        if line.startswith("/-"):
            depth += _comment_delta(line)
            continue
        if line.startswith("@[expose] public section") and section is None:
            section = i
            continue
        if IMPORT_RE.match(raw):
            last_import = i
    if section is None:
        problems.append("`@[expose] public section` is inside a comment")
    elif last_import > section:
        problems.append(
            f"an import line (line {last_import + 1}) follows "
            f"`@[expose] public section` (line {section + 1})")
    return problems


# ------------------------------------------------------------------ closure

def check_closed(modules: set[str]) -> list[str]:
    """A wave must contain every in-tree dependency of its members, because a
    `module` file cannot import a non-`module` file."""
    graph = li.ImportGraph(REPO, ROOT_DIRS)
    already = {m for m in graph.modules if graph.module_header.get(m)}
    blocked, _why = blocked_modules(graph)
    bad = []
    for m in sorted(modules):
        if m in blocked:
            bad.append(f"{m} is BLOCKED and must not be in a wave "
                       f"({_why.get(m, 'unmigratable dependency')})")
            continue
        for e in graph.edges.get(m, ()):
            t = e.target
            if t in graph.modules and t not in modules and t not in already:
                bad.append(f"{m} imports {t}, which is neither in this wave nor migrated")
    return bad


def _package_is_migrated(pkg: str) -> bool | None:
    """Does external package `pkg` use the module system?  None if not found.

    Detected rather than hardcoded, so this does not silently go stale when a
    dependency migrates upstream.  A package counts as migrated if ANY of its
    Lean sources carries a `module` header -- partial migration is enough,
    because what blocks us is a specific imported file, and a partially migrated
    package is one where the build will tell us precisely which.
    """
    roots = []
    for base in ("vendor", os.path.join(".lake", "packages")):
        full = os.path.join(REPO, base)
        if not os.path.isdir(full):
            continue
        for entry in sorted(os.listdir(full)):
            d = os.path.join(full, entry)
            if os.path.isdir(d):
                roots.append(d)
                cand = os.path.join(d, pkg)
                if os.path.isdir(cand):
                    roots.insert(0, cand)
    seen_any = False
    for root in roots:
        for dirpath, _d, files in os.walk(root):
            if os.sep + ".lake" + os.sep in dirpath + os.sep:
                continue
            for f in files:
                if not f.endswith(".lean"):
                    continue
                if os.path.basename(dirpath) != pkg and not dirpath.endswith(os.sep + pkg):
                    continue
                seen_any = True
                try:
                    with open(os.path.join(dirpath, f), encoding="utf-8") as fh:
                        if li.parse_text(fh.read())[1]:
                            return True
                except OSError:
                    continue
    return False if seen_any else None


def blocked_modules(graph) -> tuple[set[str], dict[str, str]]:
    """Modules that CANNOT migrate yet, and why.

    A `module` file cannot import a non-`module` file, so any module that
    transitively imports an unmigrated external package is blocked -- along with
    everything that imports it.  In this tree that is the vendored Sail model:
    `EvmAsm/Rv64/SailEquiv/StateRel.lean` does `import Out`, and `Out` is not
    migrated (nor is its own upstream dependency, which is not ours to change).

    This is accepted, not worked around.  Invalidation stops at a migrated
    module whose interface is unchanged, so an unmigrated straggler only
    rebuilds when something it DIRECTLY imports changes.
    """
    cache: dict[str, bool | None] = {}
    seeds: dict[str, str] = {}

    # Deliberate deferrals, each with a reason recorded in the file.  Treated
    # exactly like an unmigratable dependency, because that is what they are for
    # the purposes of wave selection: their reverse cone cannot migrate either.
    if os.path.exists(DEFERRED):
        with open(DEFERRED, encoding="utf-8") as fh:
            for line in fh:
                line = line.split("#", 1)[0].strip()
                if line and line in graph.modules:
                    seeds[line] = "deferred (see scripts/module-system-deferred.txt)"

    for m in graph.modules:
        if m in seeds:
            continue
        for pkg in graph.external.get(m, ()):  # package roots, e.g. "Out"
            if pkg not in cache:
                cache[pkg] = _package_is_migrated(pkg)
            if cache[pkg] is False:
                seeds[m] = pkg
                break

    rev = graph.importers()
    blocked: set[str] = set()
    reason: dict[str, str] = {}
    stack = [(m, f"imports unmigrated package `{p}`") for m, p in seeds.items()]
    while stack:
        m, why = stack.pop()
        if m in blocked:
            continue
        blocked.add(m)
        reason[m] = why
        for up in rev.get(m, ()):
            if up not in blocked:
                stack.append((up, f"imports blocked `{m}`"))
    return blocked, reason


def tree_closure_violations() -> list[str]:
    """Migrated modules that import a NON-migrated one, as the tree stands.

    This is the check that matters, and it is NOT the same as `--check-closed`.
    `--check-closed` validates a WAVE LIST before conversion; this validates the
    TREE AFTER it. They diverge the moment a module is deferred *after* its
    importers were already converted -- the importers stay migrated, the
    dependency reverts, and `--apply` is idempotent so it never touches them
    again.

    That happened: `Codegen.Emit` was deferred after 26 of its importers had been
    converted, and because the wave build only compiles the wave's own module
    list, nothing local noticed. CI did, with 100+ copies of
    ``cannot import non-`module` EvmAsm.Codegen.Emit from `module```.

    Source-only and about a second, so run it before every wave PR.
    """
    graph = li.ImportGraph(REPO, ROOT_DIRS)
    bad = []
    for m in sorted(graph.modules):
        if not graph.module_header.get(m):
            continue
        for e in graph.edges.get(m, ()):
            t = e.target
            if t in graph.modules and not graph.module_header.get(t):
                bad.append(f"{m} (migrated) imports {t} (NOT migrated)")
    return bad


def frontier_wave(limit: int, skip_prefixes: tuple[str, ...] = ()) -> list[str]:
    """Up to `limit` modules that can migrate NOW, skipping `skip_prefixes`.

    `wave(level)` selects by longest dependency chain, which is the right shape
    when migrating the whole tree bottom-up. It is the WRONG shape when a subtree
    is deliberately deferred: levels interleave, so a level-`k` cut drags in the
    deferred subtree's peers and stalls on them.

    This selects by REACHABILITY instead -- repeatedly take every module whose
    dependencies are all already migrated or already chosen -- so the result is
    downward closed by construction while never naming a skipped module. Used for
    the EVM-first order while `EvmAsm.Rv64.*` is held back for the interpreter /
    Sail refactor (GH #12900).

    `limit` caps the wave for merge cadence, not for correctness. Modules are
    taken in dependency order, so a truncated wave is still downward closed.
    """
    graph = li.ImportGraph(REPO, ROOT_DIRS)
    blocked, _why = blocked_modules(graph)
    migrated = {m for m in graph.modules if graph.module_header.get(m)}

    def skipped(m: str) -> bool:
        return any(m == p or m.startswith(p + ".") for p in skip_prefixes)

    eligible = {m for m in graph.modules
                if m not in migrated and m not in blocked and not skipped(m)}
    chosen: list[str] = []
    chosen_set: set[str] = set()
    while len(chosen) < limit:
        # A module is ready when every in-tree dependency is migrated or chosen.
        ready = sorted(
            m for m in eligible
            if m not in chosen_set
            and all(e.target not in graph.modules
                    or e.target in migrated or e.target in chosen_set
                    for e in graph.edges.get(m, ()))
        )
        if not ready:
            break
        for m in ready:
            if len(chosen) >= limit:
                break
            chosen.append(m)
            chosen_set.add(m)
    return chosen


def wave(level: int) -> list[str]:
    """Every module whose longest dependency chain is <= `level`.  Downward
    closed by construction: a module's dependencies all have strictly lower
    level."""
    graph = li.ImportGraph(REPO, ROOT_DIRS)
    depth: dict[str, int] = {}
    order = []
    WHITE, GREY, BLACK = 0, 1, 2
    colour = {m: WHITE for m in graph.modules}
    for start in sorted(graph.modules):
        if colour[start] != WHITE:
            continue
        stack = [(start, False)]
        while stack:
            node, expanded = stack.pop()
            if expanded:
                depth[node] = max(
                    (depth.get(e.target, 0) + 1 for e in graph.edges.get(node, ())
                     if e.target in graph.modules),
                    default=0,
                )
                colour[node] = BLACK
                order.append(node)
                continue
            if colour[node] == BLACK:
                continue
            if colour[node] == GREY:
                raise ValueError(f"import cycle through {node}")
            colour[node] = GREY
            stack.append((node, True))
            for e in graph.edges.get(node, ()):
                c = colour.get(e.target, WHITE)
                if c == GREY:
                    raise ValueError(f"import cycle through {e.target}")
                if c == WHITE:
                    stack.append((e.target, False))
    blocked, _why = blocked_modules(graph)
    return sorted(m for m in graph.modules
                  if depth.get(m, 0) <= level and m not in blocked)


# ---------------------------------------------------------------- self-test

PLAIN_IN = """/-
  EvmAsm.Demo
-/
import EvmAsm.A
import EvmAsm.B

theorem t : True := trivial
"""

PLAIN_OUT = """/-
  EvmAsm.Demo
-/
module

import EvmAsm.A
import EvmAsm.B

theorem t : True := trivial
"""


def self_test() -> int:
    fail = []

    def check(name, src, want_substrings, unwanted=()):
        got, _ = convert(src)
        for w in want_substrings:
            if w not in got:
                fail.append(f"  {name}: missing {w!r}\n--- got ---\n{got}")
        for u in unwanted:
            if u in got:
                fail.append(f"  {name}: unexpectedly contains {u!r}\n--- got ---\n{got}")
        for p in verify(src, got):
            fail.append(f"  {name}: verify: {p}")
        return got

    # 1. The plain case.
    got = check("plain", PLAIN_IN,
                ["module\n", "public import EvmAsm.A", "public import EvmAsm.B",
                 "@[expose] public section"],
                ["meta import"])
    if got.index("module") > got.index("public import EvmAsm.A"):
        fail.append("  plain: `module` must precede the first import")

    # 2. THE EMIT-POSITION TRAP.  A file whose imports each emit more than one
    #    output line is where a precomputed offset lands the section inside the
    #    import block.  This is the regression pin for that bug.
    got = check("meta trigger", PLAIN_IN.replace("theorem t", "#guard 1 = 1\ntheorem t"),
                ["meta import EvmAsm.A", "meta import EvmAsm.B",
                 "public import EvmAsm.A", "@[expose] public section"])
    sec = got.index("@[expose] public section")
    if got.index("meta import EvmAsm.B") > sec:
        fail.append("  meta trigger: an import landed AFTER the section")

    # 3. Prose interleaved between import groups must survive in place.
    src = ("/- banner -/\nimport EvmAsm.A\n/- why B -/\nimport EvmAsm.B\n\n"
           "theorem t : True := trivial\n")
    got = check("interleaved prose", src,
                ["/- why B -/", "public import EvmAsm.A", "public import EvmAsm.B"])
    if got.index("/- why B -/") > got.index("public import EvmAsm.B"):
        fail.append("  interleaved prose: comment moved past its import")

    # 4. Every import form is preserved, trailing comments included.
    check("all forms",
          "/- b -/\nimport all EvmAsm.A\nimport EvmAsm.B -- shake: keep\n\ndef d := 1\n",
          ["public import all EvmAsm.A", "public import EvmAsm.B -- shake: keep"])

    # 4b. `open private … from M` must add `import all M`, because M's private
    #     half lives in a separate `.olean.private` a public import does not
    #     carry.  Names may wrap across lines before `from`, so the multi-line
    #     shape is pinned too.
    check("open private -> import all",
          "/- b -/\nimport EvmAsm.A\nimport EvmAsm.B\n\n"
          "open private f from EvmAsm.A\n\ndef d := 1\n",
          ["import all EvmAsm.A", "public import EvmAsm.A"])
    check("open private, wrapped names",
          "/- b -/\nimport EvmAsm.A\n\n"
          "open private f g\n  h from EvmAsm.A\n\ndef d := 1\n",
          ["import all EvmAsm.A"])
    #     NEGATIVE CONTROL: a file with no `open private` must gain no
    #     `import all` -- otherwise the pin above passes for the wrong reason.
    got = check("no open private", "/- b -/\nimport EvmAsm.A\n\ndef d := 1\n",
                ["public import EvmAsm.A"], ["import all"])
    #     NEGATIVE CONTROL: `from` a module this file does NOT import is left
    #     alone; inventing an edge is worse than the error it would prevent.
    check("open private from a non-dependency",
          "/- b -/\nimport EvmAsm.A\n\nopen private f from EvmAsm.Z\n\ndef d := 1\n",
          ["public import EvmAsm.A"], ["import all"])

    # 5. No imports at all.
    got = check("no imports", "/- b -/\n\ndef d := 1\n",
                ["module", "@[expose] public section"])
    if got.index("@[expose] public section") > got.index("def d := 1"):
        fail.append("  no imports: section must precede the first definition")

    # 5b. A file that is ONLY a banner: no imports and no code, so the emit
    #     loop never reaches the insertion index.  This raised ValueError on the
    #     first full-tree dry run.
    got = check("banner only", "/-\n  EvmAsm.Umbrella\n-/\n",
                ["module", "@[expose] public section"])

    # 5b'. OVERLAPPING comment delimiters. `/-/` opens a banner whose 2nd and
    #      3rd characters spell `-/`, so a `str.count`-based depth reads it as
    #      already closed and emits the header ABOVE the real imports -- a hard
    #      build error. This tree really contains one
    #      (`Codegen/Programs/AmsterdamBlobGasPriceBody2Spec.lean`).
    got = check("banner opening `/-/`",
                "/-/\n  prose\n-/\nimport EvmAsm.A\n\ndef d := 1\n",
                ["module", "public import EvmAsm.A", "@[expose] public section"])
    if got.index("@[expose] public section") < got.index("public import EvmAsm.A"):
        fail.append("  banner opening `/-/`: section landed above the imports")
    if "/-/" not in got:
        fail.append("  banner opening `/-/`: banner was mangled")

    # 5c. The anchor must be a tracked index, not a search for "module": a file
    #     whose prose or code contains that word must not steer the insertion.
    got = check("word `module` in the body",
                "/- b -/\n\ndef module := 1\n",
                ["module\n", "@[expose] public section"])
    if got.index("@[expose] public section") > got.index("def module := 1"):
        fail.append("  word `module` in the body: section landed after the code")

    # 5d. An EMPTY file.  This tree has one (`EL/Conformance/All.lean`), and it
    #     was the single file for which the effective-line-count invariant went
    #     NEGATIVE, because the output had no trailing newline.
    got = check("empty file", "", ["module", "@[expose] public section"])
    if not got.endswith("\n"):
        fail.append("  empty file: output must end with a newline")

    # 6. IDEMPOTENCE.  This is what makes "regenerate" the merge strategy, so
    #    it is pinned, not assumed.
    once, _ = convert(PLAIN_IN)
    twice, stats = convert(once)
    if once != twice:
        fail.append("  idempotence: a second conversion changed the file")
    if stats.get("skipped") != "already migrated":
        fail.append("  idempotence: a migrated file was not reported as skipped")

    # 7. NEGATIVE CONTROL for the meta detector: an ordinary proof file with no
    #    metaprogramming must NOT get meta imports.  A detector that fires on
    #    everything would "work" on every positive case above.
    if needs_meta("/- b -/\nimport EvmAsm.A\ntheorem t : 1 = 1 := rfl\n"):
        fail.append("  meta detector: fired on an ordinary proof file")
    for trig in ["#guard 1 = 1", "#eval 2", "initialize x : Nat := pure 1",
                 "open Lean in", "def f : MetaM Unit := pure ()",
                 "syntax \"foo\" : term", "register_simp_attr my_set",
                 # Applying a user-defined attribute needs it at meta level.
                 # Wave 10 hit this as `Unknown attribute [rv64_wp_cert]`,
                 # which names the attribute and not the missing import.
                 "attribute [rv64_wp_cert] foo"]:
        if not needs_meta(f"/- b -/\nimport EvmAsm.A\n{trig}\n"):
            fail.append(f"  meta detector: MISSED {trig!r}")

    # 8. `registerSimpAttr` pulls in the attribute module, which is normally not
    #    among the file's own imports.
    got, _ = convert("/- b -/\nimport EvmAsm.A\nregister_simp_attr my_set\n")
    if f"public meta import {SIMP_ATTR_MODULE}" not in got:
        fail.append("  simp attr: the attribute module was not added")

    # 8b. The verifier must not trip over the word "import" appearing in PROSE
    #     inside a block comment after the section.  Four real files in this
    #     tree do exactly that; a raw regex over the text reported all four.
    prose = ("/- b -/\nimport EvmAsm.A\n\n/-\n  Note:\n"
             "  import (the dependency runs the other way)\n-/\ndef d := 1\n")
    got, _ = convert(prose)
    if verify(prose, got):
        fail.append(f"  prose `import`: false positive: {verify(prose, got)}")

    # 8c. THE SIZE-GATE INVARIANT: conversion must not change a file's
    #     effective line count (`wc -l` minus the header block), or
    #     `check-file-size.sh` starts failing on files nobody edited.  Two
    #     earlier definitions of the header block drifted here -- one by +2 per
    #     file, one by up to -95 on an umbrella -- and neither raised an error,
    #     they just moved the number.  Shapes chosen to cover both drifts.
    for name, src in [
        ("plain", PLAIN_IN),
        ("no imports", "/- b -/\n\ndef d := 1\n"),
        ("empty", ""),
        ("blank between imports",
         "/- b -/\nimport EvmAsm.A\n\nimport EvmAsm.B\n\ndef d := 1\n"),
        ("prose between imports",
         "/- b -/\nimport EvmAsm.A\n/- why B -/\nimport EvmAsm.B\n\ndef d := 1\n"),
        ("meta trigger",
         "/- b -/\nimport EvmAsm.A\nimport EvmAsm.B\n\n#guard 1 = 1\ndef d := 1\n"),
        ("umbrella (imports only)",
         "/- b -/\nimport EvmAsm.A\n/- group -/\nimport EvmAsm.B\nimport EvmAsm.C\n"),
    ]:
        conv, _ = convert(src)
        before = src.count("\n") - li.header_lines(src)
        after = conv.count("\n") - li.header_lines(conv)
        if before != after:
            fail.append(f"  size invariant [{name}]: effective lines {before} "
                        f"-> {after} ({after - before:+d}); conversion must be "
                        f"line-neutral for check-file-size.sh")

    import tempfile

    # 8d. Blocked-module detection, on a hand-built tree so the expected answer
    #     is known.  `x` imports an external package with no `module` header;
    #     `y` imports `x`; `z` is independent and must NOT be swept in.  The
    #     negative half matters most: an over-eager blocker would quietly shrink
    #     every wave and the migration would look "done" while nothing moved.
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, "L"))
        os.makedirs(os.path.join(td, "vendor", "p", "Ext"))
        open(os.path.join(td, "vendor", "p", "Ext", "a.lean"), "w").write("/- no header -/\n")
        open(os.path.join(td, "L", "x.lean"), "w").write("import Ext.a\n")
        open(os.path.join(td, "L", "y.lean"), "w").write("import L.x\n")
        open(os.path.join(td, "L", "z.lean"), "w").write("/- leaf -/\n")
        g = li.ImportGraph(td, ["L"])
        saved = globals()["REPO"]
        globals()["REPO"] = td
        try:
            blocked, why = blocked_modules(g)
        finally:
            globals()["REPO"] = saved
        if blocked != {"L.x", "L.y"}:
            fail.append(f"  blocked: want {{L.x, L.y}}, got {sorted(blocked)}")
        if "L.z" in blocked:
            fail.append("  blocked: an independent module was swept in")
        if blocked and "unmigrated package" not in why.get("L.x", ""):
            fail.append(f"  blocked: L.x reason should name the package, got "
                        f"{why.get('L.x')!r}")

    # 9. The verifier must actually be able to FAIL, or steps 1-8 prove nothing.
    broken = PLAIN_IN.replace("import EvmAsm.B\n", "")
    if not verify(PLAIN_IN, convert(broken)[0]):
        fail.append("  verify: a dropped import was not reported")
    # ... and it must still catch a REAL import-after-section, not just be
    # switched off by the block-comment fix above.
    real = convert(PLAIN_IN)[0] + "\nimport EvmAsm.C\n"
    if not any("follows" in x for x in verify(PLAIN_IN, real)):
        fail.append("  verify: a real import after the section was not reported")

    if fail:
        print("migrate-module-system --self-test: FAIL")
        print("\n".join(fail))
        return 1
    print("migrate-module-system --self-test: OK (12 shape cases incl. the "
          "emit-position pin, idempotence, 1 meta negative control + 7 trigger "
          "pins, simp-attr case, 2 `open private` -> `import all` pins + 2 "
          "negative controls, 7 size-invariant shapes, 1 blocked-module "
          "case with a negative control, 2 verifier non-vacuity pins)")
    return 0


# ---------------------------------------------------------------------- CLI

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("paths", nargs="*", help="`.lean` files to convert")
    ap.add_argument("--wave", type=int,
                    help="convert every module with longest chain <= LEVEL "
                         "(downward-closed by construction)")
    ap.add_argument("--apply", action="store_true", help="write the files")
    ap.add_argument("--check-closed", action="store_true",
                    help="verify the selection is downward-closed and stop")
    ap.add_argument("--check-size-invariant", action="store_true",
                    help="verify over the WHOLE tree that conversion leaves "
                         "every file's effective line count unchanged")
    ap.add_argument("--evm-wave", type=int, metavar="N",
                    help="up to N modules that can migrate now, SKIPPING "
                         "EvmAsm.Rv64.* (held back for the interpreter/Sail "
                         "refactor, GH #12900). Selects by reachability, not by "
                         "level, so it stays downward closed while the Rv64 "
                         "subtree is deferred")
    ap.add_argument("--check-tree-closure", action="store_true",
                    help="verify NO migrated module imports an unmigrated one, "
                         "as the tree stands (run before every wave PR)")
    ap.add_argument("--blocked", action="store_true",
                    help="list modules that cannot migrate, and why")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    if args.check_tree_closure:
        bad = tree_closure_violations()
        if bad:
            print(f"tree closure: {len(bad)} VIOLATION(S) — these will fail the "
                  f"build with `cannot import non-\u0060module\u0060 X from "
                  f"\u0060module\u0060`:")
            for b in bad[:30]:
                print(f"  {b}")
            if len(bad) > 30:
                print(f"  ... and {len(bad) - 30} more")
            return 1
        print("tree closure: OK (no migrated module imports an unmigrated one)")
        return 0

    if args.blocked:
        graph = li.ImportGraph(REPO, ROOT_DIRS)
        blocked, why = blocked_modules(graph)
        print(f"{len(blocked)} of {len(graph.modules)} modules cannot migrate:")
        for m in sorted(blocked):
            print(f"  {m}  -- {why[m]}")
        return 0

    if args.check_size_invariant:
        bad = []
        n = 0
        for root, _d, files in os.walk(os.path.join(REPO, ROOT_DIRS[0])):
            for f in sorted(files):
                if not f.endswith(".lean"):
                    continue
                fp = os.path.join(root, f)
                with open(fp, encoding="utf-8") as fh:
                    src = fh.read()
                conv, _ = convert(src)
                n += 1
                b = src.count("\n") - li.header_lines(src)
                a = conv.count("\n") - li.header_lines(conv)
                if a != b:
                    bad.append(f"{os.path.relpath(fp, REPO)}: {b} -> {a} ({a - b:+d})")
        print(f"size invariant: checked {n} files, {len(bad)} violation(s)")
        for x in bad[:20]:
            print(f"  {x}")
        return 1 if bad else 0

    paths = list(args.paths)
    if args.evm_wave is not None:
        mods = frontier_wave(args.evm_wave, skip_prefixes=("EvmAsm.Rv64",))
        if args.check_closed:
            bad = check_closed(set(mods))
            if bad:
                print(f"NOT downward-closed ({len(bad)} violations):")
                for b in bad[:20]:
                    print(f"  {b}")
                return 1
            print(f"evm-wave {args.evm_wave}: {len(mods)} modules, "
                  f"downward-closed OK (EvmAsm.Rv64.* skipped)")
            return 0
        for m in mods:
            q = li.module_to_path(m, REPO)
            if q:
                paths.append(os.path.join(REPO, q))

    if args.wave is not None:
        mods = wave(args.wave)
        if args.check_closed:
            bad = check_closed(set(mods))
            if bad:
                print(f"NOT downward-closed ({len(bad)} violations):")
                for b in bad[:20]:
                    print(f"  {b}")
                return 1
            print(f"wave {args.wave}: {len(mods)} modules, downward-closed OK")
            return 0
        for m in mods:
            p = li.module_to_path(m, REPO)
            if p:
                paths.append(os.path.join(REPO, p))

    if not paths:
        ap.error("nothing to do: pass paths, --wave, --evm-wave, or --self-test")

    changed = skipped = 0
    problems = []
    indirect: list[str] = []
    for p in paths:
        with open(p, encoding="utf-8") as fh:
            before = fh.read()
        after, stats = convert(before)
        for t in stats.get("indirect_private", ()):
            indirect.append(f"{p}: open private … from {t}")
        if stats.get("skipped"):
            skipped += 1
            continue
        for issue in verify(before, after):
            problems.append(f"{p}: {issue}")
        changed += 1
        if args.apply:
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(after)

    verb = "converted" if args.apply else "would convert"
    print(f"{verb} {changed} file(s), skipped {skipped} already migrated")
    if indirect:
        print(f"\n⚠️  {len(indirect)} `open private … from M` site(s) where M is only a "
              f"TRANSITIVE dependency.\n    These need `import all M` as a NEW direct "
              f"edge; the converter will not add an edge on its own.")
        for x in indirect:
            print(f"    {x}")
    if problems:
        print(f"\n{len(problems)} VERIFY PROBLEM(S) -- nothing was trusted:")
        for x in problems[:20]:
            print(f"  {x}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
