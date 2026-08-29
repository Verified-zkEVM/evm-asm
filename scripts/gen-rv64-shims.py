#!/usr/bin/env python3
"""Generate the EvmAsm/Rv64 re-export shims over the riscv-zkvm dependency.

WHAT THIS IS
------------
riscv-zkvm v0.3.0 publishes, prebuilt, the 6 RISC-V core modules and the 52
program-logic modules that evm-asm used to compile itself.  Their declarations
kept their leaf names but changed root: `EvmAsm.Rv64.foo` upstream is
`RiscvZkvm.Rv64.foo`.

Rather than rewrite ~3,800 qualified references across 562 evm-asm files, each
`EvmAsm/Rv64/<M>.lean` becomes a shim that imports the upstream module and
re-exports its declarations back into `namespace EvmAsm.Rv64`.  `export` calls
`addAlias`, so `EvmAsm.Rv64.foo` and `RiscvZkvm.Rv64.foo` are the SAME constant:
theorem statements are untouched, and upstream's tactic `Name` literals (which
say `RiscvZkvm.Rv64.*`) match evm-asm's terms exactly.

Keeping the file paths is the point -- it preserves all 835 import edges into
the set, and every piece of metadata keyed on module name.

WHY THE LISTS ARE EXPLICIT
--------------------------
`export` has no wildcard form (Lean/Parser/Command.lean, `many1 ident`), so the
names must be enumerated.  That is what makes this a generator plus a gate:
`--check` re-derives the lists from the dependency's oleans and diffs, so a
declaration added upstream cannot silently go un-exported.

WHAT IS DELIBERATELY NOT EXPORTED
---------------------------------
  * names outside the `RiscvZkvm.Rv64` namespace (attribute parsers, core
    lemmas) -- they arrive via `import`, and aliasing them would put foreign
    names under `EvmAsm.Rv64`;
  * elaborator scratch constants (`.match_1_1`, `._proof_2`) -- implementation
    detail nothing downstream names.

Usage:
    scripts/gen-rv64-shims.py            # rewrite the shims in place
    scripts/gen-rv64-shims.py --check    # fail if any shim is out of date
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The revision an original (pre-shim) module's prelude is read from, used ONLY
# when a shim does not exist yet.  Once generated, a shim carries its own prelude
# between the markers below and git is never consulted again.
#
# That matters twice over.  `origin/main` is not present in CI's shallow
# checkout, so a `--check` that consulted git failed there; and `origin/main` is
# a MOVING ref, so after this lands it would contain the shims themselves and
# regeneration would read a shim's own imports back in.
BASE_REV = "origin/main"

PRELUDE_BEGIN = "-- BEGIN shim prelude (preserved from the original module)"
PRELUDE_END = "-- END shim prelude"


def existing_prelude(path: Path) -> list[str] | None:
    """The prelude already recorded in a generated shim, if there is one."""
    if not path.exists():
        return None
    lines = path.read_text().splitlines()
    if PRELUDE_BEGIN not in lines or PRELUDE_END not in lines:
        return None
    return lines[lines.index(PRELUDE_BEGIN) + 1 : lines.index(PRELUDE_END)]

# The six core modules relocated in riscv-zkvm v0.2.0.  They are not under the
# `Logic.` prefix upstream, so they need their own mapping.
CORE = ["Word", "Basic", "Instructions", "Execution", "Program", "ZiskAccel"]

# Upstream modules with no evm-asm counterpart.  `Bytes` holds the four byte
# lemmas evm-asm's ByteOps used to declare, so its names are folded into the
# ByteOps shim; the other two are new helpers evm-asm never referenced.
FOLD_INTO = {"RiscvZkvm.Rv64.Bytes": "ByteOps"}
SKIP_MODULES = {"RiscvZkvm.Rv64.Logic.Support", "RiscvZkvm.Rv64.CoreTactics"}

# Nothing is filtered by suffix any more.  An earlier version dropped
# `noConfusion`, `injEq`, `sizeOf_spec` and the equation lemmas as "realized on
# demand", but every name here comes from `const2ModIdx`, i.e. it is genuinely
# present in the dependency's oleans.  Dropping them broke real call sites:
# `export` aliases are ALWAYS public, whereas the constants they point at need a
# public import chain, so `Reg` resolved through the alias while
# `Reg.noConfusion` did not.  Aliasing the whole surface removes that asymmetry.

# Elaborator scratch constants (`foo.match_1_1`, `foo._proof_2`).  They are real
# constants in the olean, but they are implementation detail: nothing in evm-asm
# names them, and re-exporting them would pin upstream's elaboration internals
# as part of our surface.
SCRATCH = re.compile(r"\.(match_[\d_]+|_[A-Za-z0-9_]+)(\.|$)")


def dependency_modules() -> list[str]:
    """The dependency modules that need an evm-asm shim.

    Driven off the dependency's own source tree rather than off which modules
    happen to declare something: three `*Attr` modules declare only attribute
    parsers (outside the `RiscvZkvm.Rv64` namespace) and `Tactics/PerfTrace`
    declares nothing at all, but all four still need a shim so that evm-asm's
    import edges to them survive.
    """
    src = ROOT / ".lake" / "packages" / "riscv-zkvm" / "RiscvZkvm" / "Rv64"
    logic = src / "Logic"
    if not logic.is_dir():
        raise SystemExit(
            f"gen-rv64-shims: dependency sources not found at {logic}\n"
            "  run `lake update riscv-zkvm` first"
        )
    mods = []
    for p in sorted(logic.rglob("*.lean")):
        name = str(p.relative_to(logic))[: -len(".lean")].replace("/", ".")
        mod = f"RiscvZkvm.Rv64.Logic.{name}"
        if mod not in SKIP_MODULES:
            mods.append(mod)
    return mods + [f"RiscvZkvm.Rv64.{c}" for c in CORE]

DUMP_LEAN = """\
import RiscvZkvm.Rv64.Logic
{core_imports}

open Lean in
run_cmd Elab.Command.liftCoreM do
  let env <- getEnv
  let mods := env.header.moduleNames
  let mut lines : Array String := #[]
  for (c, midx) in env.const2ModIdx.toList do
    let m := mods[midx.toNat]!
    unless (`RiscvZkvm.Rv64).isPrefixOf m do continue
    if isPrivateName c then continue
    if c.isInternal then continue
    lines := lines.push s!"{{m}}\\t{{c}}"
  IO.FS.writeFile "{out}" (String.intercalate "\\n" lines.toList ++ "\\n")
"""


def dump_declarations() -> dict[str, list[str]]:
    """Ask Lean which declarations each dependency module contributes."""
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "decls.tsv"
        src = Path(td) / "Dump.lean"
        src.write_text(
            DUMP_LEAN.format(
                core_imports="\n".join(f"import RiscvZkvm.Rv64.{c}" for c in CORE),
                out=out,
            )
        )
        proc = subprocess.run(
            ["lake", "env", "lean", str(src)],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0 or not out.exists():
            sys.stderr.write(proc.stdout + proc.stderr)
            raise SystemExit("gen-rv64-shims: failed to enumerate dependency declarations")
        rows = [l.split("\t") for l in out.read_text().splitlines() if "\t" in l]

    by_module: dict[str, list[str]] = {}
    for module, name in rows:
        if not name.startswith("RiscvZkvm.Rv64."):
            continue
        if SCRATCH.search(name):
            continue
        by_module.setdefault(module, []).append(name[len("RiscvZkvm.Rv64.") :])
    return by_module


def target_path(module: str) -> str | None:
    """EvmAsm path a dependency module's declarations should surface at."""
    if module in SKIP_MODULES:
        return None
    if module in FOLD_INTO:
        return FOLD_INTO[module]
    if module.startswith("RiscvZkvm.Rv64.Logic."):
        return module[len("RiscvZkvm.Rv64.Logic.") :].replace(".", "/")
    tail = module[len("RiscvZkvm.Rv64.") :]
    return tail if tail in CORE else None


def upstream_module(rel: str) -> str:
    """The dependency module a given shim should import."""
    name = rel.replace("/", ".")
    return f"RiscvZkvm.Rv64.{name}" if name in CORE else f"RiscvZkvm.Rv64.Logic.{name}"


IMPORT_LINE = re.compile(r"^\s*(public\s+|meta\s+|private\s+)*import\s+")

# The prelude is defined POSITIVELY -- a line belongs to it only if it is one of
# these forms.  An earlier version listed declaration keywords to stop AT, and
# quietly swallowed `meta register_option xperm.cert` (not in the list) into the
# shim, which then collided with upstream's copy of the same option.  Enumerating
# what to keep fails closed; enumerating what to stop at fails open.
PRELUDE_LINE = re.compile(
    r"^\s*(module|@\[expose\]\s+public\s+section|public\s+section|section)\s*$"
)


def original_prelude(rel: str) -> tuple[list[str], bool]:
    """This module's prelude before it became a shim, plus whether it is `meta`.

    Preserving the prelude verbatim is load-bearing, not cosmetic, for two
    independent reasons:

    1. `export` creates an ALIAS, and aliases live in the file that writes
       them -- they do not travel transitively the way a declaration does.  A
       file importing `EvmAsm.Rv64.SepLogic` used to pick up
       `EvmAsm.Rv64.signExtend12` through SepLogic's own import chain.  Without
       these edges that name arrives only as `RiscvZkvm.Rv64.signExtend12`, and
       every use site silently auto-binds it as an implicit variable instead.

    2. 53 of the 58 modules are already migrated to the Lean module system, so
       the header (`module`, `public import`, `meta import`, `@[expose] public
       section`) has to come across intact -- `public import` outside `module`
       is a hard error.
    """
    path = f"EvmAsm/Rv64/{rel}.lean"
    proc = subprocess.run(
        ["git", "show", f"{BASE_REV}:{path}"],
        cwd=ROOT, capture_output=True, text=True,
    )
    if proc.returncode != 0:
        raise SystemExit(
            f"gen-rv64-shims: no shim at {path} and cannot read {BASE_REV}:{path}\n"
            "  A dependency module has no evm-asm shim yet. Generate it locally\n"
            "  (scripts/gen-rv64-shims.py, with origin/main fetched) and commit the\n"
            "  result -- CI's shallow checkout has no origin/main and cannot do this."
        )

    # Block-comment depth must be tracked: these files open with `/- ... -/`
    # banners whose prose contains lines starting `namespace`, `def`, ... and
    # stopping on one of those mid-banner truncates the comment, which surfaces
    # far away as `unterminated comment` and a cascade of `bad import`.
    prelude, has_meta, depth = [], False, 0
    doc_start = None          # index where a trailing `/-- ... -/` block began
    for line in proc.stdout.splitlines():
        stripped = line.strip()
        if depth == 0:
            keep = (
                not stripped
                or stripped.startswith("--")
                or stripped.startswith("/-")
                or bool(IMPORT_LINE.match(line))
                or bool(PRELUDE_LINE.match(line))
            )
            # Order matters: break BEFORE clearing doc_start.  The line that
            # ends the prelude is precisely the declaration a trailing `/--`
            # docstring belongs to, so clearing first would lose the very fact
            # that tells us to drop it.
            if not keep:
                break
            if stripped.startswith("/--"):
                doc_start = len(prelude)
            elif stripped:
                doc_start = None
        if IMPORT_LINE.match(line):
            has_meta = has_meta or stripped.startswith("meta ")
        prelude.append(line)
        depth += line.count("/-") - line.count("-/")
        depth = max(depth, 0)
    # A `/-- ... -/` doc comment binds to the declaration that follows it.  If
    # the prelude ends with one, that declaration is exactly what we just cut,
    # and the docstring is left dangling -- which Lean reports at EOF as
    # `unexpected end of input; expected 'abbrev', 'axiom', ...`.  Drop it.
    if doc_start is not None:
        prelude = prelude[:doc_start]

    while prelude and not prelude[-1].strip():
        prelude.pop()

    # Fail closed on an attribute left waiting for its declaration.  A plain
    # `/- ... -/` banner at the end is fine (it binds to nothing); only a `/--`
    # doc comment dangles, and those are truncated above.
    tail = prelude[-1].strip() if prelude else ""
    if tail.startswith("@[") and "section" not in tail:
        raise SystemExit(
            f"gen-rv64-shims: {path} prelude ends on a dangling comment/attribute:\n"
            f"  {tail}\n"
            "  this would not parse; the prelude scanner needs adjusting"
        )
    return prelude, has_meta


def render(rel: str, names: list[str], path: Path) -> str:
    up = upstream_module(rel)
    prelude = existing_prelude(path)

    note = [
        "-- GENERATED by scripts/gen-rv64-shims.py -- do not edit by hand.",
        "--",
        f"-- `{rel.replace('/', '.')}` now lives in the riscv-zkvm dependency, prebuilt.",
        "-- This shim re-exports it so evm-asm's existing references keep resolving;",
        "-- `export` aliases the SAME constants, so no statement changes meaning.",
        "--",
        "-- Only the export block below is regenerated. The prelude between the",
        "-- markers is preserved verbatim and is the source of truth -- aliases do not",
        "-- propagate transitively, so those import edges are what let downstream files",
        "-- still see the names they used to. Edit it here if the imports must change.",
        "--",
        "-- Regenerate with `scripts/gen-rv64-shims.py`; `--check` gates it in CI.",
    ]

    if prelude is None:
        # First generation only: lift the prelude off the pre-shim module, then
        # splice the dependency import in after the last existing import so it
        # sits inside the module header rather than after `public section`.
        prelude, has_meta = original_prelude(rel)
        last = max((i for i, l in enumerate(prelude) if IMPORT_LINE.match(l)), default=-1)
        is_module = any(l.strip() == "module" for l in prelude)
        added = [f"public import {up}"] if is_module else [f"import {up}"]
        if is_module and has_meta:
            added.append(f"meta import {up}")
        if last >= 0:
            prelude = prelude[: last + 1] + added + prelude[last + 1 :]
        else:
            insert = next((i for i, l in enumerate(prelude) if l.strip() == "module"), -1)
            prelude = prelude[: insert + 1] + [""] + added + prelude[insert + 1 :]

    body = note + [PRELUDE_BEGIN] + prelude + [PRELUDE_END, ""]
    if names:
        body.append("namespace EvmAsm.Rv64")
        body.append("")
        # 4 names per line keeps the diff readable and the lines under 100 cols.
        for i in range(0, len(names), 4):
            chunk = " ".join(names[i : i + 4])
            body.append(f"export RiscvZkvm.Rv64 ({chunk})")

        # `export` registers ALIASES, which are constants -- it does not create
        # namespaces.  Downstream files write `open EvmAsm.Rv64.Program`, and
        # without these declarations that is `unknown namespace`.  An empty
        # `namespace X end X` is enough, and is visible to importers.
        prefixes = sorted({
            n.rsplit(".", i)[0]
            for n in names
            for i in range(1, n.count(".") + 1)
        })
        if prefixes:
            body.append("")
            body.append("-- Namespaces downstream files `open`; see render() for why these")
            body.append("-- cannot come from `export`.")
            for p in prefixes:
                body.append(f"namespace {p} end {p}")

        body.append("")
        body.append("end EvmAsm.Rv64")
    return "\n".join(body) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="verify, do not rewrite")
    args = ap.parse_args()

    by_module = dump_declarations()

    # Every dependency module gets a shim, even if it exports nothing.
    shims: dict[str, list[str]] = {}
    for module in dependency_modules():
        rel = target_path(module)
        if rel is not None:
            shims.setdefault(rel, [])

    for module, names in by_module.items():
        rel = target_path(module)
        if rel is not None:
            shims.setdefault(rel, []).extend(names)

    stale, written = [], 0
    for rel, names in sorted(shims.items()):
        path = ROOT / "EvmAsm" / "Rv64" / f"{rel}.lean"
        text = render(rel, sorted(set(names)), path)
        if args.check:
            if not path.exists() or path.read_text() != text:
                stale.append(str(path.relative_to(ROOT)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            written += 1

    if args.check:
        if stale:
            print("gen-rv64-shims: these shims are out of date:", file=sys.stderr)
            for s in stale:
                print(f"  {s}", file=sys.stderr)
            print("  regenerate with: scripts/gen-rv64-shims.py", file=sys.stderr)
            return 1
        print(f"gen-rv64-shims: {len(shims)} shims up to date")
        return 0

    total = sum(len(set(v)) for v in shims.values())
    print(f"gen-rv64-shims: wrote {written} shims re-exporting {total} declarations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
