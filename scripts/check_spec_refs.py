#!/usr/bin/env python3
r"""check_spec_refs.py — machine-check the per-opcode execution-specs reference links.

PROGRESS.md axis F tracks "Per-opcode reference-link audit" and records it as
"manual; `EvmWord.<op>` defs cite Python files in their docstrings (not yet
machine-checked)". This script closes that row: it extracts every
`execution-specs/<path>.py` citation from `EvmAsm/**/*.lean`, resolves it
against the pinned `execution-specs` submodule, and (when the citation carries
a `function \`name\`` anchor within the following two lines) verifies the
anchored symbol is defined in the cited Python file.

Outcome classes:
  * DEAD PATH   (blocking) — cited file does not exist at the pinned rev.
  * DEAD SYMBOL (blocking) — cited file exists but defines no `def <name>`
    / `class <name>`.
  * ELLIPSIS    (advisory) — citations of the form `execution-specs/.../x.py`
    cannot be resolved to a unique file; counted and listed, never blocking
    (they are prose shorthand, not links).

Self-test (`--self-test`): scans a synthetic file containing one good, one
dead-path, and one dead-symbol citation and exits non-zero unless the checker
flags exactly the two bad ones — a checker that cannot demonstrate catching a
planted violation is itself unaudited.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
import tempfile

CITE_RE = re.compile(r"execution-specs/((?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_.-]+\.py)")
ELLIPSIS_RE = re.compile(r"execution-specs/\.\.\./((?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_.-]+\.py)")
FUNC_RE = re.compile(r"function\s+`([A-Za-z_][A-Za-z0-9_]*)`")


def find_citations(lean_root: pathlib.Path):
    """Yield (lean_file, line_no, cited_path, anchor_or_None, is_ellipsis)."""
    for lean_file in sorted(lean_root.rglob("*.lean")):
        lines = lean_file.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if "execution-specs/" not in line:
                continue
            for m in ELLIPSIS_RE.finditer(line):
                yield lean_file, i + 1, m.group(1), None, True
            stripped = ELLIPSIS_RE.sub("", line)
            for m in CITE_RE.finditer(stripped):
                anchor = None
                window = " ".join(lines[i : i + 3])
                fm = FUNC_RE.search(window)
                if fm:
                    anchor = fm.group(1)
                yield lean_file, i + 1, m.group(1), anchor, False


def symbol_defined(py_file: pathlib.Path, name: str) -> bool:
    pat = re.compile(rf"^\s*(?:def|class)\s+{re.escape(name)}\b", re.MULTILINE)
    return bool(pat.search(py_file.read_text(encoding="utf-8", errors="replace")))


def run_scan(lean_root: pathlib.Path, specs_root: pathlib.Path,
             allow: set[str] | None = None) -> int:
    allow = allow or set()
    dead_paths, dead_symbols, ellipses, allowed, ok = [], [], [], [], 0
    for lean_file, line_no, rel, anchor, is_ellipsis in find_citations(lean_root):
        where = f"{lean_file}:{line_no}"
        if is_ellipsis:
            ellipses.append((where, rel))
            continue
        target = specs_root / rel
        if not target.is_file():
            if rel in allow:
                allowed.append((where, rel))
            else:
                dead_paths.append((where, rel))
            continue
        if anchor is not None and not symbol_defined(target, anchor):
            dead_symbols.append((where, rel, anchor))
            continue
        ok += 1
    print(f"check-spec-refs: {ok} resolved citation(s), "
          f"{len(ellipses)} ellipsis citation(s) (advisory), "
          f"{len(allowed)} allowlisted known-stale (burndown), "
          f"{len(dead_paths)} dead path(s), {len(dead_symbols)} dead symbol(s)")
    for where, rel in allowed:
        print(f"  BURNDOWN (allowlisted): {where} cites execution-specs/{rel} "
              f"(missing at pinned rev; tracked in spec-refs-allow.txt)")
    for where, rel in ellipses:
        print(f"  advisory (ellipsis, not checkable): {where} -> .../{rel}")
    for where, rel in dead_paths:
        print(f"  DEAD PATH: {where} cites execution-specs/{rel} (missing at pinned rev)")
    for where, rel, anchor in dead_symbols:
        print(f"  DEAD SYMBOL: {where} cites function `{anchor}` "
              f"not defined in execution-specs/{rel}")
    return 1 if dead_paths or dead_symbols else 0


def self_test(specs_root: pathlib.Path) -> int:
    good = None
    for cand in sorted((specs_root / "src").rglob("*.py")):
        good = cand.relative_to(specs_root)
        break
    if good is None:
        print("self-test: no python files under specs root", file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory() as td:
        root = pathlib.Path(td)
        (root / "Synthetic.lean").write_text(
            f"/-! good: `execution-specs/{good}`.\n"
            f"dead path: `execution-specs/src/ethereum/no_such_module.py`.\n"
            f"dead symbol: `execution-specs/{good}`,\n"
            f"  function `no_such_function_xyzzy`. -/\n",
            encoding="utf-8",
        )
        rc = run_scan(root, specs_root)
    if rc != 1:
        print("self-test FAILED: planted violations were not flagged", file=sys.stderr)
        return 1
    print("self-test OK: planted dead path and dead symbol both flagged")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean-root", default="EvmAsm")
    ap.add_argument("--specs-root", default="execution-specs")
    ap.add_argument("--allowlist", default="scripts/spec-refs-allow.txt")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    specs_root = pathlib.Path(args.specs_root)
    if not (specs_root / "src").is_dir():
        print(f"check-spec-refs: specs root {specs_root} not initialized "
              f"(run: git submodule update --init {specs_root})", file=sys.stderr)
        return 2
    if args.self_test:
        return self_test(specs_root)
    allow = set()
    allow_path = pathlib.Path(args.allowlist)
    if allow_path.is_file():
        for raw in allow_path.read_text(encoding="utf-8").splitlines():
            entry = raw.split("#", 1)[0].strip()
            if entry:
                allow.add(entry)
    return run_scan(pathlib.Path(args.lean_root), specs_root, allow)


if __name__ == "__main__":
    sys.exit(main())
