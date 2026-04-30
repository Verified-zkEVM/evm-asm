#!/usr/bin/env python3
"""
Filter `lake exe shake EvmAsm` output to drop suggestions in files where
shake is known to produce false positives.

Background
----------
shake's static analysis follows direct constant references but does not see:

  * notations / `notation` declarations exported from an imported module,
  * tactic registries (e.g. `@[spec_gen_*]`, `@[grindset]`, custom simp attrs)
    where lemmas are looked up by attribute, not by direct reference,
  * `runBlock` / `xperm` / `xperm_hyp` / `xcancel` / `xsimp` / `seqFrame`
    macros that elaborate spec lookups via tactics, and
  * identifiers introduced through term-elaborator macros referenced only
    inside proofs.

Whenever a file uses any of these mechanisms, the imports that supply the
underlying lemma database look unused to shake even though they are not.
Past attempts (#1045 slices 3, 4, 5, 6) repeatedly hit this — see beads tasks
evm-asm-o6y, evm-asm-pic and the discussion under #1045.

What this script does
---------------------
Reads shake stdout (or a saved capture) on stdin, parses each per-file block,
and drops the block if the file body contains any of the marker tokens below.

The result is a much smaller list of suggestions, dominated by genuine
unused imports — a much better starting point than the raw 800+ line output.

Usage
-----
    lake build
    lake exe shake EvmAsm 2>/dev/null | scripts/shake-filter.py

Or with a saved capture:

    lake exe shake EvmAsm 2>/dev/null > shake.txt
    scripts/shake-filter.py < shake.txt

Add `--show-dropped` to see what was filtered out and why.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Marker tokens that indicate a file relies on attribute-driven tactic
# lookup, custom simp attributes, or notation re-export. Any file whose
# source text contains one of these will have its shake suggestions dropped.
#
# Keep this list short and targeted — each entry should correspond to a
# documented false-positive class, not just "things that look unusual".
MARKERS: list[tuple[str, str]] = [
    # Spec database lookup (attribute-driven). These tactics expand to
    # `simp` / `grind` calls that pick up lemmas by `@[spec_gen]` /
    # `@[spec_gen_*]`, so the import that *registers* the lemma looks
    # unreferenced to shake.
    ("runBlock",           "tactic looks up @[spec_gen] specs by attribute"),
    ("xperm",              "AC-perm tactic uses sepConj_* lemmas via simp set"),
    ("xperm_hyp",          "AC-perm tactic uses sepConj_* lemmas via simp set"),
    ("xcancel",            "frame-cancel tactic uses sepConj_* lemmas via simp set"),
    ("xsimp",              "tactic uses xsimp simp set (attribute-driven)"),
    ("seqFrame",           "tactic uses seqFrame simp set (attribute-driven)"),
    ("liftSpec",           "tactic uses liftSpec simp set (attribute-driven)"),
    # spec_gen attribute attached locally — declares lemmas that consumers
    # of the namespace pick up by attribute, not by direct reference.
    ("@[spec_gen",         "@[spec_gen_*] declarations are consumed by attribute"),
    # spec_gen lookup names commonly appearing in CallingConvention etc.
    ("ld_spec_gen_within", "spec_gen lookup name; backing lemma loaded by attribute"),
    ("sd_spec_gen_within", "spec_gen lookup name; backing lemma loaded by attribute"),
    ("addi_spec_gen_same_within",
                           "spec_gen lookup name; backing lemma loaded by attribute"),
    ("jal_spec_within",    "spec_gen lookup name; backing lemma loaded by attribute"),
    ("jalr_spec_within",   "spec_gen lookup name; backing lemma loaded by attribute"),
    ("jalr_x0_spec_gen_within",
                           "spec_gen lookup name; backing lemma loaded by attribute"),
    # Custom simp attribute registries (the `*Attr.lean` files declare these;
    # consumer files invoke them via `simp [attr]` which shake doesn't track).
    ("rv64_addr",          "custom simp attribute (rv64_addr)"),
    ("divmod_addr",        "custom simp attribute (divmod_addr)"),
    ("reg_ops",            "custom simp attribute (reg_ops)"),
    ("byte_alg",           "custom simp attribute (byte_alg)"),
    # Notation use — `notation \"Word\" => BitVec 64` is in Rv64.Basic; files
    # using `Word` look unrelated to that import.
    ("notation \"Word\"",  "Word notation defined in Rv64.Basic"),
    # RLP Phase1 cascade helpers — the *Cascade*.lean files invoke
    # `rlp_phase1_step_code_disjoint_*` lemmas registered in the
    # `Phase1Disjoint` import (verified in evm-asm-5et: removing the import
    # breaks the build). shake doesn't follow the chained-helper-name lookup.
    ("rlp_phase1_step_code_disjoint",
                           "Phase1Disjoint helpers used via attribute / chained lookup"),
    # DivMod compose Offsets uses `divK_phaseA` / `divK_loopBody` etc inside
    # `example := by decide` blocks; shake misses references inside `example`.
    ("divK_phaseA",        "DivMod.Program identifiers used in `example` blocks"),
    # EvmWordArith CallSkipClose uses `div128Quot_le_q_true` from
    # Div128KB6Composition; shake doesn't follow the underscored compound name.
    ("div128Quot",         "Div128KB6Composition lemmas referenced via compound names"),
]

BLOCK_HEADER = re.compile(r"^/.+\.lean:$")


def parse_blocks(text: str) -> list[tuple[str, list[str]]]:
    """Split shake output into (header_path, body_lines) blocks."""
    blocks: list[tuple[str, list[str]]] = []
    current_path: str | None = None
    current_body: list[str] = []
    for line in text.splitlines():
        if BLOCK_HEADER.match(line):
            if current_path is not None:
                blocks.append((current_path, current_body))
            current_path = line[:-1]  # drop trailing ':'
            current_body = []
        else:
            if current_path is None:
                # Pre-header noise (warnings, etc.) — pass through verbatim
                # by stashing under a sentinel.
                blocks.append(("", [line]))
            else:
                current_body.append(line)
    if current_path is not None:
        blocks.append((current_path, current_body))
    return blocks


def file_markers(path: Path) -> list[tuple[str, str]]:
    """Return the list of (marker, reason) the file body matches."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    hits: list[tuple[str, str]] = []
    for marker, reason in MARKERS:
        if marker in text:
            hits.append((marker, reason))
    return hits


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Filter `lake exe shake` output to drop known false positives.",
    )
    p.add_argument(
        "--show-dropped",
        action="store_true",
        help="Print dropped blocks (commented out) with the marker that triggered them.",
    )
    p.add_argument(
        "--root",
        default=".",
        help="Repo root used to resolve relative paths in shake output (default: cwd).",
    )
    args = p.parse_args(argv)

    raw = sys.stdin.read()
    blocks = parse_blocks(raw)

    kept = 0
    dropped = 0
    out: list[str] = []
    for path_str, body in blocks:
        if path_str == "":
            # Pre-header noise — pass through.
            out.extend(body)
            continue
        path = Path(path_str)
        if not path.is_absolute():
            path = (Path(args.root) / path_str).resolve()
        hits = file_markers(path)
        if hits:
            dropped += 1
            if args.show_dropped:
                marker, reason = hits[0]
                out.append(f"# DROPPED ({marker}): {reason}")
                out.append(f"# {path_str}:")
                for line in body:
                    out.append(f"#   {line}")
            continue
        kept += 1
        out.append(f"{path_str}:")
        out.extend(body)

    print("\n".join(out))
    print(
        f"\n# shake-filter: {kept} block(s) kept, {dropped} dropped as likely false positives.",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
