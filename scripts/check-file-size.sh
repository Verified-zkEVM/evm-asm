#!/usr/bin/env bash
#
# check-file-size.sh — enforce the per-file line caps described in
# AGENTS.md ("File-size guardrail") and tracked by issue #314.
#
# Caps (lines, inclusive):
#   * EvmAsm/Evm64/**/Compose/**/*.lean       hard cap 1200 (soft cap 1000)
#   * EvmAsm/Evm64/**/*.lean (everything else) hard cap 1500
#   * EvmAsm/Codegen/Programs.lean +
#     EvmAsm/Codegen/Programs/**/*.lean        hard cap 1500
#
# The Codegen/Programs scope is enforced solely by this script (issue #12494).
# A former Lean `#eval` gate (`FileSizeGuard.lean`) imported only `Lean` and
# read sibling paths from the filesystem, so Lake never invalidated its olean
# when Programs files grew — it passed by not executing. #12493 fixed that
# gate's line-count off-by-one while it was still dormant; the second
# implementation is removed rather than repaired again. This source scan is
# cache-independent and is what actually enforces the codegen cap in CI.
#
# Structural exemption:
#   * Files named Program.lean are exempt under EvmAsm/Evm64 — concrete
#     bytecode + tests are intrinsically long and cheap to compile. (The
#     Codegen/Programs scope has no such exemption: every file is capped.)
#
# No per-file opt-out comments are recognized. A `file-size-exception`
# marker in a checked Lean file is itself a guardrail violation; split
# the file instead.
#
# WHAT IS COUNTED: content lines, i.e. `wc -l` MINUS the module-system header
# block (the `module` keyword, the import lines, and `@[expose] public section`).
# The caps exist to bound REVIEWABLE CONTENT, and that header is a fixed
# mechanical cost which the file's author neither wrote nor can shorten. Without
# the discount, 13 files in this tree breach their cap on the module-system
# migration commit alone -- five of them sit at EXACTLY the cap today, which is
# itself evidence that the cap binds on content and that authors trim to fit.
# Blank lines, banners and prose are NOT discounted: those are the file's own
# and were already inside the cap.
#
# The header block is measured by `scripts/lib/lean_imports.py --header-lines`,
# NOT by a regex here. That file exists precisely because several gates each
# rolled their own import regex and disagreed with each other; `public import`
# and `meta import` defeat all three of the original patterns. So this script
# now has a python3 dependency, which its header previously disclaimed. That is
# a deliberate trade: the alternative is a fifth divergent import parser, and a
# size gate that quietly hands a file free slack for a line of prose beginning
# with the word "import" (`ArenaCapacities.lean` has one).
#
# Usage:
#   scripts/check-file-size.sh           # exit 1 on any violation
#   scripts/check-file-size.sh --report  # always exit 0; print summary
#
# The script is bash (it already requires `mapfile`, i.e. bash 4+) plus one
# batched python3 call for the header-line discount described above -- one
# invocation for the whole file list, not one per file.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ROOT_REL="EvmAsm/Evm64"
# Codegen program registry hub + its sibling submodules (sole Programs cap).
CODEGEN_REL="EvmAsm/Codegen/Programs"
CODEGEN_HUB="EvmAsm/Codegen/Programs.lean"
COMPOSE_CAP=1200
DEFAULT_CAP=1500

mode="enforce"
if [[ ${1:-} == "--report" ]]; then
  mode="report"
fi

violations=0
checked=0
exception_markers=0

# Collect files in deterministic order.
mapfile -t files < <(cd "$ROOT" && {
  find "$ROOT_REL" -name '*.lean' -type f
  find "$CODEGEN_REL" -name '*.lean' -type f
  [[ -f "$CODEGEN_HUB" ]] && printf '%s\n' "$CODEGEN_HUB"
} | LC_ALL=C sort -u)

# Header-line discount for every candidate, in ONE python invocation (the same
# batching rationale as check-unimported.sh, which spent 54 s in CI doing the
# per-file thing).
declare -A header_lines
while IFS=$'\t' read -r hl_path hl_n; do
  header_lines["$hl_path"]="$hl_n"
done < <(cd "$ROOT" && python3 scripts/lib/lean_imports.py --header-lines "${files[@]}")

for rel in "${files[@]}"; do
  path="$ROOT/$rel"
  base="${rel##*/}"

  if [[ "$rel" == EvmAsm/Codegen/* ]]; then
    # Codegen registry hub + submodules: every file capped, no Program.lean exemption.
    cap=$DEFAULT_CAP
    bucket="codegen"
  else
    # Program.lean files are intrinsically bytecode-shaped; skip.
    if [[ "$base" == "Program.lean" ]]; then
      continue
    fi
    if [[ "$rel" == */Compose/* ]]; then
      cap=$COMPOSE_CAP
      bucket="Compose"
    else
      cap=$DEFAULT_CAP
      bucket="opcode"
    fi
  fi

  checked=$((checked + 1))

  raw_lines=$(wc -l < "$path")
  hdr=${header_lines["$rel"]:-0}
  lines=$(( raw_lines - hdr ))
  # A file that is nothing but a header (this tree has a 0-line placeholder)
  # must report 0 content lines, never a negative count.
  (( lines < 0 )) && lines=0

  if grep -q 'file-size-exception' "$path"; then
    violations=$((violations + 1))
    exception_markers=$((exception_markers + 1))
    printf '  FAIL    forbidden file-size-exception marker  %s  [%s]\n' \
      "$rel" "$bucket"
    continue
  fi

  if (( lines <= cap )); then
    continue
  fi

  violations=$((violations + 1))
  printf '  FAIL    %4d / %d lines  %s  [%s]\n' \
    "$lines" "$cap" "$rel" "$bucket"
done

if [[ "$mode" == "report" ]]; then
  printf '\nchecked %d files, %d over cap, %d forbidden exemption marker(s)\n' \
    "$checked" "$((violations - exception_markers))" "$exception_markers"
  exit 0
fi

if (( violations > 0 )); then
  cat >&2 <<EOF

==================================================================
File-size guardrail failed: $violations file(s) exceed the cap.

Caps:
  Evm64 Compose/**/*.lean        $COMPOSE_CAP lines
  other Evm64 Lean files         $DEFAULT_CAP lines  (Program.lean exempt)
  Codegen/Programs[/**/]*.lean   $DEFAULT_CAP lines

Per-file file-size-exception markers are not supported. To fix, split
the file. For Evm64, Compose/ is the canonical pattern — see AGENTS.md
"Parallel file splitting for Compose files" (the DivMod Compose split
took monolithic build time from 87s to 55s). For Codegen/Programs,
extract a cluster of defs into a new sibling submodule and import it back
(e.g. Bls12MapG1Real.lean / ChildFrameHandlerTails.lean).
==================================================================
EOF
  exit 1
fi

printf 'file-size guardrail: %d files checked, all within cap.\n' "$checked"
