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
# The Codegen/Programs scope mirrors the elaboration-time
# EvmAsm.Codegen.Programs.FileSizeGuard `#eval`. That guard only re-runs when
# FileSizeGuard.lean itself recompiles, so a warm CI `.lake` cache skips it and
# an oversize sibling reaches `main` undetected — only a clean `lake build
# codegen` (e.g. the Docker image build) trips it. This source scan is
# cache-independent, so it is what actually enforces the codegen cap on the PR
# path.
#
# Structural exemption:
#   * Files named Program.lean are exempt under EvmAsm/Evm64 — concrete
#     bytecode + tests are intrinsically long and cheap to compile. (The
#     Codegen/Programs scope has none and mirrors FileSizeGuard, which caps
#     every file with no exemption.)
#
# No per-file opt-out comments are recognized. A `file-size-exception`
# marker in a checked Lean file is itself a guardrail violation; split
# the file instead.
#
# Usage:
#   scripts/check-file-size.sh           # exit 1 on any violation
#   scripts/check-file-size.sh --report  # always exit 0; print summary
#
# The script intentionally stays POSIX/bash with no external deps so it
# runs in CI and as a pre-commit hook without setup.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ROOT_REL="EvmAsm/Evm64"
# Codegen program registry hub + its sibling submodules. Capped to mirror
# EvmAsm.Codegen.Programs.FileSizeGuard (see header).
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

for rel in "${files[@]}"; do
  path="$ROOT/$rel"
  base="${rel##*/}"

  if [[ "$rel" == EvmAsm/Codegen/* ]]; then
    # Codegen registry hub + submodules: mirror FileSizeGuard, which caps every
    # file with no Program.lean exemption (there are none in this scope).
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

  lines=$(wc -l < "$path")

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
  Codegen/Programs[/**/]*.lean   $DEFAULT_CAP lines  (mirrors FileSizeGuard)

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
