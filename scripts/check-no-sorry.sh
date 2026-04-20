#!/usr/bin/env bash
#
# check-no-sorry.sh — fail if any .lean file under EvmAsm/ contains
# `sorry` or `admit` outside of comments. Documents the SOUNDNESS.md
# claim that "the build passes with no `sorry` and no `admit`".
#
# Strategy:
#   1. Strip `/- ... -/` block comments (handles `/-- ... -/` docstrings
#      and nested blocks).
#   2. Strip `--` line-comment tails.
#   3. grep for the tokens `sorry` / `admit` in what remains.
#
# Exits 1 on any violation; 0 otherwise.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

violations=0
while IFS= read -r -d '' file; do
  awk '
    BEGIN { depth = 0 }
    {
      line = $0
      out = ""
      i = 1
      n = length(line)
      while (i <= n) {
        c2 = substr(line, i, 2)
        if (depth > 0) {
          if (c2 == "-/") { depth--; i += 2 }
          else if (c2 == "/-") { depth++; i += 2 }
          else i++
        } else {
          if (c2 == "/-") { depth++; i += 2 }
          else { out = out substr(line, i, 1); i++ }
        }
      }
      # strip `--` line comment tails (only when not inside a block)
      if (depth == 0) {
        c = index(out, "--")
        if (c > 0) out = substr(out, 1, c - 1)
      }
      print out
    }
  ' "$file" > "$tmp"
  if matches=$(grep -nE '\b(sorry|admit)\b' "$tmp"); then
    echo "violation in $file:"
    echo "$matches" | sed 's/^/  /'
    violations=$((violations + 1))
  fi
done < <(find EvmAsm -name '*.lean' -type f -print0)

if [ "$violations" -gt 0 ]; then
  echo ""
  echo "$violations file(s) contain sorry/admit outside comments."
  echo "See SOUNDNESS.md §1 — no sorry / no admit is a soundness claim."
  exit 1
fi

echo "OK: no sorry/admit in EvmAsm/"
