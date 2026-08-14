#!/usr/bin/env bash
# check-codegen-counts.sh — keep CODEGEN.md's opcode prose tied to the
# built codegen registry (#12322).
#
# The expected count comes from the already-built `codegen` executable, which
# evaluates the actual `tinyInterpRegistry` definition. It is intentionally
# not scraped from RegistryInvariants.lean:
# comparing prose with a theorem literal would allow both to drift together.
# RegistryInvariants.lean remains the independent kernel-checked backstop.
#
# Both CODEGEN.md sites are checked independently. The invalid count is derived
# as 256 - wired rather than treated as a second independent source of truth.

set -euo pipefail
cd "$(dirname "$0")/.."

CODEGEN_EXE="${CODEGEN_EXE:-.lake/build/bin/codegen}"
if [[ ! -x "$CODEGEN_EXE" ]]; then
  echo "check-codegen-counts: built codegen executable not found at $CODEGEN_EXE" >&2
  echo "check-codegen-counts: run 'lake build codegen' before this gate" >&2
  exit 1
fi

report="$("$CODEGEN_EXE" --registry-count)"
wired="$(printf '%s\n' "$report" | sed -nE 's/^wired=([0-9]+)$/\1/p')"
invalid="$(printf '%s\n' "$report" | sed -nE 's/^invalid=([0-9]+)$/\1/p')"

if [[ -z "$wired" || -z "$invalid" ]]; then
  echo "check-codegen-counts: malformed registry report:" >&2
  printf '%s\n' "$report" >&2
  exit 1
fi

derived_invalid=$((256 - wired))
if [[ "$invalid" -ne "$derived_invalid" ]]; then
  echo "check-codegen-counts: executable report is inconsistent: wired=$wired invalid=$invalid expected_invalid=$derived_invalid" >&2
  exit 1
fi

site1="$(grep -F '**Opcode coverage**' CODEGEN.md \
  | sed -nE 's/.*\*\*([0-9]+) \/ 256 bytes wired\*\*.*; ([0-9]+) → `h_invalid`.*/\1 \2/p')"
site2="$(grep -F '**Total:' CODEGEN.md \
  | sed -nE 's/.*\*\*Total: ([0-9]+) wired opcode bytes.*\*\* ([0-9]+) bytes fall through to.*/\1 \2/p')"

if [[ -z "$site1" || -z "$site2" ]]; then
  echo "check-codegen-counts: could not locate both CODEGEN.md count sites" >&2
  exit 1
fi

expected="$wired $invalid"
if [[ "$site1" != "$expected" ]]; then
  echo "check-codegen-counts: CODEGEN.md opcode-coverage site says '$site1', expected '$expected'" >&2
  exit 1
fi
if [[ "$site2" != "$expected" ]]; then
  echo "check-codegen-counts: CODEGEN.md registry site says '$site2', expected '$expected'" >&2
  exit 1
fi

echo "check-codegen-counts: OK — both CODEGEN.md sites match built tinyInterpRegistry (wired=$wired, h_invalid=$invalid)."
