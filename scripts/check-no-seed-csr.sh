#!/usr/bin/env bash
# CI gate for GH #10796: the SailEquiv bridge excludes Sail's nondeterministic
# Zkr seed-CSR arm.  The exclusion is valid only while the production guest
# contains no CSR instruction addressed at 0x015.  Scan the linked production
# ELF, rather than a source fixture or a stale count, and fail closed on every
# missing-input/tool error.
#
# Usage:
#   scripts/check-no-seed-csr.sh --guest-elf gen-out/regionmap/stateless_guest.elf
#
# The RISC-V toolchain is required.  This gate deliberately has no skip path:
# a missing ELF or objdump means the scope assertion was not checked and must
# not read as a green result.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# shellcheck source=lib/riscv-tools.sh
source "$ROOT/scripts/lib/riscv-tools.sh"

usage() {
  echo "usage: scripts/check-no-seed-csr.sh --guest-elf PATH" >&2
}

ELF=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --guest-elf)
      if [[ $# -lt 2 || -z "${2:-}" ]]; then
        usage
        exit 2
      fi
      ELF="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "check-no-seed-csr: unknown argument: $1" >&2
      usage
      exit 2
      ;;
  esac
done

if [[ -z "$ELF" ]]; then
  echo "check-no-seed-csr: --guest-elf is required; refusing to inspect nothing" >&2
  usage
  exit 2
fi
if [[ ! -f "$ELF" || ! -r "$ELF" || ! -s "$ELF" ]]; then
  echo "check-no-seed-csr: guest ELF is missing, unreadable, or empty: $ELF" >&2
  exit 2
fi

if ! OBJDUMP="$(resolve_riscv_tool objdump)"; then
  echo "check-no-seed-csr: required RISC-V objdump is unavailable" >&2
  echo "  tried RISCV_OBJDUMP, riscv64-unknown-elf-objdump and riscv64-elf-objdump" >&2
  exit 2
fi

# A SYSTEM word has opcode 0x73.  CSR forms have a nonzero funct3, and the
# Zkr seed CSR is address 0x015 in bits 31:20.  Match exactly eight hex digits
# so compressed/system data printed by objdump cannot be mistaken for a word.
scan="$({ "$OBJDUMP" -d -j .text "$ELF" || exit $?; } | python3 -c '
import re
import sys

hits = []
for line in sys.stdin:
    match = re.match(r"\s*([0-9a-fA-F]+):\s*([0-9a-fA-F]{8})\s", line)
    if not match:
        continue
    address, word_text = match.groups()
    word = int(word_text, 16)
    if (word & 0x7f) == 0x73 and ((word >> 12) & 0x7) != 0 \
            and ((word >> 20) & 0xfff) == 0x015:
        hits.append((address, word_text))
print(len(hits))
for address, word in hits:
    print(f"{address} {word}")
')"

count="${scan%%$'\n'*}"
if [[ "$scan" == "$count" ]]; then
  details=""
else
  details="${scan#*$'\n'}"
fi

sha="$(sha256sum "$ELF" | awk '{print $1}')"
if [[ "$count" != 0 ]]; then
  echo "check-no-seed-csr: FAIL — found $count seed-CSR instruction(s) in $ELF" >&2
  echo "  guest_elf_sha256=$sha" >&2
  printf '%s\n' "$details" | sed 's/^/  seed_csr: /' >&2
  exit 1
fi

echo "check-no-seed-csr: OK — 0 seed-CSR instructions in $ELF"
echo "  guest_elf_sha256=$sha"
