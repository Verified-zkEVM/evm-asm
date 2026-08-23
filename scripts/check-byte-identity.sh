#!/usr/bin/env bash
# check-byte-identity.sh — assemble two GNU-as fragments and compare their
# .text bytes.  The byte gate for proof-first (DCode) ports: the previously
# hand-written label-form assembly and the `emitProgram` rendering of the
# verified program must assemble to IDENTICAL bytes before the emitted
# string may be replaced (docs/dcode-porting-playbook.md, step 6).
#
# Usage:
#   scripts/check-byte-identity.sh OLD.s NEW.s
#   scripts/check-byte-identity.sh OLD.s -          # NEW body on stdin
#
# The stdin form is convenient for piping the pinned `#guard` emission
# string: paste the exact string (real newlines, no surrounding quotes);
# a leading "label:" line is NOT added automatically — include one in
# both fragments if the routine is branched into by symbol.
#
# Exit status: 0 = byte-identical, 1 = mismatch or assembly failure.
set -u

AS="${RISCV_AS:-riscv64-unknown-elf-as}"
OBJCOPY="${RISCV_OBJCOPY:-riscv64-unknown-elf-objcopy}"
MARCH="${RISCV_MARCH:-rv64im}"

if [ $# -ne 2 ]; then
  sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'
  exit 1
fi

command -v "$AS" >/dev/null || { echo "error: $AS not found (set RISCV_AS)"; exit 1; }
command -v "$OBJCOPY" >/dev/null || { echo "error: $OBJCOPY not found (set RISCV_OBJCOPY)"; exit 1; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cp "$1" "$tmp/old.s" || exit 1
if [ "$2" = "-" ]; then
  cat > "$tmp/new.s"
else
  cp "$2" "$tmp/new.s" || exit 1
fi

for side in old new; do
  if ! "$AS" -march="$MARCH" -o "$tmp/$side.o" "$tmp/$side.s"; then
    echo "error: assembling $side fragment failed"
    exit 1
  fi
  "$OBJCOPY" -O binary --only-section=.text "$tmp/$side.o" "$tmp/$side.bin"
done

if cmp -s "$tmp/old.bin" "$tmp/new.bin"; then
  echo "BYTE-IDENTICAL ($(wc -c < "$tmp/old.bin") bytes)"
  exit 0
else
  echo "MISMATCH:"
  echo "--- old ---"; xxd "$tmp/old.bin"
  echo "--- new ---"; xxd "$tmp/new.bin"
  cmp "$tmp/old.bin" "$tmp/new.bin" || true
  exit 1
fi
