#!/usr/bin/env bash
# codegen-zisk-bal-recipient-field-empty-check.sh -- bead bmvmx.1.6.3 (nonce/code slice).
#
# Locks the soundness-critical list-emptiness contract the verdict relies on: for a *list*
# RLP item, rlp_list_nth_item returns the FULL encoded size (incl. the 1-byte prefix), so an
# empty list 0xc0 yields len==1 (NOT 0). block_verdict rejects a recipient's BAL nonce_changes
# (item 4) / code_changes (item 5) only when len>1; an empty-list len of 0 would mass-false-
# reject every contract recipient. The probe hand-builds AccountChanges and asserts:
#   nth(empty, 4) status -> 0 ; empty nonce/code len -> 1 ; non-empty nonce len -> 2 (>1).
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_bal_recipient_field_empty ELF"
lake exe codegen --program zisk_bal_recipient_field_empty --halt linux93 -o gen-out/zisk_bal_recipient_field_empty

: > gen-out/zisk_bal_recipient_field_empty.input
"$ZISKEMU" -e gen-out/zisk_bal_recipient_field_empty.elf \
  -i gen-out/zisk_bal_recipient_field_empty.input -o gen-out/zisk_bal_recipient_field_empty.output -n 100000000 \
  >gen-out/zisk_bal_recipient_field_empty.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_bal_recipient_field_empty.output', 'rb').read()
def u64(off): return struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
checks = [
    ('nth(empty,4) status',          u64(0),  0),
    ('empty nonce_changes len',      u64(8),  1),
    ('empty code_changes len',       u64(16), 1),
    ('non-empty nonce_changes len',  u64(24), 2),
]
failed = False
for label, got, exp in checks:
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:30s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: empty BAL nonce/code list -> len 1 (no reject); non-empty -> len>1 (reject)"
