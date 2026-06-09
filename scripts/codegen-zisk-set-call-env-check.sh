#!/usr/bin/env bash
# codegen-zisk-set-call-env-check.sh -- bead fhsxz.2.4.2.61.7.1.
#
# Focused check for call_frame_set_call_env's four message-call modes
# (0=CALL, 1=STATICCALL, 2=CALLCODE, 3=DELEGATECALL). The probe runs the helper
# with parent markers (ADDRESS=0xaa, CALLER=0xcc, CALLVALUE=0xee), to=0xbb,
# value=0xdd into four child env buffers and records each child's ADDRESS /
# CALLER / CALLVALUE low limb. Asserts the per-mode address roles from
# execution-specs vm/instructions/system.py.
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

echo "==> emit zisk_set_call_env ELF"
lake exe codegen --program zisk_set_call_env --halt linux93 -o gen-out/zisk_set_call_env

: > gen-out/zisk_set_call_env.input
"$ZISKEMU" -e gen-out/zisk_set_call_env.elf \
  -i gen-out/zisk_set_call_env.input -o gen-out/zisk_set_call_env.output -n 100000000 \
  >gen-out/zisk_set_call_env.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_set_call_env.output', 'rb').read()
checks = [
    ('CALL ADDRESS (to)',            0xbb),
    ('CALL CALLER (parent addr)',    0xaa),
    ('CALL CALLVALUE (value)',       0xdd),
    ('STATICCALL ADDRESS (to)',      0xbb),
    ('STATICCALL CALLER (parent)',   0xaa),
    ('STATICCALL CALLVALUE (0)',     0),
    ('CALLCODE ADDRESS (self)',      0xaa),
    ('CALLCODE CALLER (parent)',     0xaa),
    ('CALLCODE CALLVALUE (value)',   0xdd),
    ('DELEGATECALL ADDRESS (self)',  0xaa),
    ('DELEGATECALL CALLER (inherit)',0xcc),
    ('DELEGATECALL CALLVALUE (inh)', 0xee),
]
failed = False
for i, (label, exp) in enumerate(checks):
    off = i * 8
    got = struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:30s} got={got:#x} exp={exp:#x}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: call_frame_set_call_env sets the correct ADDRESS/CALLER/CALLVALUE"
echo "          roles for CALL / STATICCALL / CALLCODE / DELEGATECALL"
