#!/usr/bin/env bash
# codegen-zisk-call-frame-descend-check.sh -- bead fhsxz.2.4.2.61.6.5.
#
# Unit-check the `call_frame_descend` orchestration helper (the CALL/STATICCALL
# child-frame switch). The `zisk_call_frame_descend` probe sets up a depth-0
# parent frame (regs + env with witness context) and a value-bearing CALL
# descriptor, descends, then records the full child-frame setup so we can assert
# every field the descent writes: depth bump, frame_save_area, the frame_call_ctx
# return-context, the child register rebase, the per-frame env
# (ADDRESS/CALLER/CALLVALUE/calldata/gas/codeSize), the EIP-150 forwarded gas, and
# the copied witness context.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_call_frame_descend ELF"
lake exe codegen --program zisk_call_frame_descend --halt linux93 \
  -o gen-out/zisk_call_frame_descend

: > gen-out/zisk_call_frame_descend.input
"$ZISKEMU" -e gen-out/zisk_call_frame_descend.elf \
  -i gen-out/zisk_call_frame_descend.input -o gen-out/zisk_call_frame_descend.output -n 100000000 \
  >gen-out/zisk_call_frame_descend.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_call_frame_descend.output', 'rb').read()
checks = [
    ('evm_call_depth after',            1),
    ('frame_save_area[0].pc',           0x500),
    ('frame_save_area[0].codebase',     0x600),
    ('ctx[1].parent_x12 - &pstack',     0),
    ('ctx[1].outOff_abs - &pmem',       0x100),
    ('ctx[1].outSize',                  0x20),
    ('ctx[1].netPopBytes',              192),
    ('child x13 - &call_frame_arena',   0),
    ('child x20 - &arena (frameEnvOff)',0x28400),
    ('child x21 - &code (callee base)', 0),
    ('child x10 - &code (child PC)',    0),
    ('child env.ADDRESS (to)',          0xbb),
    ('child env.CALLER (parent addr)',  0xaa),
    ('child env.CALLVALUE (value)',     0x7),
    ('child env.callDataPtr - &pmem',   0x40),
    ('child env.callDataLen',           0x20),
    ('child env.gasRemaining (EIP-150)',3300),
    ('child env.codeSize',              0x33),
    ('child env witness.state ptr',     0x592),
]
failed = False
for i, (label, exp) in enumerate(checks):
    off = i * 8
    got = struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:34s} got={got:#x} exp={exp:#x}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: call_frame_descend performs the full CALL child-frame switch"
echo "          (depth, save-area, return-context, regs, env, gas, code, witness)"
