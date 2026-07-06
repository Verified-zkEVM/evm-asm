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
    ('child x20 - &arena (frameEnvOff)',0x38400),
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
    ('evm_cur_stack_top - &arena',      0x28200),
    ('evm_cur_stack_low - &arena',      0x20200),
    ('parent gas after transfer+cost',  90000),
    # nxio8.4.1: descend snapshots the parent's pre-child state gas into the child
    # env at +624/632 so frame_return can restore it on a child REVERT.
    ('child env state_gas_left snapshot', 12345),
    ('child env state_gas_used snapshot', 67890),
    # nxio8.4.2: descend also snapshots the EIP-3529 refund accumulator.
    ('child env refund_acc snapshot',     24680),
    # nxio8.4.3: descend also snapshots the EIP-2929 storage-warmth count.
    ('child env warmth_count snapshot',   5),
    ('running bloom checkpoint[0]',       0x1111222233334444),
    ('running bloom checkpoint[31]',      0xaaaabbbbccccdddd),
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

echo "==> emit zisk_set_call_env ELF"
lake exe codegen --program zisk_set_call_env --halt linux93 \
  -o gen-out/zisk_set_call_env

: > gen-out/zisk_set_call_env.input
"$ZISKEMU" -e gen-out/zisk_set_call_env.elf \
  -i gen-out/zisk_set_call_env.input -o gen-out/zisk_set_call_env.output -n 100000000 \
  >gen-out/zisk_set_call_env.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open("gen-out/zisk_set_call_env.output", "rb").read()
checks = [
    ("mode0 ADDRESS", 0xbb), ("mode0 CALLER", 0xaa), ("mode0 CALLVALUE", 0xdd),
    ("mode1 ADDRESS", 0xbb), ("mode1 CALLER", 0xaa), ("mode1 CALLVALUE", 0),
    ("mode2 ADDRESS", 0xaa), ("mode2 CALLER", 0xaa), ("mode2 CALLVALUE", 0xdd),
    ("mode3 ADDRESS", 0xaa), ("mode3 CALLER", 0xcc), ("mode3 CALLVALUE", 0xee),
    ("mode0 isStatic", 7), ("mode1 isStatic", 1),
    ("mode2 isStatic", 7), ("mode3 isStatic", 7),
]
failed = False
for i, (label, exp) in enumerate(checks):
    off = i * 8
    got = struct.unpack("<Q", data[off:off+8])[0] if off + 8 <= len(data) else None
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:34s} got={got:#x} exp={exp:#x}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: call_frame_descend performs the full CALL child-frame switch"
echo "          (depth, save-area, return-context, regs, env, gas, code, witness)"
