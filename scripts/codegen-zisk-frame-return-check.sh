#!/usr/bin/env bash
# codegen-zisk-frame-return-check.sh -- bead fhsxz.2.4.2.61.6.6.
#
# Unit-check the `frame_return` call-frame return mechanic (the iterative CALL
# descent's pop-and-resume-parent step). The `zisk_frame_return` probe
# synthesizes a per-depth save-area + call-context + depth counter and drives
# `frame_return` twice -- a depth-1->0 STOP-style return (parent restored from
# the evm_memory/evm_env labels) and a depth-2->1 REVERT-style return (parent
# restored from frame_base(1), with a returndata byte copied to the output
# window) -- then records the restored registers so we can assert the
# pc/codebase/mem/env/stack-top math and the pushed success word.
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

echo "==> emit zisk_frame_return ELF"
lake exe codegen --program zisk_frame_return --halt linux93 \
  -o gen-out/zisk_frame_return

: > gen-out/zisk_frame_return.input
"$ZISKEMU" -e gen-out/zisk_frame_return.elf \
  -i gen-out/zisk_frame_return.input -o gen-out/zisk_frame_return.output -n 100000000 \
  >gen-out/zisk_frame_return.emu.log 2>&1

# Each OUTPUT word is a little-endian u64; assert against the expected values.
python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_frame_return.output', 'rb').read()
checks = [
    ('A pc/codebase pack',              (0x222 << 32) | 0x101),
    ('A running bloom word0 (success keep)',   0x1111222233334444),
    ('A mem/env delta pack',            0),
    ('A running bloom word31 (success keep)',  0xaaaabbbbccccdddd),
    ('A stack/success pack',            (1 << 32) | 192),
    ('B running bloom word0 (revert restore)', 0x123456789abcdef0),
    ('A evm_call_depth',                0),
    ('B mem/env delta pack',            (0x38400 << 32) | 0),
    ('B running bloom word31 (revert restore)',0x0fedcba987654321),
    ('B x12 - &fr_pstack2 (netpop)',    160),
    ('B success word (REVERT)',         0),
    ('B evm_call_depth',                1),
    ('B copied returndata byte',        0xab),
    ('A cur_stack_top - &evm_stack_top',     0),
    ('B cur_stack_top - &call_frame_arena',  0x28200),
    ('A returndata size (STOP, none)',       0),
    ('B returndata size (retlen)',           4),
    ('B returndata data[0]',                 0xab),
    ('A gas refund (100+50)',                150),
    ('B gas refund (200+30)',                230),
    # nxio8.4.1: SUCCESS leaves the EIP-8037 state-gas globals unchanged;
    # REVERT restores them to the child-env snapshot (incorporate_child_on_error).
    ('A state_gas_left (success: unchanged)', 1000),
    ('A state_gas_used (success: unchanged)', 2000),
    ('B state_gas_left (revert: restored)',   555),
    ('B state_gas_used (revert: restored)',   666),
    # nxio8.4.2: SUCCESS leaves the refund accumulator; REVERT discards the child's
    # additions by restoring evm_refund_acc to the child-env snapshot.
    ('A refund_acc (success: unchanged)',     3000),
    ('B refund_acc (revert: restored)',       777),
    # nxio8.4.3: SUCCESS leaves the EIP-2929 warmth count; REVERT truncates it
    # back to the child-env snapshot (discarding the reverted child's warm keys).
    ('A warmth_count (success: unchanged)',   11),
    ('B warmth_count (revert: restored)',     44),
    # .61.9: SUCCESS commits child-frame storage/transient/event cursors into the
    # parent; REVERT leaves the parent's pre-child cursor values intact.
    ('A persistent cursor (success merge)',    12),
    ('A transient/event cursor pack',          (13 << 32) | 14),
    ('B persistent cursor (revert preserve)',  21),
    ('B transient/event cursor pack',          (22 << 32) | 23),
]
failed = False
for i, (label, exp) in enumerate(checks):
    off = i * 8
    got = struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:32s} got={got:#x} exp={exp:#x}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: frame_return pops the depth, restores the parent frame registers,"
echo "          pushes the success word, and copies returndata to the output window"
