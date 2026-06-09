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
    ('A x10 (parent_pc+1)',        0x101),
    ('A x21 (parent codebase)',    0x222),
    ('A x13 - &evm_memory',        0),
    ('A x20 - &evm_env',           0),
    ('A x12 - &fr_pstack (netpop)',192),
    ('A success word',             1),
    ('A evm_call_depth',           0),
    ('B x13 - &call_frame_arena',  0),
    ('B x20 - &arena (frameEnvOff)', 0x28400),
    ('B x12 - &fr_pstack2 (netpop)', 160),
    ('B success word (REVERT)',    0),
    ('B evm_call_depth',           1),
    ('B copied returndata byte',   0xab),
    ('A cur_stack_top - &evm_stack_top',     0),
    ('B cur_stack_top - &call_frame_arena',  0x18200),
    ('A returndata size (STOP, none)',       0),
    ('B returndata size (retlen)',           4),
    ('B returndata data[0]',                 0xab),
    ('A gas refund (100+50)',                150),
    ('B gas refund (200+30)',                230),
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
