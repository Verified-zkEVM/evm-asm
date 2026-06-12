#!/usr/bin/env bash
# codegen-zisk-ecrecover-precompile-check.sh -- end-to-end ECRECOVER (0x01)
# through the runtime dispatcher (.62.2.5).
#
# Bytecode stages valid_signature_1 (docs/eest-precompile-frontier.md) into
# memory via MSTOREs, CALLs the precompile, MLOADs the 32-byte output window
# and STOPs, so the recovered left-padded address is the stack top -> the
# dispatcher epilogue copies it to OUTPUT[0..32] (LE byte order, like the
# other opcode cases). Also asserts the spec's failure behavior: an invalid v
# (29) and r = 0 must leave the output window untouched (empty returndata,
# call still succeeds).
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
mkdir -p gen-out
echo "==> lake build codegen"; lake build codegen >/dev/null
echo "==> emit zisk_ecrecover_precompile_probe"
lake exe codegen --program zisk_ecrecover_precompile_probe --halt linux93 \
  -o gen-out/zisk_ecrp >/dev/null

run_case() {
  local name="$1" hash="$2" v="$3" r="$4" s="$5" expected_addr="$6"
  python3 - "$name" "$hash" "$v" "$r" "$s" <<'PY'
import subprocess, sys
name, h, v, r, s = sys.argv[1:]
def push32(hex32):
    return "0x7f, " + ", ".join("0x"+hex32[i:i+2] for i in range(0, 64, 2))
ops = []
for word, off in ((h, 0x00), (v, 0x20), (r, 0x40), (s, 0x60)):
    ops.append(push32(word))
    ops.append(f"0x60, 0x{off:02x}")   # PUSH1 offset
    ops.append("0x52")                  # MSTORE
# CALL(gas=0xffff, addr=1, value=0, in=0..128, out=0x80..0xa0)
ops.append("0x60, 0x20")  # PUSH1 outsize 32
ops.append("0x60, 0x80")  # PUSH1 outoff 0x80
ops.append("0x60, 0x80")  # PUSH1 insize 128
ops.append("0x60, 0x00")  # PUSH1 inoff 0
ops.append("0x60, 0x00")  # PUSH1 value 0
ops.append("0x60, 0x01")  # PUSH1 addr 1
ops.append("0x61, 0xff, 0xff")  # PUSH2 gas
ops.append("0xf1")        # CALL
ops.append("0x50")        # POP call status
ops.append("0x60, 0x80")  # PUSH1 0x80
ops.append("0x51")        # MLOAD output word
ops.append("0x00")        # STOP
bytecode = ", ".join(ops)
subprocess.run(["python3", "scripts/pack-bytecode.py", bytecode,
                f"gen-out/zisk_ecrp_{name}.input"], check=True)
PY
  "$ZISKEMU" -e gen-out/zisk_ecrp.elf -i "gen-out/zisk_ecrp_${name}.input" \
    -o "gen-out/zisk_ecrp_${name}.output" -n 50000000 \
    >"gen-out/zisk_ecrp_${name}.emu.log" 2>&1 </dev/null \
    || { echo "  ERROR  $name (ziskemu)"; tail -3 "gen-out/zisk_ecrp_${name}.emu.log"; return 1; }
  python3 - "$name" "$expected_addr" <<'PY'
import sys
name, expected_addr = sys.argv[1:]
out = open(f"gen-out/zisk_ecrp_{name}.output", "rb").read()[:32]
# OUTPUT[0..32] is the stack word's LE byte order = byte-reversed BE word.
word_be = bytes(12) + bytes.fromhex(expected_addr) if expected_addr else bytes(32)
expected = word_be[::-1]
if out == expected:
    print(f"  PASS   {name}")
else:
    print(f"  FAIL   {name}")
    print(f"    expected {expected.hex()}")
    print(f"    actual   {out.hex()}")
    sys.exit(1)
PY
}

fail=0
run_case valid_signature_1 \
  18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c \
  000000000000000000000000000000000000000000000000000000000000001c \
  73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f \
  eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549 \
  a94f5374fce5edbc8e2a8697c15331677e6ebf0b || fail=1
# invalid v -> empty returndata, output window untouched (zero word)
run_case invalid_v_29 \
  18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c \
  000000000000000000000000000000000000000000000000000000000000001d \
  73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f \
  eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549 \
  "" || fail=1
# r = 0 -> empty returndata
run_case zero_r \
  18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c \
  000000000000000000000000000000000000000000000000000000000000001c \
  0000000000000000000000000000000000000000000000000000000000000000 \
  eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549 \
  "" || fail=1

[[ "$fail" -eq 0 ]] && echo "==> PASS: dispatcher ECRECOVER recovers the address (and fails closed)" \
  || { echo "==> FAIL"; exit 1; }
