#!/usr/bin/env bash
# codegen-zisk-secp256k1-curve-check.sh -- affine secp256k1 point helper probe.
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

program="zisk_secp256k1_curve_point_ops"
echo "==> emit ${program} ELF"
lake exe codegen --program "$program" --halt linux93 -o "gen-out/${program}"

out_file="gen-out/${program}.output"
input_file="gen-out/${program}.input"
exp_file="gen-out/${program}.expected"
log_file="gen-out/${program}.emu.log"

# Static double/add probe slots (independent of the scalar input):
#   bytes 0x00..0x48  = double(G)            -> infinity flag (u64 LE) || 2G
#   bytes 0x48..0x90  = add(G,G)             -> infinity flag (u64 LE) || 2G
# Scalar-mul probe slot (driven by the 32-byte big-endian scalar input):
#   bytes 0x90..0xd8  = scalar_mul(k, G)     -> infinity flag (u64 LE) || k*G
# The ziskemu -o window is 256 bytes, so we cannot emit k=1,2,3 in one run.
# Instead we re-run the ELF once per scalar, feeding k via the guest input,
# and check the static prefix plus the per-k scalar slot each time.

python3 - "$exp_file" <<'PYSCRIPT'
import struct
import sys

point1 = bytes.fromhex(
    '79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798'
    '483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8'
)
point2 = bytes.fromhex(
    'c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5'
    '1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a'
)
point3 = bytes.fromhex(
    'f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9'
    '388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672'
)
# Static double/add prefix: bytes 0x00..0x90.
prefix = (
    struct.pack('<Q', 0) + point2 +
    struct.pack('<Q', 0) + point2
)
with open(sys.argv[1], 'wb') as f:
    f.write(prefix)
PYSCRIPT

# Per-k scalar-multiplication expected k*G points (big-endian x||y).
declare -A KPOINT
KPOINT[1]='79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8'
KPOINT[2]='c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee51ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a'
KPOINT[3]='f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672'

prefix_expected="$(xxd -p -l 144 "$exp_file" 2>/dev/null | tr -d '\n')"

for k in 1 2 3; do
  python3 -c "import sys; open(sys.argv[1],'wb').write(int(sys.argv[2]).to_bytes(32,'big'))" \
    "$input_file" "$k"
  "$ZISKEMU" -e "gen-out/${program}.elf" -i "$input_file" -o "$out_file" -n 1000000000 \
    >"$log_file" 2>&1 || true

  # Static double/add prefix (bytes 0x00..0x90) must always match.
  prefix_actual="$(xxd -p -l 144 "$out_file" 2>/dev/null | tr -d '\n')"
  if [[ "$prefix_actual" != "$prefix_expected" ]]; then
    echo "==> FAIL: secp256k1 double/add prefix mismatch (k=$k)"
    echo "    expected: $prefix_expected"
    echo "    actual:   $prefix_actual"
    echo "    ziskemu log: $log_file"
    exit 1
  fi

  # Scalar slot: infinity flag (8 bytes LE) at 0x90, then k*G at 0x98.
  flag_actual="$(xxd -p -s 144 -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  point_actual="$(xxd -p -s 152 -l 64 "$out_file" 2>/dev/null | tr -d '\n')"
  if [[ "$flag_actual" != "0000000000000000" || "$point_actual" != "${KPOINT[$k]}" ]]; then
    echo "==> FAIL: secp256k1 scalar_mul mismatch (k=$k)"
    echo "    expected flag: 0000000000000000 point: ${KPOINT[$k]}"
    echo "    actual   flag: $flag_actual point: $point_actual"
    echo "    ziskemu log: $log_file"
    exit 1
  fi
  echo "    ok: scalar_mul k=$k => ${k}G"
done

echo "==> PASS: secp256k1 point helpers and scalar multiplication match 2G, k=1=>G, k=2=>2G, k=3=>3G"
exit 0
