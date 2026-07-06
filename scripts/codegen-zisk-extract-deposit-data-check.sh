#!/usr/bin/env bash
# codegen-zisk-extract-deposit-data-check.sh -- bead 8uld3.1 (EIP-6110).
#
# extract_deposit_data strips the Solidity ABI framing from a 576-byte DepositEvent
# payload and returns pubkey(48)||wc(32)||amount(8)||sig(96)||index(8) = 192 bytes,
# rejecting any non-canonical length / offset / size.
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

echo "==> emit zisk_extract_deposit_data ELF"
lake exe codegen --program zisk_extract_deposit_data --halt linux93 -o gen-out/zisk_extract_deposit_data

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <expected_status> [expected_192_hex]
run_case() {
  local name="$1" mode="$2" exp="$3" exphex="${4:-}"
  local in_file="$REPO_ROOT/gen-out/zisk_edd_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_edd_${name}.output"

  MODE="$mode" python3 -c "
import struct, sys, os
mode = os.environ['MODE']
pubkey = bytes(range(1,49))                 # 48
wc     = bytes([0xcc])*32                   # 32
amount = (1000000000).to_bytes(8,'little')  # 8 (gwei, LE per spec)
sig    = bytes(range(100,196))              # 96
index  = (7).to_bytes(8,'little')           # 8

def field(data, size):
    pad = (-len(data)) % 32
    return size.to_bytes(32,'big') + data + bytes(pad)

offsets = [160,256,320,384,512]
sizes   = [48,32,8,96,8]
if mode == 'bad_offset':   offsets[0] = 161
if mode == 'bad_size':     sizes[0]   = 47   # pubkey size word wrong (data still 48B)
head = b''.join(o.to_bytes(32,'big') for o in offsets)
body = field(pubkey, sizes[0]) + field(wc, sizes[1]) + field(amount, sizes[2]) \
     + field(sig, sizes[3]) + field(index, sizes[4])
data = head + body
assert len(data) == 576, len(data)

dlen = len(data)
if mode == 'bad_length': dlen = 568        # pass a wrong length to the helper

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', dlen))       # +8  data length (to the helper)
    f.write(data)                          # +16 data
    total = 8 + len(data)
    pad = (-total) % 8
    if pad: f.write(b'\x00'*pad)

# expected 192-byte deposit for the valid case
exp = (pubkey + wc + amount + sig + index)
sys.stderr.write(exp.hex())
" "$in_file" 2>"$REPO_ROOT/gen-out/zisk_edd_${name}.exp"

  "$ZISKEMU" -e gen-out/zisk_extract_deposit_data.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_edd_${name}.emu.log" 2>&1 || true

  local status; status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$exp').to_bytes(8,'little').hex())")"
  if [[ "$status" != "$exp_le" ]]; then
    printf "  %-16s FAIL status=0x%s expected=%s\n" "$name" "$status" "$exp"
    return 1
  fi
  if [[ "$exp" == "0" ]]; then
    local got; got="$(dd if="$out_file" bs=1 skip=8 count=192 2>/dev/null | xxd -p | tr -d '\n')"
    local want; want="$(cat "$REPO_ROOT/gen-out/zisk_edd_${name}.exp")"
    if [[ "$got" != "$want" ]]; then
      printf "  %-16s FAIL deposit bytes mismatch\n    got=%s\n    exp=%s\n" "$name" "$got" "$want"
      return 1
    fi
    printf "  %-16s OK   status=0, 192B deposit matches\n" "$name"
  else
    printf "  %-16s OK   status=%s (rejected)\n" "$name" "$exp"
  fi
  return 0
}

FAILED=0
run_case "valid"       valid      0 || FAILED=1
run_case "bad_length"  bad_length 1 || FAILED=1
run_case "bad_offset"  bad_offset 1 || FAILED=1
run_case "bad_size"    bad_size   1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: extract_deposit_data unframes a canonical DepositEvent and rejects"
  echo "          bad length / offset / size"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
