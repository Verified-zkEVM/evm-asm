#!/usr/bin/env bash
# codegen-zisk-deposit-derivation-e2e-check.sh -- bead 8uld3.1.3 (EIP-6110).
#
# End-to-end deposit-request derivation: a synthesized M26 descriptor for a real
# DepositEvent (address/topic0 stored little-endian) + its 576-byte ABI payload ->
# materialize_log_records (LE->BE canonicalization) -> parse_deposit_requests ->
# extract_deposit_data -> the 192-byte deposit body. Then feed that execution-derived
# deposit body through requests_hash_verify with empty withdrawal/consolidation bodies
# and assert the valid derived hash accepts while a forged header hash rejects.
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

echo "==> emit zisk_deposit_derivation_e2e ELF"
lake exe codegen --program zisk_deposit_derivation_e2e --halt linux93 -o gen-out/zisk_dde

# ziskemu prepends its own 8-byte input length, so the probe reads the payload at
# INPUT+8 -- the input file is the RAW 576-byte DepositEvent ABI (no extra wrapper).
python3 - gen-out/zisk_dde.input gen-out/zisk_dde.expect <<'PY'
import sys
pubkey = bytes(range(1, 49)); wc = bytes([0xcc]) * 32
amount = (1_000_000_000).to_bytes(8, 'little'); sig = bytes(range(100, 196))
index = (7).to_bytes(8, 'little')
def field(d, s): return s.to_bytes(32, 'big') + d + bytes((-len(d)) % 32)
head = b''.join(o.to_bytes(32, 'big') for o in [160, 256, 320, 384, 512])
data = head + field(pubkey, 48) + field(wc, 32) + field(amount, 8) + field(sig, 96) + field(index, 8)
assert len(data) == 576, len(data)
open(sys.argv[1], 'wb').write(data)
open(sys.argv[2], 'wb').write(pubkey + wc + amount + sig + index)
PY

"$ZISKEMU" -e gen-out/zisk_dde.elf -i gen-out/zisk_dde.input -o gen-out/zisk_dde.output -n 5000000 \
  >gen-out/zisk_dde.emu.log 2>&1 || true

python3 - <<'PY'
import struct
d = open('gen-out/zisk_dde.output', 'rb').read()
status = struct.unpack('<Q', d[0:8])[0]
total = struct.unpack('<Q', d[8:16])[0]
body = d[16:16 + 192]
verify_zero = struct.unpack('<Q', d[208:216])[0]
verify_match = struct.unpack('<Q', d[216:224])[0]
verify_corrupt = struct.unpack('<Q', d[224:232])[0]
exp = open('gen-out/zisk_dde.expect', 'rb').read()
ok = (status == 0 and total == 192 and body == exp and verify_zero == 1 and verify_match == 0 and verify_corrupt == 1)
print(
    f"  c1_dstatus={status} c1_dlen={total} body_match={body == exp} "
    f"c1_erh_status(zero)={verify_zero} c1_erh_status(correct)={verify_match} "
    f"c1_erh_status(corrupt)={verify_corrupt}"
)
if not ok:
    print("  FAIL: derived deposit body did not yield sound requests_hash verification")
    print("  (expect status=0, total=192, body_match=True, verify(zero)=1, verify(correct)=0, verify(corrupt)=1)")
    raise SystemExit(1)
print("  PASS: descriptor -> materialize -> parse_deposit_requests -> derived deposit requests_hash accept/reject")
PY
