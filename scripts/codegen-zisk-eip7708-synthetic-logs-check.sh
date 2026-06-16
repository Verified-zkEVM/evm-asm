#!/usr/bin/env bash
# codegen-zisk-eip7708-synthetic-logs-check.sh -- EIP-7708 synthetic logs.
#
# Verifies the helper-generated Transfer and Burn descriptors used by the
# receipt/log path. Descriptor topics use the runtime event-log word order;
# synthetic amount data is canonical big-endian, as in execution-specs.
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

echo "==> emit zisk_eip7708_synthetic_logs ELF"
lake exe codegen --program zisk_eip7708_synthetic_logs --halt linux93 \
  -o gen-out/zisk_eip7708_synthetic_logs

REPO_ROOT="$(pwd)"

python3 - <<'MAKE_INPUTS'
from pathlib import Path
import struct
root = Path('gen-out')
for name, mode in [('transfer', 0), ('burn', 1), ('zero', 2)]:
    with open(root / f'zisk_eip7708_synthetic_logs_{name}.input', 'wb') as f:
        f.write(struct.pack('<Q', 1))
        f.write(bytes([mode]))
        f.write(bytes(7))
MAKE_INPUTS

python3 - <<'MAKE_EXPECTED'
from pathlib import Path
import struct

TRANSFER_TOPIC = bytes.fromhex('ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef')
BURN_TOPIC = bytes.fromhex('cc16f5dbb4873280815c1ee09dbd06736cffcc184412cf7a71a0fdb75d397ca5')

def word_from_be32(value: bytes) -> bytes:
    return value[::-1]

def word_from_address_byte(byte: int) -> bytes:
    return bytes([byte]) * 20 + bytes(12)

def descriptor(topic_count: int, topics: list[bytes], amount_word: bytes) -> bytes:
    d = bytearray(256)
    struct.pack_into('<Q', d, 0, topic_count)
    struct.pack_into('<Q', d, 16, 32)
    struct.pack_into('<Q', d, 24, 32)
    for i, topic in enumerate(topics):
        d[32 + 32 * i : 64 + 32 * i] = topic
    d[160:192] = amount_word[::-1]
    d[192:224] = bytes.fromhex('ff' * 19 + 'fe') + bytes(12)
    return bytes(d)

sender = word_from_address_byte(0x11)
recipient = word_from_address_byte(0x22)
account = word_from_address_byte(0x33)
amount_transfer = bytes.fromhex(
    '11223344556677880099aabbccddeeffefcdab89674523011032547698badcfe'
)
amount_burn = struct.pack('<Q', 5) + bytes(24)

root = Path('gen-out')
(root / 'zisk_eip7708_synthetic_logs_transfer.expected').write_bytes(
    descriptor(3, [word_from_be32(TRANSFER_TOPIC), sender, recipient], amount_transfer)
)
(root / 'zisk_eip7708_synthetic_logs_burn.expected').write_bytes(
    descriptor(2, [word_from_be32(BURN_TOPIC), account], amount_burn)
)
(root / 'zisk_eip7708_synthetic_logs_zero.expected').write_bytes(
    struct.pack('<Q', 0) + struct.pack('<Q', 0) + bytes(240)
)
MAKE_EXPECTED

FAILED=0
for name in transfer burn zero; do
  in_file="$REPO_ROOT/gen-out/zisk_eip7708_synthetic_logs_${name}.input"
  out_file="$REPO_ROOT/gen-out/zisk_eip7708_synthetic_logs_${name}.output"
  exp_file="$REPO_ROOT/gen-out/zisk_eip7708_synthetic_logs_${name}.expected"

  "$ZISKEMU" -e gen-out/zisk_eip7708_synthetic_logs.elf     -i "$in_file" -o "$out_file" -n 1000000     >"$REPO_ROOT/gen-out/zisk_eip7708_synthetic_logs_${name}.emu.log" 2>&1 || true

  actual="$(xxd -p -l 256 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 256 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-12s OK
" "$name"
  else
    printf "  %-12s FAIL
expected: %s
actual:   %s
" "$name" "$expected" "$actual"
    echo "emulator log: gen-out/zisk_eip7708_synthetic_logs_${name}.emu.log"
    FAILED=1
  fi
done

if [[ "$FAILED" -ne 0 ]]; then
  echo "==> FAIL: EIP-7708 synthetic log descriptors differ"
  exit 1
fi

echo "==> PASS: EIP-7708 synthetic Transfer/Burn descriptors match execution-specs shape"
