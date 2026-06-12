#!/usr/bin/env bash
# codegen-zisk-log-records-encode-rlp-check.sh -- verify log_records_encode_rlp
# against a python RLP reference over the dispatcher's native descriptor layout
# (.63.1.6.2.1 logs leaf).
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
echo "==> emit zisk_log_records_encode_rlp"
lake exe codegen --program zisk_log_records_encode_rlp --halt linux93 \
  -o gen-out/zisk_lrr >/dev/null

python3 - <<'PY'
import struct, subprocess, sys, os

def rlp_bytes(b):
    if len(b) == 1 and b[0] < 0x80: return b
    if len(b) < 56: return bytes([0x80+len(b)]) + b
    lb = len(b).to_bytes((len(b).bit_length()+7)//8, 'big')
    return bytes([0xb7+len(lb)]) + lb + b

def rlp_list(items):
    payload = b''.join(items)
    if len(payload) < 56: return bytes([0xc0+len(payload)]) + payload
    lb = len(payload).to_bytes((len(payload).bit_length()+7)//8, 'big')
    return bytes([0xf7+len(lb)]) + lb + payload

def descriptor(addr20, topics, ):
    d = bytearray(256)
    struct.pack_into('<Q', d, 0, len(topics))
    for i, t in enumerate(topics):
        d[32+32*i:32+32*(i+1)] = t[::-1]          # LE stack word
    addr_word = (bytes(12)+addr20)[::-1]          # LE word, low 160 bits = addr
    d[192:224] = addr_word
    return bytes(d)

cases = []
# 1. one log, 2 topics, 5-byte data
addr = bytes.fromhex('a94f5374fce5edbc8e2a8697c15331677e6ebf0b')
t1 = bytes(range(32)); t2 = bytes(reversed(range(32)))
data1 = b'\x01\x02\x03\x04\x05'
cases.append(("one_log", [(addr, [t1, t2], data1)]))
# 2. zero logs -> 0xc0
cases.append(("zero_logs", []))
# 3. two logs: 0 topics + empty data; 4 topics + 1-byte low data (bare-byte rule)
cases.append(("two_logs", [
    (addr, [], b''),
    (bytes.fromhex('00'*19+'ff'), [t1, t2, t1, t2], b'\x7f'),
]))
# 4. long data (60 bytes -> long-form string header)
cases.append(("long_data", [(addr, [t1], bytes(60))]))

fail = 0
for name, logs in cases:
    descs = b''.join(descriptor(a, ts) for a, ts, _ in logs)
    blob = b''; metas = b''
    for _, _, d in logs:
        metas += struct.pack('<QQ', len(blob), len(d)); blob += d
    payload = struct.pack('<Q', len(logs)) + descs + metas + blob
    payload += bytes(-len(payload) % 8)   # ziskemu inputs must be 8-byte multiples
    open(f'gen-out/zisk_lrr_{name}.input', 'wb').write(payload)
    r = subprocess.run([os.environ.get('ZISKEMU', os.path.expanduser('~/.zisk/bin/ziskemu')),
                        '-e', 'gen-out/zisk_lrr.elf', '-i', f'gen-out/zisk_lrr_{name}.input',
                        '-o', f'gen-out/zisk_lrr_{name}.output', '-n', '5000000'],
                       capture_output=True)
    out = open(f'gen-out/zisk_lrr_{name}.output','rb').read()
    status = struct.unpack('<Q', out[0:8])[0]
    enc_len = struct.unpack('<Q', out[8:16])[0]
    actual = out[16:16+enc_len]
    expected = rlp_list([rlp_list([rlp_bytes(a), rlp_list([rlp_bytes(t) for t in ts]), rlp_bytes(d)])
                         for a, ts, d in logs])
    if status == 0 and actual == expected:
        print(f"  PASS   {name} ({enc_len} bytes)")
    else:
        print(f"  FAIL   {name} status={status}")
        print(f"    expected {expected.hex()}")
        print(f"    actual   {actual.hex()}")
        fail = 1
sys.exit(fail)
PY
echo "==> PASS: log_records_encode_rlp matches the python RLP reference"
