#!/usr/bin/env bash
# codegen-zisk-materialize-log-records-check.sh -- bead 8uld3.1.2 (EIP-6110).
#
# materialize_log_records bridges the M26 evm_event_logs descriptors + the persistent
# evm_log_data full-data buffer (8uld3.1a) into the CANONICAL big-endian log-record
# array parse_deposit_requests consumes: it copies the packed descriptor's canonical-BE
# address (+8), byte-reverses topic0 (+32) to Ethereum BE, and copies the full data verbatim.
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

echo "==> emit zisk_materialize_log_records ELF"
lake exe codegen --program zisk_materialize_log_records --halt linux93 -o gen-out/zisk_mlr

python3 -c "import struct; open('gen-out/zisk_mlr.input','wb').write(struct.pack('<Q',0))"

"$ZISKEMU" -e gen-out/zisk_mlr.elf -i gen-out/zisk_mlr.input -o gen-out/zisk_mlr.output -n 2000000 \
  >gen-out/zisk_mlr.emu.log 2>&1 || true

python3 - <<'PY'
import struct
d = open('gen-out/zisk_mlr.output','rb').read()
total = struct.unpack('<Q', d[0:8])[0]
r0 = d[8:8+88]
r1 = d[96:96+80]
ok = (
    total == 168
    and r0[0:20] == bytes(range(1,21))                  # addr0 BE 01..14
    and struct.unpack('<Q', r0[32:40])[0] == 2          # topic_count
    and r0[40:72] == bytes(range(1,33))                 # topic0 BE 01..20
    and struct.unpack('<Q', r0[72:80])[0] == 4          # data_len
    and r0[80:84] == b'DEPO'                            # data verbatim
    and r1[0:20] == bytes(range(21,41))                 # addr1 BE 15..28
    and struct.unpack('<Q', r1[32:40])[0] == 1
    and r1[40:72] == bytes(range(33,65))                # topic0 BE 21..40
    and struct.unpack('<Q', r1[72:80])[0] == 0
)
print(f"  total={total} rec0.addr={r0[0:20].hex()} rec0.topic0={r0[40:72].hex()} data={r0[80:84]!r}")
print(f"  rec1.addr={r1[0:20].hex()} rec1.topic0={r1[40:72].hex()}")
if not ok:
    print("  FAIL: canonicalization incorrect")
    raise SystemExit(1)
print("  PASS: address copied BE, topic0 reversed LE->BE, full data copied, canonical layout")
PY
