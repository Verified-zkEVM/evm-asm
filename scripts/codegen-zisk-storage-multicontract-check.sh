#!/usr/bin/env bash
# codegen-zisk-storage-multicontract-check.sh -- bead fhsxz.2.4.2.61.6.7.1.
#
# Positive verification that the persistent storage log is keyed per-contract on
# env.ADDRESS (PRs #8546/#8547/#8548). The zisk_storage_multicontract probe runs
# at depth 0 with env.ADDRESS = A and a pre-seeded log holding contract B's slot 7
# (=0x99) and contract A's slot 8 (=0x77), then runs bytecode where A SLOADs slot
# 7 (must be isolated -> 0) and slot 8 (its own -> 0x77), capturing each via SSTORE
# to slots 0 and 1. The halt-time dedup (by slotKey, last-write-wins) surfaces:
#   key 1 -> 0x77 (A read its OWN slot 8)        [positive]
#   key 0 -> 0    (A did NOT read B's slot 7)    [isolation]
# A bug that ignored addrHash would surface key 0 -> 0x99.
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

echo "==> emit zisk_storage_multicontract ELF"
lake exe codegen --program zisk_storage_multicontract --halt linux93 -o gen-out/zisk_storage_multicontract

: > gen-out/zisk_storage_multicontract.input
"$ZISKEMU" -e gen-out/zisk_storage_multicontract.elf \
  -i gen-out/zisk_storage_multicontract.input -o gen-out/zisk_storage_multicontract.output -n 100000000 \
  >gen-out/zisk_storage_multicontract.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_storage_multicontract.output', 'rb').read()
def u64(off): return struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
checks = [
    ('halt_kind (OUTPUT+32)',          u64(32),  0),
    ('emitted slot count (+56)',       u64(56),  3),
    ('slot0 key (+64)',                u64(64),  1),
    ('slot0 value (+96) A-own slot 8', u64(96),  0x77),
    ('slot1 key (+128)',               u64(128), 0),
    ('slot1 value (+160) ISOLATION',   u64(160), 0),
]
failed = False
for label, got, exp in checks:
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:34s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: persistent storage is per-contract isolated — A reads its own slot 8"
echo "          (0x77) but reads 0 for contract B's slot 7 (not B's 0x99)"
