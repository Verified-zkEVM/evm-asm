#!/usr/bin/env bash
# codegen-zisk-tx-access-list-span-check.sh
#
# Drive tx_access_list_span over legacy and typed transactions. The helper must
# return the whole encoded access_list span for typed txs and an explicit
# no-access-list status for legacy transactions.
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

mkdir -p gen-out
echo "==> lake build codegen"
lake build codegen >/dev/null
echo "==> emit zisk_tx_access_list_span ELF"
lake exe codegen --program zisk_tx_access_list_span --halt linux93 \
  -o gen-out/zisk_tx_access_list_span

run_case() {
  local name="$1" kind="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_tx_access_list_span_${name}.input"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_access_list_span_${name}.expected"
  uv run --directory execution-specs --quiet python3 - "$kind" "$in_file" "$exp_file" <<'PYVEC'
import rlp, struct, sys
kind, in_path, exp_path = sys.argv[1:4]
addr = bytes.fromhex("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
slot = bytes.fromhex("11" + "00" * 31)
access_list = [[addr, [slot]]]
access_list_rlp = rlp.encode(access_list)

def write(tx: bytes, exp):
    with open(in_path, "wb") as f:
        f.write(struct.pack("<Q", len(tx)))
        f.write(tx)
        pad = (-(8 + len(tx))) % 8
        if pad:
            f.write(b"\x00" * pad)
    with open(exp_path, "w") as f:
        f.write(" ".join(str(x) for x in exp))

def typed(type_byte: int, fields):
    inner = rlp.encode(fields)
    tx = bytes([type_byte]) + inner
    off = 1 + inner.index(access_list_rlp)
    return tx, [0, off, len(access_list_rlp), access_list_rlp[0]]

if kind == "legacy":
    tx = rlp.encode([0, 1, 21000, addr, 0, b"", 27, 1, 1])
    write(tx, [1, 0, 0, 0])
elif kind == "type1":
    tx, exp = typed(1, [1, 0, 7, 50000, addr, 0, b"", access_list, 0, 1, 1])
    write(tx, exp)
elif kind == "type2":
    tx, exp = typed(2, [1, 0, 2, 9, 50000, addr, 0, b"", access_list, 0, 1, 1])
    write(tx, exp)
elif kind == "type3":
    blob_hash = bytes.fromhex("01" + "22" * 31)
    tx, exp = typed(3, [1, 0, 2, 9, 50000, addr, 0, b"", access_list, 3, [blob_hash], 0, 1, 1])
    write(tx, exp)
elif kind == "type4":
    tx, exp = typed(4, [1, 0, 2, 9, 50000, addr, 0, b"", access_list, [], 0, 1, 1])
    write(tx, exp)
elif kind == "malformed_type2":
    write(bytes([2, 0x80]), [2, 0, 0, 0])
else:
    raise SystemExit("bad kind " + kind)
PYVEC
  local out_file="$REPO_ROOT/gen-out/zisk_tx_access_list_span_${name}.output"
  "$ZISKEMU" -e gen-out/zisk_tx_access_list_span.elf -i "$in_file" -o "$out_file" -n 200000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_access_list_span_${name}.emu.log" 2>&1 || true
  python3 - "$out_file" "$exp_file" "$name" <<'PYCHK'
import struct, sys
out, exp_path, name = sys.argv[1:4]
d = open(out, "rb").read()
def u(o): return struct.unpack("<Q", d[o:o+8])[0]
got = [u(0), u(8), u(16), u(24)]
exp = [int(x) for x in open(exp_path).read().split()]
if got != exp:
    print(f"  {name:<16} FAIL got={got} exp={exp}")
    raise SystemExit(1)
print(f"  {name:<16} OK   status={got[0]} off={got[1]} len={got[2]}")
PYCHK
}

FAILED=0
run_case "legacy"          legacy          || FAILED=1
run_case "type1"           type1           || FAILED=1
run_case "type2"           type2           || FAILED=1
run_case "type3"           type3           || FAILED=1
run_case "type4"           type4           || FAILED=1
run_case "malformed_type2" malformed_type2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_access_list_span locates typed access_list spans and fails conservatively"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
