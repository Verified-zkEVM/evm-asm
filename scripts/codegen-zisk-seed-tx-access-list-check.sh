#!/usr/bin/env bash
# codegen-zisk-seed-tx-access-list-check.sh
#
# Drive seed_tx_access_list over EIP-2930/1559 access lists and assert it seeds
# every (address, storage_key) pair into the runtime EIP-2929 storage-warmth set
# (evm_storage_access_keys / evm_storage_access_count). The 32-byte warm-set
# token is the address big-endian, left-aligned (env.ADDRESS format).
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
echo "==> emit zisk_seed_tx_access_list ELF"
lake exe codegen --program zisk_seed_tx_access_list --halt linux93 \
  -o gen-out/zisk_seed_tx_access_list

# run_case <name> <kind> <expected_status> <expected_count> <exp_tok0> <exp_slot0> <exp_tok19>
run_case() {
  local name="$1" kind="$2" est="$3" ecnt="$4" et0="$5" es0="$6" et19="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_seed_tx_access_list_${name}.input"
  uv run --directory execution-specs --quiet python3 - "$kind" "$in_file" <<'PYVEC'
import rlp, struct, sys
kind, path = sys.argv[1:3]
def w(al):
    with open(path,"wb") as f:
        f.write(struct.pack("<Q", len(al))); f.write(al)
        p=(-(8+len(al)))%8
        if p: f.write(b"\x00"*p)
if kind == "empty":
    w(rlp.encode([]))
elif kind == "one_entry_two_slots":
    addr=bytes([0xaa]*20); s1=bytes([0x11])+bytes(31); s2=bytes([0x22])+bytes(31)
    w(rlp.encode([[addr,[s1,s2]]]))
elif kind == "two_entries":
    a1=bytes([0xaa]*20); a2=bytes([0xbb]*20)
    # distinct slots so each (token, slot) is a unique warm-set key (the seed is
    # idempotent — identical pairs dedupe).
    s1=bytes([0x11])+bytes(31); s2=bytes([0x22])+bytes(31); s3=bytes([0x33])+bytes(31)
    s4=bytes([0x44])+bytes(31)
    w(rlp.encode([[a1,[s1,s2,s3]],[a2,[s4]]]))   # 3 + 1 = 4 distinct keys
elif kind == "entry_no_slots":
    w(rlp.encode([[bytes([0xaa]*20),[]]]))   # 0 slots
else:
    raise SystemExit("bad kind "+kind)
PYVEC
  local out_file="$REPO_ROOT/gen-out/zisk_seed_tx_access_list_${name}.output"
  "$ZISKEMU" -e gen-out/zisk_seed_tx_access_list.elf -i "$in_file" -o "$out_file" -n 200000000 \
    >"$REPO_ROOT/gen-out/zisk_seed_tx_access_list_${name}.emu.log" 2>&1 || true
  python3 - "$out_file" "$name" "$est" "$ecnt" "$et0" "$es0" "$et19" <<'PYCHK'
import struct, sys
out, name, est, ecnt, et0, es0, et19 = sys.argv[1:8]
d=open(out,"rb").read()
def u(o): return struct.unpack("<Q", d[o:o+8])[0]
got=[u(0),u(8),u(16),u(24),u(32)]; exp=[int(est),int(ecnt),int(et0,0),int(es0,0),int(et19,0)]
labels=["status","count","tok0","slot0","tok19"]
ok = got[0]==exp[0] and got[1]==exp[1]
# byte fields only meaningful when at least one slot was seeded
if exp[1] > 0:
    ok = ok and got[2]==exp[2] and got[3]==exp[3] and got[4]==exp[4]
if not ok:
    print(f"  {name:<22} FAIL got={got} exp={exp}"); raise SystemExit(1)
print(f"  {name:<22} OK   status={got[0]} count={got[1]}")
PYCHK
}

FAILED=0
run_case "empty"              empty               0 0 0    0    0    || FAILED=1
run_case "one_entry_two_slots" one_entry_two_slots 0 2 0xaa 0x11 0xaa || FAILED=1
run_case "two_entries"        two_entries         0 4 0xaa 0x11 0xaa || FAILED=1
run_case "entry_no_slots"     entry_no_slots      0 0 0    0    0    || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: seed_tx_access_list seeds every (address, slot) of the access list into the EIP-2929 warm set"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
