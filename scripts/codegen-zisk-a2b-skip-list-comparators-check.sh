#!/usr/bin/env bash
# codegen-zisk-a2b-skip-list-comparators-check.sh -- bead bmvmx.5.5.1.2.1.1.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
mkdir -p gen-out
REPO_ROOT="$(pwd)"
echo "==> lake build codegen"; lake build codegen
for program in zisk_bal_all_accounts_storage_consistent_skip_list zisk_bal_all_accounts_tuple_sequences_consistent_skip_list; do
  echo "==> emit $program ELF"
  lake exe codegen --program "$program" --halt linux93 -o "gen-out/$program"
done

run_storage() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/a2b_storage_${name}.input"
  local out_file="$REPO_ROOT/gen-out/a2b_storage_${name}.output"
  MODE="$mode" python3 -c "
import os, struct, sys
mode = os.environ[\"MODE\"]
R1 = bytes([0xBB]*20); R2 = bytes([0xCC]*20); C = bytes(range(1,21))
def account_changes(addr20):
    blob = bytes([0xcf,0xc8,0x07,0xc6,0xc2,0x80,0x11,0xc2,0x01,0x22,0xc5,0x09,0xc3,0xc2,0x80,0x33])
    payload = bytes([0x94]) + addr20 + blob + bytes([0xc0,0xc0,0xc0,0xc0])
    return bytes([0xf8, len(payload)]) + payload
def rlp_list(items):
    inner = b\"\".join(items)
    return bytes([0xf8, len(inner)]) + inner if len(inner) > 55 else bytes([0xc0+len(inner)]) + inner
def callee_key(addr20): return addr20[::-1] + bytes(12)
def log_entry(addrhash32, slot, cur): return addrhash32 + slot.to_bytes(32, \"little\") + bytes(32) + cur.to_bytes(32, \"little\")
ck = callee_key(C)
if mode == \"one_skip_ok\":
    skips = [R1]; accts = [account_changes(R1), account_changes(C)]; log = [log_entry(ck,7,0x22), log_entry(ck,9,0x33)]
elif mode == \"two_skip_ok\":
    skips = [R1, R2]; accts = [account_changes(R1), account_changes(R2), account_changes(C)]; log = [log_entry(ck,7,0x22), log_entry(ck,9,0x33)]
elif mode == \"callee_bad\":
    skips = [R1, R2]; accts = [account_changes(R1), account_changes(R2), account_changes(C)]; log = [log_entry(ck,7,0x99), log_entry(ck,9,0x33)]
else:
    raise ValueError(mode)
bal = rlp_list(accts); skip = b\"\".join(x + bytes(12) for x in skips); logb = b\"\".join(log)
with open(sys.argv[1], \"wb\") as f:
    f.write(struct.pack(\"<Q\", len(bal))); f.write(struct.pack(\"<Q\", len(log))); f.write(struct.pack(\"<Q\", len(skips)))
    f.write(skip); f.write(logb); f.write(bal)
    total = 24 + len(skip) + len(logb) + len(bal); f.write(bytes((-total) % 8))
" "$in_file"
  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_storage_consistent_skip_list.elf -i "$in_file" -o "$out_file" -n 100000000 >"gen-out/a2b_storage_${name}.emu.log" 2>&1 || true
  local st; st=$(python3 -c "d=open(\"$out_file\",\"rb\").read(); print(int.from_bytes(d[:8],\"little\"))")
  [[ "$st" == "$exp" ]] && printf "  storage %-12s OK   status=%s\n" "$name" "$st" || { printf "  storage %-12s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1; }
}

run_tuple() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/a2b_tuple_${name}.input"
  local out_file="$REPO_ROOT/gen-out/a2b_tuple_${name}.output"
  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import os, rlp, struct, sys
mode = os.environ[\"MODE\"]
def b32(n): return n.to_bytes(32, \"big\")
def b32le(n): return n.to_bytes(32, \"little\")
R1 = bytes([0xBB]*20); R2 = bytes([0xCC]*20); C = bytes(range(1,21))
ckey = C[::-1] + bytes(12); K = b32(7); O = b32le(0)
def entry(ah, sk_n, cur_n, o=O): return ah + b32le(sk_n) + o + b32le(cur_n)
rows = [(entry(ckey,7,0x11),1),(entry(ckey,7,0x33),3)]
sys_rows = []
callee_sc = [[K, [[1,b32(0x11)],[3,b32(0x33)]]]]; skipped_sc = [[K, [[1,b32(0xDEAD)],[2,b32(0xBEEF)]]]]
if mode == \"one_skip_ok\":
    skips = [R1]; accounts = [[R1, skipped_sc, [], [], [], []], [C, callee_sc, [], [], [], []]]
elif mode == \"two_skip_ok\":
    skips = [R1, R2]; accounts = [[R1, skipped_sc, [], [], [], []], [R2, skipped_sc, [], [], [], []], [C, callee_sc, [], [], [], []]]
elif mode == \"callee_bad\":
    skips = [R1, R2]; bad_sc = [[K, [[1,b32(0x11)],[3,b32(0x99)]]]]; accounts = [[R1, skipped_sc, [], [], [], []], [R2, skipped_sc, [], [], [], []], [C, bad_sc, [], [], [], []]]
elif mode == \"system_tuple_ok\":
    skips = [R1, R2]; system_sc = [[K, [[0,b32(0x44)]]]]; accounts = [[R1, skipped_sc, [], [], [], []], [R2, skipped_sc, [], [], [], []], [C, system_sc, [], [], [], []]]; rows = []; sys_rows = [entry(ckey,7,0x44)]
elif mode == \"system_tuple_bad\":
    skips = [R1, R2]; system_sc = [[K, [[0,b32(0x45)]]]]; accounts = [[R1, skipped_sc, [], [], [], []], [R2, skipped_sc, [], [], [], []], [C, system_sc, [], [], [], []]]; rows = []; sys_rows = [entry(ckey,7,0x44)]
elif mode == \"mixed_tuple_ok\":
    skips = [R1, R2]; mixed_sc = [[K, [[0,b32(0x44)],[2,b32(0x99)]]]]; accounts = [[R1, skipped_sc, [], [], [], []], [R2, skipped_sc, [], [], [], []], [C, mixed_sc, [], [], [], []]]; rows = [(entry(ckey,7,0x99,b32le(0x44)),2)]; sys_rows = [entry(ckey,7,0x44)]
elif mode == \"mixed_tuple_bad_system\":
    skips = [R1, R2]; mixed_sc = [[K, [[0,b32(0x45)],[2,b32(0x99)]]]]; accounts = [[R1, skipped_sc, [], [], [], []], [R2, skipped_sc, [], [], [], []], [C, mixed_sc, [], [], [], []]]; rows = [(entry(ckey,7,0x99,b32le(0x44)),2)]; sys_rows = [entry(ckey,7,0x44)]
elif mode == \"mixed_tuple_bad_user\":
    skips = [R1, R2]; mixed_sc = [[K, [[0,b32(0x44)],[2,b32(0x9a)]]]]; accounts = [[R1, skipped_sc, [], [], [], []], [R2, skipped_sc, [], [], [], []], [C, mixed_sc, [], [], [], []]]; rows = [(entry(ckey,7,0x99,b32le(0x44)),2)]; sys_rows = [entry(ckey,7,0x44)]
else:
    raise ValueError(mode)
txidx = b\"\".join(struct.pack(\"<Q\", t) for _, t in rows); log = b\"\".join(e for e, _ in rows); sys_log = b\"\".join(sys_rows)
bal = rlp.encode(accounts); skip = b\"\".join(x + bytes(12) for x in skips)
with open(sys.argv[1], \"wb\") as f:
    f.write(struct.pack(\"<Q\", len(bal))); f.write(struct.pack(\"<Q\", len(rows))); f.write(struct.pack(\"<Q\", len(skips))); f.write(struct.pack(\"<Q\", len(sys_rows)))
    f.write(skip); f.write(txidx); f.write(log); f.write(sys_log); f.write(bal)
    total = 32 + len(skip) + len(txidx) + len(log) + len(sys_log) + len(bal); f.write(bytes((-total) % 8))
" "$in_file"
  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_tuple_sequences_consistent_skip_list.elf -i "$in_file" -o "$out_file" -n 9000000 >"gen-out/a2b_tuple_${name}.emu.log" 2>&1 || true
  local st; st=$(python3 -c "d=open(\"$out_file\",\"rb\").read(); print(int.from_bytes(d[:8],\"little\"))")
  [[ "$st" == "$exp" ]] && printf "  tuple   %-12s OK   status=%s\n" "$name" "$st" || { printf "  tuple   %-12s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1; }
}

FAILED=0
run_storage one_skip_ok one_skip_ok 0 || FAILED=1
run_storage two_skip_ok two_skip_ok 0 || FAILED=1
run_storage callee_bad  callee_bad  1 || FAILED=1
run_tuple one_skip_ok one_skip_ok 0 || FAILED=1
run_tuple two_skip_ok two_skip_ok 0 || FAILED=1
run_tuple system_tuple_ok system_tuple_ok 0 || FAILED=1
run_tuple system_tuple_bad system_tuple_bad 1 || FAILED=1
run_tuple mixed_tuple_ok mixed_tuple_ok 0 || FAILED=1
run_tuple mixed_tuple_bad_system mixed_tuple_bad_system 1 || FAILED=1
run_tuple mixed_tuple_bad_user mixed_tuple_bad_user 1 || FAILED=1
run_tuple callee_bad  callee_bad  1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then echo "==> PASS: A2b skip-list comparator probes"; exit 0; else echo "==> FAIL"; exit 1; fi
