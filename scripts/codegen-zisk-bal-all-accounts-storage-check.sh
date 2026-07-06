#!/usr/bin/env bash
# codegen-zisk-bal-all-accounts-storage-check.sh -- bead bmvmx.1.6.4.3.
#
# bal_all_accounts_storage_consistent iterates the BAL account list, SKIPS the
# recipient (checked elsewhere), and for each callee runs the forward (matches) +
# reverse (covers) exec-vs-BAL storage comparators, keying the callee on its
# byte-reversed (LE) address via bal_addr_to_exec_log_key.
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

echo "==> emit zisk_bal_all_accounts_storage_consistent ELF"
lake exe codegen --program zisk_bal_all_accounts_storage_consistent --halt linux93 \
  -o gen-out/zisk_bal_all_accounts_storage_consistent

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <expected_status>
run_case() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_bal_aas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bal_aas_${name}.output"

  MODE="$mode" python3 -c "
import struct, sys, os
mode = os.environ['MODE']
R = bytes([0xBB]*20)               # recipient address (20B BE)
C = bytes(range(1,21))             # callee address 01..14 (distinct, reversal matters)

def account_changes(addr20):
    # claude-c1's AccountChanges hand-encoding: slot7->[[0,11],[1,22]] (final 0x22),
    # slot9->[[0,33]] (final 0x33); 4 trailing empty lists.
    blob = bytes([0xcf,0xc8,0x07,0xc6,0xc2,0x80,0x11,0xc2,0x01,0x22,0xc5,0x09,0xc3,0xc2,0x80,0x33])
    payload = bytes([0x94]) + addr20 + blob + bytes([0xc0,0xc0,0xc0,0xc0])
    assert len(payload) == 41, len(payload)
    return bytes([0xf8, len(payload)]) + payload

def rlp_list(items):
    inner = b''.join(items); L = len(inner)
    if L <= 55: return bytes([0xc0+L]) + inner
    assert L < 256
    return bytes([0xf8, L]) + inner

def callee_key(addr20):                # bal_addr_to_exec_log_key: reverse into low 20B
    return addr20[::-1] + bytes(12)

def log_entry(addrhash32, slot, cur):  # 128B: addrHash, slotKey, original(0), current  (all LE)
    return addrhash32 + slot.to_bytes(32,'little') + bytes(32) + cur.to_bytes(32,'little')

ck = callee_key(C)
if mode == 'consistent':              # recipient(no log, skipped) + callee(log correct) -> 0
    accts = [account_changes(R), account_changes(C)]
    log = [log_entry(ck,7,0x22), log_entry(ck,9,0x33)]
elif mode == 'callee_value_bad':      # callee slot7 current corrupted -> 1
    accts = [account_changes(R), account_changes(C)]
    log = [log_entry(ck,7,0x99), log_entry(ck,9,0x33)]
elif mode == 'callee_absent':         # callee claims changes but no log entries -> 1
    accts = [account_changes(R), account_changes(C)]
    log = []
elif mode == 'recipient_only':        # only the recipient (skipped), no callee -> 0
    accts = [account_changes(R)]
    log = []
else:
    raise ValueError(mode)

bal = rlp_list(accts)
logb = b''.join(log)
recipient = R + bytes(12)             # 32B (20B BE addr + pad)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(bal)))   # +0  BAL section len
    f.write(struct.pack('<Q', len(log)))   # +8  exec log entry count
    f.write(recipient)                     # +16 recipient (32B)
    f.write(logb)                          # +48 exec log
    f.write(bal)                           # +48+128*count BAL section
    total = 48 + len(logb) + len(bal)      # ziskemu requires an 8-byte-multiple input
    pad = (-total) % 8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_storage_consistent.elf \
    -i "$in_file" -o "$out_file" -n 100000000 \
    >"$REPO_ROOT/gen-out/zisk_bal_aas_${name}.emu.log" 2>&1 || true

  local status; status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$exp').to_bytes(8,'little').hex())")"
  if [[ "$status" == "$exp_le" ]]; then
    printf "  %-22s OK   status=%s\n" "$name" "$exp"
    return 0
  fi
  printf "  %-22s FAIL status=0x%s expected=%s\n" "$name" "$status" "$exp"
  return 1
}

FAILED=0
run_case "consistent"        consistent       0 || FAILED=1
run_case "callee_value_bad"  callee_value_bad 1 || FAILED=1
run_case "callee_absent"     callee_absent    1 || FAILED=1
run_case "recipient_only"    recipient_only   0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_all_accounts_storage_consistent skips recipient, LE-keys callees,"
  echo "          accepts consistent storage, rejects value-mismatch/omission"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
