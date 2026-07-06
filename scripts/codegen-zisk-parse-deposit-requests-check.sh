#!/usr/bin/env bash
# codegen-zisk-parse-deposit-requests-check.sh -- bead evm-asm-8uld3.1 (EIP-6110).
#
# parse_deposit_requests scans a block's logs and concatenates the 192-byte unframed
# body of every valid DepositEvent (address == DEPOSIT_CONTRACT_ADDRESS and topic0 ==
# DEPOSIT_EVENT_SIGNATURE_HASH), via extract_deposit_data. Mirrors execution-specs
# amsterdam requests.py::parse_deposit_requests. Non-deposit logs are skipped; a
# deposit log with malformed data sets the status flag.
#
# Output: status@0, total_bytes@8, concatenated deposit bodies@16.
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

echo "==> emit zisk_parse_deposit_requests ELF"
lake exe codegen --program zisk_parse_deposit_requests --halt linux93 \
  -o gen-out/zisk_parse_deposit_requests

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <exp_status> <exp_total_bytes>
run_case() {
  local name="$1" mode="$2" exp_status="$3" exp_total="$4"
  local in_file="$REPO_ROOT/gen-out/zisk_pdr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_pdr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_pdr_${name}.expected"

  MODE="$mode" python3 -c "
import struct, sys, os
mode = os.environ['MODE']
DEPOSIT_ADDR = bytes.fromhex('00000000219ab540356cbb839cbe05303d7705fa')          # 20
DEPOSIT_SIG  = bytes.fromhex('649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5')  # 32
OTHER_ADDR   = bytes.fromhex('1111111111111111111111111111111111111111')
OTHER_SIG    = bytes.fromhex('22'*32)

def deposit_event(pubkey, wc, amount, sig, index, bad_offset=False):
    def field(d, size): pad=(-len(d))%32; return size.to_bytes(32,'big')+d+bytes(pad)
    offsets=[160,256,320,384,512]; sizes=[48,32,8,96,8]
    if bad_offset: offsets[0]=161
    head=b''.join(o.to_bytes(32,'big') for o in offsets)
    body=field(pubkey,48)+field(wc,32)+field(amount,8)+field(sig,96)+field(index,8)
    d=head+body; assert len(d)==576, len(d); return d

def body192(pubkey, wc, amount, sig, index):
    return pubkey+wc+amount+sig+index   # 48+32+8+96+8 = 192

def log_record(addr, topic0, data, topic_count=1):
    rec  = addr.ljust(32, b'\x00')[:32]      # +0  address (first 20), pad to 32
    rec += struct.pack('<Q', topic_count)    # +32 topic_count
    rec += topic0.ljust(32, b'\x00')[:32]    # +40 topic0 (32B)
    rec += struct.pack('<Q', len(data))      # +72 data_len
    rec += data                              # +80 data
    rec += bytes((-len(data)) % 8)           # pad to 8
    return rec

# deposit #1 / #2 field sets (distinct so the concat order is checked)
d1 = dict(pubkey=bytes(range(1,49)),   wc=bytes([0xcc])*32, amount=(1000000000).to_bytes(8,'little'), sig=bytes(range(100,196)),  index=(7).to_bytes(8,'little'))
d2 = dict(pubkey=bytes(range(49,97)),  wc=bytes([0xdd])*32, amount=(2000000000).to_bytes(8,'little'), sig=bytes(range(150,246)),  index=(8).to_bytes(8,'little'))

logs=[]; exp=b''
if mode=='two_deposits':
    logs.append(log_record(OTHER_ADDR, DEPOSIT_SIG, b'\x00'*576))                       # wrong addr -> skip
    logs.append(log_record(DEPOSIT_ADDR, DEPOSIT_SIG, deposit_event(**d1)))             # match
    logs.append(log_record(DEPOSIT_ADDR, OTHER_SIG,   deposit_event(**d2)))             # wrong sig -> skip
    logs.append(log_record(DEPOSIT_ADDR, DEPOSIT_SIG, deposit_event(**d2)))             # match
    exp = body192(**d1) + body192(**d2)
elif mode=='none':
    logs.append(log_record(OTHER_ADDR, DEPOSIT_SIG, b'\x00'*576))
    logs.append(log_record(DEPOSIT_ADDR, OTHER_SIG, deposit_event(**d1)))
    logs.append(log_record(DEPOSIT_ADDR, DEPOSIT_SIG, deposit_event(**d1), topic_count=0))  # topic_count 0 -> skip
    exp = b''
elif mode=='one_deposit_d2':
    logs.append(log_record(DEPOSIT_ADDR, DEPOSIT_SIG, deposit_event(**d2)))                 # single match
    exp = body192(**d2)
elif mode=='malformed':
    logs.append(log_record(DEPOSIT_ADDR, DEPOSIT_SIG, deposit_event(bad_offset=True, **d1)))  # bad ABI -> status 1
    exp = b''
else:
    raise SystemExit('bad mode')

# the probe dumps at most 240 payload bytes (ziskemu output cap is 256B); the
# status + total length still verify the full count, and the dumped prefix verifies
# the in-order content (each individual 192-byte body is fully covered by a
# single-deposit case).
exp = exp[:240]

array = b''.join(logs)
with open(sys.argv[1],'wb') as f:
    rec = struct.pack('<Q', len(logs)) + array
    f.write(rec)
    f.write(bytes((-len(rec)) % 8))
with open(sys.argv[2],'wb') as f:
    f.write(exp)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_parse_deposit_requests.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_pdr_${name}.emu.log" 2>&1 || true

  local status total exp_bytes got_bytes
  status="$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")"
  total="$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[8:16],'little'))")"
  exp_bytes="$(xxd -p "$exp_file" | tr -d '\n')"
  # compare the dumped prefix (capped at 240B by the probe / ziskemu output cap).
  got_bytes="$(python3 -c "d=open('$out_file','rb').read(); n=min($total,240); print(d[16:16+n].hex())")"

  if [[ "$status" == "$exp_status" && "$total" == "$exp_total" && "$got_bytes" == "$exp_bytes" ]]; then
    printf "  %-16s OK   status=%s total=%s\n" "$name" "$status" "$total"; return 0
  fi
  printf "  %-16s FAIL status=%s/%s total=%s/%s\n    got=%s\n    exp=%s\n" \
    "$name" "$status" "$exp_status" "$total" "$exp_total" "$got_bytes" "$exp_bytes"; return 1
}

FAILED=0
# two valid deposits interleaved with wrong-addr + wrong-sig logs -> 2x192=384 bytes, in order.
run_case "two_deposits" two_deposits 0 384 || FAILED=1
# a single deposit (d2) -> full 192-byte body verified (fits the output cap).
run_case "one_deposit_d2" one_deposit_d2 0 192 || FAILED=1
# no matching deposit (wrong addr / wrong sig / topic_count 0) -> 0 bytes.
run_case "none"         none         0 0   || FAILED=1
# a deposit-addr+sig log with malformed ABI data -> status 1, 0 bytes.
run_case "malformed"    malformed    1 0   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: parse_deposit_requests EIP-6110 deposit-log scan"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
