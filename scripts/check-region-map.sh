#!/usr/bin/env bash
# CI drift guard for bead evm-asm-4ch8f.6: the authoritative guest region map.
#
# Cross-checks EvmAsm/Codegen/RegionMap.lean (and the .9.3 linker-facts TSV)
# against the linked stateless_guest ELF -- the final arbiter. Two tiers:
#
#   STRUCTURAL (hard fail): facts that must NEVER drift silently --
#     * section bases (.text/.data/.sszscratch) == the -Ttext/-Tdata/
#       --section-start flags and RegionMap constants;
#     * the top RW LOAD segment stays below the 0xc0000000 RAM ceiling;
#     * .data ends below .sszscratch;
#     * the call_frame_arena union: call_frame_arena == basr_values, the six
#       coalesced children sit at the RegionMap arena-relative offsets, the arena
#       is fully inside .data, and its extent == frameArrayBytes.
#
#   LINK-LAYOUT (hard fail, but fixed by regeneration): the .text/.data SIZES and
#     the symbol->address TSV are link-dependent. When a guest change moves them,
#     regenerate: `scripts/gen-symbol-addresses.py --build` and update
#     RegionMap.textSizeBytes/dataSizeBytes to the reported sizes. This keeps the
#     Lean map matching the ELF (the .6 contract) instead of quietly diverging.
#
# Skips gracefully (exit 0) when the RISC-V toolchain is absent, mirroring
# scripts/check-asm-to-program.sh.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v riscv64-unknown-elf-as >/dev/null 2>&1 && ! command -v riscv64-elf-as >/dev/null 2>&1; then
  echo "check-region-map: riscv64 cross toolchain not found; skipping (install to enable)"
  exit 0
fi
READELF="$(command -v readelf || command -v riscv64-unknown-elf-readelf || true)"
if [[ -z "$READELF" ]]; then
  echo "check-region-map: readelf not found; skipping"
  exit 0
fi

ELF_DIR="${ELF_DIR:-gen-out/regionmap}"
ELF="$ELF_DIR/stateless_guest.elf"
mkdir -p "$ELF_DIR"
if [[ "${NO_BUILD:-0}" != "1" || ! -f "$ELF" ]]; then
  echo "==> emit stateless_guest ELF"
  lake exe codegen --program stateless_guest --halt linux93 -o "$ELF_DIR/stateless_guest" >/dev/null
fi

fail=0
note() { echo "  $*"; }
check() { # desc expected actual
  if [[ "$2" == "$3" ]]; then note "OK   $1 = $2"; else note "DRIFT $1: expected $2, ELF has $3"; fail=1; fi
}

# --- section headers (base<TAB>size, lowercase hex, no 0x) ---
sec() {
  "$READELF" -SW "$ELF" | python3 -c "
import re,sys
want=sys.argv[1]
for line in sys.stdin:
    m=re.search(r'\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)', line)
    if m and m.group(1)==want:
        print(m.group(2), m.group(3)); break
" "$1"
}
read TEXT_BASE TEXT_SIZE <<<"$(sec .text)"
read DATA_BASE DATA_SIZE <<<"$(sec .data)"
read SSZ_BASE  SSZ_SIZE  <<<"$(sec .sszscratch)"

echo "== structural (must never drift) =="
check ".text base"       "0000000080000000" "$TEXT_BASE"
check ".data base"       "00000000a3000000" "$DATA_BASE"
check ".sszscratch base" "00000000bf500000" "$SSZ_BASE"

# emitted-reality anchors the section table omits (guest stack top + ZisK MTVEC).
# These live in the emitted .s (absolute `li` constants), not the ELF symtab.
GUEST_S="$ELF_DIR/stateless_guest.s"
if [[ -f "$GUEST_S" ]]; then
  SP_INIT=$(grep -cE "li sp, *0xa0050000" "$GUEST_S")
  MTVEC=$(grep -cE "li [a-z0-9]+, *0xa0009828" "$GUEST_S")
  check "guest_stack top (li sp,0xa0050000) present" "1" "$([[ $SP_INIT -ge 1 ]] && echo 1 || echo 0)"
  check "zisk MTVEC (0xa0009828) referenced"          "1" "$([[ $MTVEC  -ge 1 ]] && echo 1 || echo 0)"
  # the sole sp init must be exactly 0xa0050000 (guest_stack top invariant)
  OTHER_SP=$(grep -E "li sp," "$GUEST_S" | grep -vcE "0xa0050000" || true)
  check "no other 'li sp,' init besides 0xa0050000" "0" "$OTHER_SP"
else
  note "SKIP emitted-reality (.s) checks: $GUEST_S absent (pass without --no-build to emit it)"
fi

# top RW LOAD below RAM ceiling + .data below .sszscratch
DATA_END=$(python3 -c "print('%x' % (0x$DATA_BASE + 0x$DATA_SIZE))")
python3 - "$DATA_END" <<'PY' || fail=1
import sys
data_end = int(sys.argv[1], 16)
ok = data_end < 0xbf500000 and data_end < 0xc0000000
print(f"  {'OK  ' if ok else 'DRIFT'} .data end 0x{data_end:x} < .sszscratch 0xbf500000 and < RAM ceiling 0xc0000000")
sys.exit(0 if ok else 1)
PY

# --- union arena (soundness-critical placement) ---
echo "== call_frame_arena union =="
symaddr() { "$READELF" -sW "$ELF" | awk -v n="$1" '$8==n {print $2; exit}'; }
python3 - "$(symaddr call_frame_arena)" "$(symaddr basr_values)" "$(symaddr basr_accounts)" \
  "$(symaddr bv_system_storage_log)" "$(symaddr baap_storage_desc)" "$(symaddr baap_storage_paths)" \
  "$(symaddr baap_storage_delete_paths)" "$(symaddr baap_storage_values)" "$(symaddr call_frame_arena_end)" \
  "0x$DATA_BASE" "0x$DATA_SIZE" <<'PY' || fail=1
import sys
(cfa, bval, bacc, syslog, desc, paths, dpaths, vals, cend, dbase, dsize) = [int(x,16) for x in sys.argv[1:]]
# RegionMap constants (kept in sync with BlockVerdictParams.lean).
S = 100018*256          # bsrMaxStateChanges*bsrEncodedAccountBytes
syslogL = 32768*128     # bvSystemStorageLogBytes (4ch8f.73: 2*16384 rows, standalone)
descB = 100000*40       # bsrMaxBalItems*baapStorageDescBytes
pathB = 100000*64       # bsrMaxBalItems*bsrPathBytes
frameArrayBytes = 1025*0x39000  # frameSlotCount * CallFrameLayout.frameStride (keep in sync)
# 4ch8f.73: bv_system_storage_log is NO LONGER unioned into call_frame_arena; the
# six remaining children are basr pair + four baap_storage_* (baap at offset 2S).
exp = {
 "call_frame_arena == basr_values": (cfa, bval),
 "basr_accounts off": (bacc-cfa, S),
 "baap_storage_desc off": (desc-cfa, 2*S),
 "baap_storage_paths off": (paths-cfa, 2*S+descB),
 "baap_storage_delete_paths off": (dpaths-cfa, 2*S+descB+pathB),
 "baap_storage_values off": (vals-cfa, 2*S+descB+2*pathB),
 "arena extent == frameArrayBytes": (cend-cfa, frameArrayBytes),
}
bad = 0
for k,(a,b) in exp.items():
    ok = a==b
    print(f"  {'OK  ' if ok else 'DRIFT'} {k}: {a}{'' if ok else ' (expected '+str(b)+')'}")
    bad |= (not ok)
within = dbase <= cfa and cfa+frameArrayBytes <= dbase+dsize
print(f"  {'OK  ' if within else 'DRIFT'} call_frame_arena within .data")
bad |= (not within)
# 4ch8f.73 clobber-closed: standalone bv_system_storage_log must NOT overlap the
# frame arena (else deep dispatch frames would zero it before the BAL validators
# read it). It is emitted below the arena, so syslog end <= arena base.
sys_ok = (syslog + syslogL <= cfa) or (cend <= syslog)
print(f"  {'OK  ' if sys_ok else 'DRIFT'} bv_system_storage_log disjoint from call_frame_arena")
bad |= (not sys_ok)
sys.exit(1 if bad else 0)
PY

# --- link-dependent sizes vs RegionMap constants ---
echo "== link-layout (regenerate on drift: gen-symbol-addresses.py --build) =="
LEAN_TEXT=$(grep -oE 'def textSizeBytes : Nat := 0x[0-9a-fA-F]+' EvmAsm/Codegen/RegionMap.lean | grep -oE '0x[0-9a-fA-F]+')
LEAN_DATA=$(grep -oE 'def dataSizeBytes : Nat := 0x[0-9a-fA-F]+' EvmAsm/Codegen/RegionMap.lean | grep -oE '0x[0-9a-fA-F]+')
check "RegionMap.textSizeBytes" "$(printf '%x' $LEAN_TEXT)" "$(printf '%x' 0x$TEXT_SIZE)"
check "RegionMap.dataSizeBytes" "$(printf '%x' $LEAN_DATA)" "$(printf '%x' 0x$DATA_SIZE)"

# --- TSV snapshot ---
TMP_TSV="$(mktemp)"
OUT_BAK="scripts/asm-fixtures/symbol-addresses.tsv"
cp "$OUT_BAK" "$TMP_TSV"
NO_BUILD=1 ELF_DIR="$ELF_DIR" python3 scripts/gen-symbol-addresses.py --elf-dir "$ELF_DIR" >/dev/null
if ! diff -q "$TMP_TSV" "$OUT_BAK" >/dev/null; then
  echo "  DRIFT symbol-addresses.tsv changed; commit the regenerated snapshot"
  cp "$TMP_TSV" "$OUT_BAK"  # restore working copy; report only
  fail=1
else
  echo "  OK   symbol-addresses.tsv matches ELF"
fi
rm -f "$TMP_TSV"

if [[ "$fail" != "0" ]]; then
  echo "check-region-map: DRIFT detected (see above)"
  exit 1
fi
echo "check-region-map: region map matches the linked ELF"
