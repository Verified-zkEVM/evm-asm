#!/usr/bin/env bash
# CI drift guard for bead evm-asm-4ch8f.6: the authoritative guest region map.
#
# Cross-checks EvmAsm/Codegen/RegionMap.lean (and the .9.3 linker-facts TSV)
# against the linked stateless_guest ELF -- the final arbiter. Two tiers:
#
#   SCOPE: this guard validates the stateless_guest ELF ONLY. Since GH #10836
#     the `.bss` section-start is PER UNIT (guest 0xa3110000, probe/test units
#     0xa3d10000, see Driver.assembleAndLink / Cli.emitAndLink); probe ELFs are
#     deliberately NOT checked here and RegionMap describes the guest's layout.
#
#   STRUCTURAL (hard fail): facts that must NEVER drift silently --
#     * section bases (.text/.data/.bss/.sszscratch) == the -Ttext/-Tdata/
#       --section-start flags and RegionMap constants;
#     * the top RW LOAD segment stays below the 0xc0000000 RAM ceiling;
#     * .data ends below .sszscratch;
#     * the call_frame_arena union: call_frame_arena == basr_values, the five
#       coalesced children sit at the RegionMap arena-relative offsets, the arena
#       is fully inside .bss, and its extent == frameArrayBytes.
#
#   LINK-LAYOUT (hard fail, repaired by a manual convergent regen): the section
#     sizes and symbol->address TSV are link-dependent. `gen-symbol-addresses.py`
#     writes only the TSV; it does NOT update RegionMap or GuestImage. On drift:
#       1. relink + regenerate the TSV; regenerate GuestAddrs and GuestImageEntries;
#       2. copy the ELF's .text/.data/.bss sizes into RegionMap and its .bss end
#          into GuestImage.lean's `guestScratch_sat` literals; then
#       3. relink and repeat from step 1 until those values stop moving.
#     See docs/regenerating-generated-files.md. This keeps the Lean map matching
#     the ELF (the .6 contract) instead of quietly diverging.
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
read BSS_BASE  BSS_SIZE  <<<"$(sec .bss)"
read SSZ_BASE  SSZ_SIZE  <<<"$(sec .sszscratch)"
COMMITTED_SECTION_COUNT=$("$READELF" -SW "$ELF" | awk '$2 == ".committed_storage" { n++ } END { print n + 0 }')

echo "== structural (must never drift) =="
check ".text base"       "0000000080000000" "$TEXT_BASE"
check ".committed_storage section absent" "0" "$COMMITTED_SECTION_COUNT"
check ".data base"       "00000000a3000000" "$DATA_BASE"
check ".bss base"        "00000000a3110000" "$BSS_BASE"
check ".sszscratch base" "00000000bf980000" "$SSZ_BASE"

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

# top RW LOAD below RAM ceiling + .data/.bss below .sszscratch
DATA_END=$(python3 -c "print('%x' % (0x$DATA_BASE + 0x$DATA_SIZE))")
BSS_END=$(python3 -c "print('%x' % (0x$BSS_BASE + 0x$BSS_SIZE))")
python3 - "$DATA_END" "$BSS_END" <<'PY' || fail=1
import sys
data_end, bss_end = [int(x, 16) for x in sys.argv[1:]]
ok = data_end <= 0xa3110000 and bss_end < 0xbf980000 and bss_end < 0xc0000000
print(f"  {'OK  ' if ok else 'DRIFT'} .data end 0x{data_end:x} <= .bss base 0xa3110000")
print(f"  {'OK  ' if ok else 'DRIFT'} .bss end 0x{bss_end:x} < .sszscratch 0xbf980000 and < RAM ceiling 0xc0000000")
sys.exit(0 if ok else 1)
PY

# --- union arena (soundness-critical placement) ---
echo "== call_frame_arena union =="
symaddr() {
  # Consume all readelf output: an early awk exit makes readelf receive
  # SIGPIPE, which is fatal under this script's `pipefail` setting.
  "$READELF" -sW "$ELF" | awk -v n="$1" '$8==n && !found {print $2; found=1}'
}

# Absolute link-dependent pins are part of the map contract too. Keep this
# check next to the relative union checks: a relative extent can remain valid
# after every symbol moves while an absolute RegionMap pin silently goes stale.
LEAN_MAP="EvmAsm/Codegen/RegionMap.lean"
lean_def_hex() {
  sed -nE "s/^def $1 : Nat := 0x([0-9a-fA-F]+)$/\1/p" "$LEAN_MAP" | head -n 1
}
check_link_pin() {
  local desc="$1" def_name="$2" symbol="$3" map_hex actual expected
  map_hex="$(lean_def_hex "$def_name")"
  actual="$(symaddr "$symbol")"
  if [[ -z "$map_hex" || -z "$actual" ]]; then
    note "DRIFT $desc: RegionMap def or ELF symbol is missing (map=$map_hex elf=$actual)"
    fail=1
    return
  fi
  printf -v expected '%016x' "$((16#$map_hex))"
  check "$desc" "$expected" "$actual"
}
check_link_pin "RegionMap.callFrameArenaBase" callFrameArenaBase call_frame_arena
check_link_pin "RegionMap.evmMemoryPoolBase" evmMemoryPoolBase evm_memory_pool
check_link_pin "RegionMap.syslogBase" syslogBase bv_system_storage_log

# The union inventory is a closed set for this emitted guest. Checking only
# the three symbols used by the relative arithmetic would let a phantom map
# child survive indefinitely, so check the map's names and every ELF symbol.
map_union_names="$(awk '
  /^def dataUnionChildren/ {inside=1; next}
  inside && /name :=/ {
    line=$0; sub(/^.*name := "/, "", line); sub(/".*$/, "", line); print line
  }
  inside && /^$/ {exit}
' "$LEAN_MAP" | sort | paste -sd' ' -)"
expected_union_names="baap_storage_desc baap_storage_paths baap_storage_values basr_accounts basr_values"
if [[ "$map_union_names" == "$expected_union_names" ]]; then
  note "OK   RegionMap.dataUnionChildren names = $expected_union_names"
else
  note "DRIFT RegionMap.dataUnionChildren names: expected $expected_union_names, map has $map_union_names"
  fail=1
fi
for union_name in $expected_union_names; do
  union_addr="$(symaddr "$union_name")"
  if [[ -n "$union_addr" ]]; then
    note "OK   union symbol $union_name = $union_addr"
  else
    note "DRIFT union symbol $union_name is absent from ELF"
    fail=1
  fi
done

# GuestAddrs.lean is generated from the linked symbol table and is consumed by
# handwritten proof/relocation code. Check the whole generated symbol set
# against this ELF, not only the five union children above. This makes a name
# that exists only in Lean fail as a phantom instead of silently becoming a
# proof subject with no emitted storage.
GUEST_ADDRS="EvmAsm/Codegen/GuestAddrs.lean"
guest_addrs_missing="$(comm -23 \
  <(rg '^def [A-Za-z0-9_]+ : Nat := 0x' "$GUEST_ADDRS" |
      sed -E 's/^def ([A-Za-z0-9_]+) : Nat := 0x.*/\1/' | sort -u) \
  <("$READELF" -sW "$ELF" |
      awk 'NF >= 8 && $7 != "UND" && $4 != "SECTION" && $4 != "FILE" && $8 !~ /^\$/ {print $8}' |
      sort -u))"
if [[ -z "$guest_addrs_missing" ]]; then
  guest_addrs_count="$(rg -c '^def [A-Za-z0-9_]+ : Nat := 0x' "$GUEST_ADDRS")"
  note "OK   GuestAddrs symbols all exist in ELF ($guest_addrs_count names)"
else
  note "DRIFT GuestAddrs names absent from ELF: $guest_addrs_missing"
  fail=1
fi
python3 - "$(symaddr call_frame_arena)" "$(symaddr basr_values)" "$(symaddr basr_accounts)" \
  "$(symaddr bv_system_storage_log)" "$(symaddr baap_storage_desc)" "$(symaddr baap_storage_paths)" \
  "$(symaddr baap_storage_values)" \
  "0x$BSS_BASE" "0x$BSS_SIZE" "$(symaddr evm_memory_pool)" "$(symaddr evm_memory_pool_end)" \
  "$(symaddr evm_memory)" <<'PY' || fail=1
import sys
(cfa, bval, bacc, syslog, desc, paths, vals, bbase, bsize, pool, pend, emem) = [int(x,16) for x in sys.argv[1:]]
# RegionMap constants (kept in sync with BlockVerdictParams.lean).
S = 100018*256          # bsrMaxStateChanges*bsrEncodedAccountBytes
syslogL = 32768*128     # bvSystemStorageLogBytes (4ch8f.73: 2*16384 rows, standalone)
descB = 100000*40       # bsrMaxBalItems*baapStorageDescBytes
pathB = 100000*64       # bsrMaxBalItems*bsrPathBytes
frameArrayBytes = 1025*0x19000  # frameSlotCount * CallFrameLayout.frameStride (keep in sync)
# 4ch8f.73: bv_system_storage_log is NO LONGER unioned into call_frame_arena; the
# five remaining children are basr pair + three baap_storage_* (baap at offset 2S).
exp = {
 "call_frame_arena == basr_values": (cfa, bval),
 "basr_accounts off": (bacc-cfa, S),
 "baap_storage_desc off": (desc-cfa, 2*S),
 "baap_storage_paths off": (paths-cfa, 2*S+descB),
 "baap_storage_values off": (vals-cfa, 2*S+descB+pathB),
 "arena extent == frameArrayBytes": (frameArrayBytes, frameArrayBytes),
}
bad = 0
for k,(a,b) in exp.items():
    ok = a==b
    print(f"  {'OK  ' if ok else 'DRIFT'} {k}: {a}{'' if ok else ' (expected '+str(b)+')'}")
    bad |= (not ok)
within = bbase <= cfa and cfa+frameArrayBytes <= bbase+bsize
print(f"  {'OK  ' if within else 'DRIFT'} call_frame_arena within .bss")
bad |= (not within)
# 4ch8f.73 clobber-closed: standalone bv_system_storage_log must NOT overlap the
# frame arena (else deep dispatch frames would zero it before the BAL validators
# read it). It is emitted below the arena, so syslog end <= arena base.
sys_ok = syslog + syslogL <= cfa
print(f"  {'OK  ' if sys_ok else 'DRIFT'} bv_system_storage_log disjoint from call_frame_arena")
bad |= (not sys_ok)
pool_ok = pool == cfa + frameArrayBytes and pend - pool == 0x6000000 and pend <= bbase + bsize
print(f"  {'OK  ' if pool_ok else 'DRIFT'} evm_memory_pool adjacent, 96 MiB, and within .bss")
bad |= (not pool_ok)
# GH #10557: SECOND LINE OF DEFENCE for the memory-clamp fill loops. An overshoot
# past a dense arena's top end corrupts whatever is mapped above it -- and
# rb_running_block_bloom sits at exactly evm_memory_pool_end with zero slack, so
# on that boundary an off-by-N reaches verdict state (see the layout invariant at
# the pool's emission site in Programs/BlockVerdictDataSectionTail.lean).
#
# The mitigation that costs nothing is that ONE of the two arenas ends exactly at
# __BSS_END__, whose neighbour is ~7.2 MiB of UNMAPPED address space: nothing
# there can be corrupted into a committed value. Today that is evm_memory
# (evm_memory + 0x400000 == __BSS_END__ exactly). This is a COINCIDENCE between an
# arena size and a section layout, not a construction, so it is pinned here --
# appending any new .bss section would otherwise silently push both arenas away
# from the boundary and remove the backstop with no other signal.
#
# Deliberately written as "whichever arena is last", not "evm_memory is last", so
# it survives the #10557 reorder that would put evm_memory_pool at the top
# instead. It fails only if NEITHER arena ends at __BSS_END__.
bss_end = bbase + bsize
backstop_ok = bss_end in (emem + 0x400000, pend)
which = "evm_memory" if bss_end == emem + 0x400000 else ("evm_memory_pool" if bss_end == pend else "NEITHER")
print(f"  {'OK  ' if backstop_ok else 'DRIFT'} a dense arena ends at __BSS_END__ "
      f"(unmapped backstop): {which}")
bad |= (not backstop_ok)
sys.exit(1 if bad else 0)
PY

# --- link-dependent sizes vs RegionMap constants ---
echo "== link-layout (DRIFT REPAIR: relink + TSV/GuestAddrs/GuestImageEntries; pin RegionMap .text/.data/.bss and GuestImage .bss end from that ELF; repeat to fixpoint — docs/regenerating-generated-files.md) =="
LEAN_TEXT=$(grep -oE 'def textSizeBytes : Nat := 0x[0-9a-fA-F]+' EvmAsm/Codegen/RegionMap.lean | grep -oE '0x[0-9a-fA-F]+')
LEAN_DATA=$(grep -oE 'def dataSizeBytes : Nat := 0x[0-9a-fA-F]+' EvmAsm/Codegen/RegionMap.lean | grep -oE '0x[0-9a-fA-F]+')
LEAN_BSS=$(grep -oE 'def bssSizeBytes : Nat := 0x[0-9a-fA-F]+' EvmAsm/Codegen/RegionMap.lean | grep -oE '0x[0-9a-fA-F]+')
check "RegionMap.textSizeBytes" "$(printf '%x' $LEAN_TEXT)" "$(printf '%x' 0x$TEXT_SIZE)"
check "RegionMap.dataSizeBytes" "$(printf '%x' $LEAN_DATA)" "$(printf '%x' 0x$DATA_SIZE)"
check "RegionMap.bssSizeBytes" "$(printf '%x' $LEAN_BSS)" "$(printf '%x' 0x$BSS_SIZE)"

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
