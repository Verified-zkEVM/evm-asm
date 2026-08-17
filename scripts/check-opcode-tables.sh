#!/usr/bin/env bash
# CI drift guard for bead evm-asm-4ch8f.10.2: the opcode dispatch tables.
#
# The Lean mirror in EvmAsm/Codegen/Proofs/OpcodeTables.lean pins the two
# 256-entry, 8-byte-stride `.data` tables the dispatch loop indexes:
#
#   * opcode_gas_costs  -- 256 numeric dwords (staticGasCost b);
#   * opcode_handlers   -- 256 link-resolved dwords (address of the handler
#                          label jumpTargetLabel callFrameGuestRegistry b).
#
# This script links the stateless_guest ELF (the final arbiter), reads the
# 2048 bytes at each symbol, and compares them to the Lean defs (rendered via
# `lake env lean`).  Any divergence -- a re-tiered gas cost, a re-pointed
# handler, a resized/reordered table -- fails loudly, so the kernel-checked
# load spec can never silently describe a table the guest no longer ships.
#
#   gas:      ELF dword[b]  ==  staticGasCost b            (numeric)
#   handlers: ELF dword[b]  ==  symtab[ opcodeHandlerLabels[b] ]  (address)
#
# Wired into scripts/check-build-parallel.sh codegen lane (GH #12496). Previously
# documented as a CI drift guard but never invoked from build.yml / parallel —
# dormant-gate class. Skips gracefully (exit 0) when the RISC-V toolchain is
# absent, mirroring scripts/check-region-map.sh.
#
# NOTE: uses `lake env lean` to render the Lean mirror; that path is incompatible
# with LAKE_ARTIFACT_CACHE=true (#10537). CI's build-parallel runner is
# non-cache for these gates.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v riscv64-unknown-elf-as >/dev/null 2>&1 && ! command -v riscv64-elf-as >/dev/null 2>&1; then
  echo "check-opcode-tables: riscv64 cross toolchain not found; skipping (install to enable)"
  exit 0
fi
READELF="$(command -v readelf || command -v riscv64-unknown-elf-readelf || true)"
OBJCOPY="$(command -v riscv64-unknown-elf-objcopy || command -v objcopy || true)"
if [[ -z "$READELF" || -z "$OBJCOPY" ]]; then
  echo "check-opcode-tables: readelf/objcopy not found; skipping"
  exit 0
fi

ELF_DIR="${ELF_DIR:-gen-out/opcodetables}"
ELF="$ELF_DIR/stateless_guest.elf"
mkdir -p "$ELF_DIR"
if [[ "${NO_BUILD:-0}" != "1" || ! -f "$ELF" ]]; then
  echo "==> emit stateless_guest ELF"
  lake exe codegen --program stateless_guest --halt linux93 -o "$ELF_DIR/stateless_guest" >/dev/null
fi

# --- render the Lean mirror (gas values + handler labels) ----------------
echo "==> render Lean mirror (EvmAsm.Codegen.Proofs.OpcodeTables)"
LEAN_SNIPPET="$(mktemp --suffix=.lean)"
LEAN_OUT="$(mktemp)"
DATA_BIN="$(mktemp)"
cleanup() { rm -f "$LEAN_SNIPPET" "$LEAN_OUT" "$DATA_BIN"; }
trap cleanup EXIT
cat > "$LEAN_SNIPPET" <<'LEAN'
import EvmAsm.Codegen.Proofs.OpcodeTables
open EvmAsm.Codegen
open EvmAsm.Codegen.Proofs.OpcodeTables
-- Render the LEAN MIRROR DEFS (not the emitter source) so any divergence
-- between EvmAsm/Codegen/Proofs/OpcodeTables.lean and the ELF is caught.
def main : IO Unit := do
  IO.println "GAS"
  for v in opcodeGasCostEntries do
    IO.println (toString v.toNat)
  IO.println "HANDLERS"
  for lbl in opcodeHandlerLabels do
    IO.println lbl
LEAN
if ! lake env lean --run "$LEAN_SNIPPET" > "$LEAN_OUT" 2>"$LEAN_OUT.err"; then
  echo "check-opcode-tables: rendering Lean mirror failed -- output follows:" >&2
  cat "$LEAN_OUT.err" >&2 || true
  rm -f "$LEAN_OUT.err"
  exit 1
fi
rm -f "$LEAN_OUT.err"

# --- pull the ELF facts and compare --------------------------------------
echo "==> compare against linked ELF: $ELF"
# .data as a flat binary blob (base = .data vaddr) so we can slice by vaddr.
"$OBJCOPY" -O binary --only-section=.data "$ELF" "$DATA_BIN"
DATA_BASE="$("$READELF" -SW "$ELF" | python3 -c "
import re,sys
for line in sys.stdin:
    m=re.search(r'\]\s+\.data\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+', line)
    if m: print(int(m.group(1),16)); break
")"

# symbol -> address map (name<TAB>hexaddr) for the tables + every handler label.
SYMS="$("$READELF" -sW "$ELF" | awk '$1 ~ /^[0-9]+:$/ && NF>=8 {print $8"\t"$2}')"

rc=0
OPCODE_SYMS="$SYMS" python3 - "$ELF" "$DATA_BIN" "$DATA_BASE" "$LEAN_OUT" <<'PY' || rc=$?
import sys
elf, data_bin, data_base, lean_out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]

# symbol table: name -> int addr (built from the here-doc env below)
import os
syms = {}
for line in os.environ["OPCODE_SYMS"].splitlines():
    if not line.strip():
        continue
    name, addr = line.split("\t")
    # first definition wins (matches readelf order / symaddr in check-region-map)
    syms.setdefault(name, int(addr, 16))

blob = open(data_bin, "rb").read()

def table_dwords(sym):
    if sym not in syms:
        sys.exit(f"check-opcode-tables: symbol {sym} not in ELF symtab")
    off = syms[sym] - data_base
    if off < 0 or off + 256*8 > len(blob):
        sys.exit(f"check-opcode-tables: {sym} table (off {off}) outside .data blob ({len(blob)} bytes)")
    return [int.from_bytes(blob[off+8*i:off+8*i+8], "little") for i in range(256)]

# parse the Lean mirror
lines = open(lean_out).read().splitlines()
gi = lines.index("GAS"); hi = lines.index("HANDLERS")
gas_expected = [int(x) for x in lines[gi+1:hi]]
handler_labels = lines[hi+1:hi+1+256]
if len(gas_expected) != 256 or len(handler_labels) != 256:
    sys.exit(f"check-opcode-tables: Lean mirror gave {len(gas_expected)} gas / {len(handler_labels)} handler entries (want 256/256)")

fail = 0

gas_actual = table_dwords("opcode_gas_costs")
for b in range(256):
    if gas_actual[b] != gas_expected[b]:
        print(f"  DRIFT opcode_gas_costs[{b}]: ELF {gas_actual[b]} != Lean staticGasCost {gas_expected[b]}")
        fail = 1
if not fail:
    print(f"  OK   opcode_gas_costs: 256 dwords match staticGasCost")

hnd_actual = table_dwords("opcode_handlers")
hfail = 0
for b in range(256):
    lbl = handler_labels[b]
    if lbl not in syms:
        print(f"  DRIFT opcode_handlers[{b}]: Lean label {lbl!r} has no ELF symbol")
        hfail = 1; continue
    want = syms[lbl]
    if hnd_actual[b] != want:
        print(f"  DRIFT opcode_handlers[{b}]: ELF {hnd_actual[b]:#x} != &{lbl} {want:#x}")
        hfail = 1
if not hfail:
    print(f"  OK   opcode_handlers: 256 dwords match &(opcodeHandlerLabels[b])")
fail |= hfail

sys.exit(1 if fail else 0)
PY

if [[ "$rc" != "0" ]]; then
  echo "check-opcode-tables: DRIFT detected (see above)"
  exit 1
fi
echo "check-opcode-tables: opcode tables match the linked ELF"
