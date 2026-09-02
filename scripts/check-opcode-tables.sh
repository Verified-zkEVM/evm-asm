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
# GH #13229 adds a THIRD leg, and it is a different claim from the first two.
# Those compare the ELF against the emitter-side mirror plus the ELF's OWN
# symbol table, so they stay green no matter what Lean believes the loaded
# `.data` contains.  `Proofs/GuestDataImage.lean` now asserts exactly that —
# `guestDataImage` says the two tables HOLD these bytes at entry — and it gets
# there through a chain the first two legs never touch:
#
#     ELF  ->  symbol-addresses.tsv  ->  GuestAddrs.h_*
#          ->  GuestHandlerAddrs.handlerAddrRows  ->  guestHandlerAddr
#          ->  opcodeHandlerEntries guestHandlerAddr
#
# Each link in that chain has its own regenerate-and-diff gate, but nothing
# compared the far END of it to the shipped bytes.  So:
#
#   pinned:   ELF dword[b]  ==  GuestDataImage.shippedHandlerTable[b]
#             ELF dword[b]  ==  GuestDataImage.shippedGasCostTable[b]
#   layout:   `.data` is PROGBITS, and its (addr, size) IS
#             (RegionMap.dataRegion.base, .size) -- the loader copies these
#             bytes in before `_start`, which is WHY pinning them is faithful
#             rather than merely convenient;
#             the table pair is adjacent, dword-aligned, and ends exactly at
#             the top of `.data` (`GuestDataImage.dataTables_layout` as an ELF
#             fact rather than a `decide` over Lean constants).
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

# GH #12156, two defects, and they compound.
#
#   1. TOOL RESOLUTION. This gate hand-rolled its probes and neither accepted
#      the `riscv64-elf-*` spelling that Homebrew's `riscv64-elf-binutils`
#      installs: `READELF` looked for a BARE `readelf` first (macOS has none)
#      then only the `-unknown-` triple, and `OBJCOPY` likewise. So it skipped
#      on every macOS checkout that in fact had everything it needed, while
#      `check-region-map.sh` resolved the same tools in the same run.
#      ⇒ Fixed by ADOPTING `scripts/lib/riscv-tools.sh` (#12503) rather than
#      repairing the hand-rolled probes. That helper already tries
#      `riscv64-unknown-elf-*` then `riscv64-elf-*`, honours `RISCV_<TOOL>`
#      overrides, and — the part that matters for the wrapper — emits the ONE
#      skip wording that `check-build-parallel.sh` machine-checks its `SKIP_RE`
#      against. A fourth bespoke wording is how that list rotted twice
#      already (#12503, #12496, and see #12515).
#
#   2. A SKIP READ AS A PASS. Both miss paths printed to stdout and exited 0,
#      so a local run looked green while the opcode tables were never checked
#      — the #11043 failure class. CI *installs* binutils-riscv64-unknown-elf
#      (build.yml, "Install RISC-V binutils for codegen link checks"), so a
#      skip there cannot be a contributor's missing toolchain; it can only mean
#      the environment regressed. Under `CI` the skip is now a hard failure,
#      and stays a tolerated skip for a contributor without cross-binutils.
#
# shellcheck source=lib/riscv-tools.sh
source "$(dirname "$0")/lib/riscv-tools.sh"

if ! require_riscv_tools_or_skip check-opcode-tables as readelf objcopy; then
  if [[ -n "${CI:-}" ]]; then
    echo "check-opcode-tables: FAILING rather than skipping — CI installs the" >&2
    echo "  RISC-V toolchain, so a miss here means the environment regressed" >&2
    echo "  (#12156); a skip that reads as a pass is what this gate is for." >&2
    exit 1
  fi
  exit 0
fi
READELF="$RISCV_RESOLVED_READELF"
OBJCOPY="$RISCV_RESOLVED_OBJCOPY"

ELF_DIR="${ELF_DIR:-gen-out/opcodetables}"
ELF="$ELF_DIR/stateless_guest.elf"
mkdir -p "$ELF_DIR"
if [[ "${NO_BUILD:-0}" != "1" || ! -f "$ELF" ]]; then
  echo "==> emit stateless_guest ELF"
  lake exe codegen --program stateless_guest --halt linux93 -o "$ELF_DIR/stateless_guest" >/dev/null
fi

# --- render the Lean mirror (gas values + handler labels) ----------------
echo "==> render Lean mirror (EvmAsm.Codegen.Proofs.OpcodeTables)"
# GH #12156. `mktemp --suffix=` is a GNU extension; BSD/macOS `mktemp` rejects
# it outright ("unrecognized option"). This line was unreachable on macOS until
# the tool-probe fix above let the gate get this far, so fixing one blocker
# exposed the next. `lake env lean --run` needs the `.lean` suffix, so allocate
# a temp DIRECTORY and name the file inside it — portable, and it also gives the
# `.err` file written at the `lake env lean --run` below a home that `cleanup`
# actually removes (the old `rm -f` list never mentioned "$LEAN_OUT.err").
TMPD="$(mktemp -d)"
LEAN_SNIPPET="$TMPD/opcode-tables-mirror.lean"
LEAN_OUT="$TMPD/lean-out"
DATA_BIN="$TMPD/data.bin"
cleanup() { rm -rf "$TMPD"; }
trap cleanup EXIT
cat > "$LEAN_SNIPPET" <<'LEAN'
import EvmAsm.Codegen.Proofs.GuestDataImage
open EvmAsm.Codegen
open EvmAsm.Codegen.Proofs.OpcodeTables
open EvmAsm.Codegen.Proofs.GuestDataImage
-- Render the LEAN MIRROR DEFS (not the emitter source) so any divergence
-- between EvmAsm/Codegen/Proofs/OpcodeTables.lean and the ELF is caught.
def main : IO Unit := do
  IO.println "GAS"
  for v in opcodeGasCostEntries do
    IO.println (toString v.toNat)
  IO.println "HANDLERS"
  for lbl in opcodeHandlerLabels do
    IO.println lbl
  -- GH #13229: the PINNED image, i.e. what `guestDataImage` asserts the loaded
  -- `.data` holds. Rendered from GuestDataImage, so the resolver chain
  -- (GuestAddrs -> handlerAddrRows -> guestHandlerAddr) is what gets compared.
  IO.println "LAYOUT"
  IO.println (toString RegionMap.dataRegion.base)
  IO.println (toString RegionMap.dataRegion.size)
  IO.println (toString GuestAddrs.opcode_gas_costs)
  IO.println (toString GuestAddrs.opcode_handlers)
  IO.println "PINGAS"
  for v in shippedGasCostTable do
    IO.println (toString v.toNat)
  IO.println "PINHANDLERS"
  for v in shippedHandlerTable do
    IO.println (toString v.toNat)
  IO.println "END"
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
# GH #13229: the section TYPE and SIZE are read out too, not just the base.
# PROGBITS is the load-bearing fact behind pinning `.data` at all (contrast
# `.bss`, which is NOBITS and therefore genuinely havoc at entry), and the size
# is what makes "the tables end exactly at the top of `.data`" checkable.
DATA_TYPE=""; DATA_BASE=""; DATA_SIZE=""
read -r DATA_TYPE DATA_BASE DATA_SIZE < <("$READELF" -SW "$ELF" | python3 -c "
import re,sys
for line in sys.stdin:
    m=re.search(r'\]\s+\.data\s+(\S+)\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)', line)
    if m:
        print(m.group(1), int(m.group(2),16), int(m.group(3),16)); break
") || true
# Fail with a REASON rather than letting `set -e` abort on a bare `read`
# returning 1: an unparsed section header is a gate defect, not a pass.
if [[ -z "$DATA_TYPE" || -z "$DATA_BASE" || -z "$DATA_SIZE" ]]; then
  echo "check-opcode-tables: could not parse the .data section header out of" >&2
  echo "  '$READELF -SW $ELF' -- refusing to check the tables against an ELF" >&2
  echo "  whose layout this gate cannot read." >&2
  exit 1
fi

# symbol -> address map (name<TAB>hexaddr) for the tables + every handler label.
SYMS="$("$READELF" -sW "$ELF" | awk '$1 ~ /^[0-9]+:$/ && NF>=8 {print $8"\t"$2}')"

rc=0
OPCODE_SYMS="$SYMS" python3 - "$ELF" "$DATA_BIN" "$DATA_BASE" "$LEAN_OUT" \
    "$DATA_TYPE" "$DATA_SIZE" <<'PY' || rc=$?
import sys
elf, data_bin, data_base, lean_out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
data_type, data_size = sys.argv[5], int(sys.argv[6])

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

# GH #13229, checked FIRST so it reports its own reason.  A NOBITS `.data`
# would also make `table_dwords` fail (empty blob), but with the unhelpful
# "outside .data blob" message -- and PROGBITS is the premise of the whole pin,
# not an incidental bounds fact, so it deserves to be named.
if data_type != "PROGBITS":
    sys.exit(f"check-opcode-tables: .data section type is {data_type}, not "
             "PROGBITS -- the loader would NOT copy these bytes in before "
             "_start, so EvmAsm/Codegen/Proofs/GuestDataImage.lean's pin of "
             "the two dispatch tables would be unsound (#13229)")

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

# --- GH #13229: the PINNED image ------------------------------------------
# Legs 1 and 2 above never leave the ELF's own symbol table, so they cannot
# see a break anywhere in GuestAddrs -> handlerAddrRows -> guestHandlerAddr.
# `guestDataImage` is an assertion about the loaded bytes; this compares its
# RENDERED contents, plus the geometry `dataTables_layout` proves in Lean,
# against the section the loader actually copies in.
li = lines.index("LAYOUT")
pgi = lines.index("PINGAS")
phi = lines.index("PINHANDLERS")
ei = lines.index("END")
lean_data_base, lean_data_size, lean_gas_base, lean_hnd_base = \
    [int(x) for x in lines[li+1:pgi]]
pin_gas = [int(x) for x in lines[pgi+1:phi]]
pin_hnd = [int(x) for x in lines[phi+1:ei]]
if len(pin_gas) != 256 or len(pin_hnd) != 256:
    sys.exit(f"check-opcode-tables: pinned image gave {len(pin_gas)}/{len(pin_hnd)} "
             "entries (want 256/256)")

pfail = 0
if (lean_data_base, lean_data_size) != (data_base, data_size):
    print(f"  DRIFT RegionMap.dataRegion = ({lean_data_base:#x}, {lean_data_size}) "
          f"but ELF .data = ({data_base:#x}, {data_size})")
    pfail = 1
if lean_gas_base != syms.get("opcode_gas_costs") or \
        lean_hnd_base != syms.get("opcode_handlers"):
    print(f"  DRIFT GuestAddrs table bases ({lean_gas_base:#x}, {lean_hnd_base:#x}) "
          f"!= ELF ({syms.get('opcode_gas_costs'):#x}, "
          f"{syms.get('opcode_handlers'):#x})")
    pfail = 1
# `dataTables_layout` as an ELF fact: adjacent, dword-aligned, and ending
# exactly at the top of `.data` -- so no trailing havoc'd fragment is mis-sized
# and every carve in GuestDataImage lands on a dword boundary (the free side of
# the #13011/#13014 stride line).
if (lean_gas_base - data_base) % 8 != 0:
    print(f"  DRIFT table pair is not dword-aligned inside .data "
          f"(offset {lean_gas_base - data_base})")
    pfail = 1
if lean_gas_base + 2048 != lean_hnd_base:
    print(f"  DRIFT tables are not adjacent: {lean_gas_base:#x}+2048 != "
          f"{lean_hnd_base:#x}")
    pfail = 1
if lean_hnd_base + 2048 != data_base + data_size:
    print(f"  DRIFT tables do not end at the top of .data: "
          f"{lean_hnd_base + 2048:#x} != {data_base + data_size:#x}")
    pfail = 1
for b in range(256):
    if gas_actual[b] != pin_gas[b]:
        print(f"  DRIFT pinned shippedGasCostTable[{b}]: ELF {gas_actual[b]} != "
              f"Lean {pin_gas[b]}")
        pfail = 1
    if hnd_actual[b] != pin_hnd[b]:
        print(f"  DRIFT pinned shippedHandlerTable[{b}]: ELF {hnd_actual[b]:#x} != "
              f"Lean {pin_hnd[b]:#x} (resolver chain broken: GuestAddrs -> "
              "handlerAddrRows -> guestHandlerAddr; a MISSING row renders as 0)")
        pfail = 1
if not pfail:
    print("  OK   GuestDataImage pin: .data is PROGBITS at "
          f"({data_base:#x}, {data_size}); both 256-dword tables are adjacent, "
          "dword-aligned, end at the top of .data, and hold exactly "
          "shippedGasCostTable / shippedHandlerTable")
fail |= pfail

sys.exit(1 if fail else 0)
PY

if [[ "$rc" != "0" ]]; then
  echo "check-opcode-tables: DRIFT detected (see above)"
  exit 1
fi
echo "check-opcode-tables: opcode tables match the linked ELF"
