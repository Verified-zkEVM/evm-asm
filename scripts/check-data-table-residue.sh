#!/usr/bin/env bash
# GH #13229 follow-up: the evidence behind the RESIDUE half of the `.data` pin.
#
# `EvmAsm/Codegen/Proofs/GuestDataImage.lean` pins the two dispatch tables
# inside the `.data` tile, and `GuestImage.guestResidue` therefore ASSERTS, in
# the `.64` postcondition, that the tables still hold the shipped bytes when
# the guest halts.  `guestDataScratch_strictly_stronger` proves that is a real
# obligation (an all-zero `.data` heap satisfies the old havoc'd tile and fails
# the pinned one), and `guestResidue_rejects_clobbered_tables` states it in its
# sharpest form.  Nothing in Lean discharges it: `runStatelessGuestSound_of_phases`
# still takes its six phase Props as hypotheses, so there is no whole-program
# write map to quantify over.
#
# This gate is the offline evidence, and it is deliberately derived from the
# LINKED image rather than from the emitter source or from any docstring —
# #13183 is the precedent for why (`dispatchLoop_prog` was anchored 348 bytes
# off while both the `_eq_prog` `rfl` pin and `asm_cmp=IDENTICAL` read green).
#
# Five legs, each a separate claim:
#
#   1. LAYOUT.  In the linked ELF, `.data` is PROGBITS, the two table symbols
#      sit where `GuestAddrs` says, and the pair ends exactly at the top of
#      `.data`.  ⚠️ Every `.data` symbol in this image has st_size = 0 (the
#      emitter writes no `.size` directives), so "no other symbol lives in the
#      range" CANNOT be read off symbol extents.  It is checked in the only
#      form the symbol table supports: no symbol ADDRESS lies strictly inside
#      the range.  The neighbour-overhang question that leaves open is leg 5's.
#
#   2. ASM REFERENCES.  Across the WHOLE emitted assembly — not a grep over
#      `Codegen/Programs/*.lean`, which would miss `String`-emitted snippets
#      and handler bodies that never became `Program`s — each table symbol is
#      mentioned exactly twice: its definition label and one `la`.  Both `la`
#      destinations are consumed by an `ld`, never by a store.
#
#   3. MATERIALISED ADDRESSES.  In the linked disassembly, exactly two
#      instructions produce a constant inside the range, both completing an
#      `auipc`/`lui` pair, both inside `.dispatch_loop_body`.
#
#   4. UNPAIRED HIGH HALVES.  Leg 3 trusts objdump's pair annotation, so every
#      `auipc`/`lui` whose successor objdump did NOT annotate is checked
#      separately: its page window `[base-2048, base+2047]` — the full reach of
#      any later `addi` — must miss the range.  Note RV64 `lui` SIGN-EXTENDS
#      bit 31, so a bare `lui` can never yield a `0xa0b0_xxxx` address at all
#      (it yields `0xffffffff_a0b0_xxxx`); only `auipc` reaches the RAM zone,
#      and the negative control for this leg has to be written with `auipc`.
#
#   5. STORE REACHABILITY.  Intra-block constant propagation over every store
#      in `.text`.  FAIL if any store's resolved target lands in the range, and
#      FAIL if any store's base is a `.data` address plus a runtime term (the
#      mechanism by which an over-long write to a neighbouring object would
#      reach the tables without naming the symbol).  Stores whose base the
#      analysis cannot resolve are REPORTED, not failed on: they are the honest
#      residual gap, and a count-based ratchet on them would only turn `main`
#      red as the guest grows.  A base that is a known anchor plus a runtime
#      term counts as UNRESOLVED even when the anchor is outside `.data` — the
#      runtime term is unbounded here, so the anchor certifies nothing.
#
# A note on the static side of the neighbour question, which needs no leg of
# its own: symbols in a linker-laid-out section mark positions in one
# contiguous byte stream, and `scripts/check-opcode-tables.sh` already compares
# all 2048 bytes at each table base against the Lean image.  So no neighbouring
# object's bytes can statically occupy the range.  (Measured on this image, the
# object below — `bls12_g2_msm_discount_table` at 0xa0b03f10 — emits exactly
# 128 `.quad`s, ending precisely at `opcode_gas_costs`.)  The only overhang
# that remains possible is DYNAMIC, and that is what leg 5's anchor+runtime
# failure covers.
#
# Each leg was checked against a negative control that makes it FAIL, with the
# expected reason, before the gate was wired: a store resolving into the range;
# a second `la` on a table symbol; an `la` feeding a store; a third symbol
# placed inside the range; `.data` declared NOBITS; an unpaired `auipc` whose
# page window overlaps the range; the tables no longer ending at the top of
# `.data`; and a store based on the neighbouring `bls12_g2_msm_discount_table`
# plus a runtime index.  All eight fired.
#
# Wired into scripts/check-build-parallel.sh's codegen lane.  Skips gracefully
# (exit 0) without the RISC-V toolchain, hard-fails under CI, mirroring
# scripts/check-opcode-tables.sh (#12156).
set -euo pipefail
cd "$(dirname "$0")/.."

# shellcheck source=lib/riscv-tools.sh
source "$(dirname "$0")/lib/riscv-tools.sh"

if ! require_riscv_tools_or_skip check-data-table-residue readelf objdump; then
  if [[ -n "${CI:-}" ]]; then
    echo "check-data-table-residue: FAILING rather than skipping — CI installs" >&2
    echo "  the RISC-V toolchain, so a miss here means the environment" >&2
    echo "  regressed (#12156); a skip that reads as a pass is what this gate" >&2
    echo "  is for." >&2
    exit 1
  fi
  exit 0
fi
READELF="$RISCV_RESOLVED_READELF"
OBJDUMP="$RISCV_RESOLVED_OBJDUMP"

ELF_DIR="${ELF_DIR:-gen-out/datatableresidue}"
ELF="$ELF_DIR/stateless_guest.elf"
ASM="$ELF_DIR/stateless_guest.s"
mkdir -p "$ELF_DIR"
if [[ "${NO_BUILD:-0}" != "1" || ! -f "$ELF" || ! -f "$ASM" ]]; then
  echo "==> emit stateless_guest ELF + asm"
  lake exe codegen --program stateless_guest --halt linux93 \
    -o "$ELF_DIR/stateless_guest" >/dev/null
fi

TMPD="$(mktemp -d)"
cleanup() { rm -rf "$TMPD"; }
trap cleanup EXIT

echo "==> disassemble linked .text"
"$OBJDUMP" -d --no-show-raw-insn "$ELF" > "$TMPD/disasm.txt"
"$READELF" -SW "$ELF" > "$TMPD/sections.txt"
"$READELF" -sW "$ELF" > "$TMPD/symbols.txt"

python3 - "$TMPD/sections.txt" "$TMPD/symbols.txt" "$TMPD/disasm.txt" "$ASM" <<'PY'
import re, sys

sections_f, symbols_f, disasm_f, asm_f = sys.argv[1:5]
GAS_SYM, HND_SYM = "opcode_gas_costs", "opcode_handlers"
TABLE_BYTES = 8 * 256
M = (1 << 64) - 1
fail = 0


def bad(msg):
    global fail
    fail = 1
    print("  DRIFT " + msg)


# ---------------------------------------------------------------- leg 1
data_type = data_base = data_size = None
for line in open(sections_f):
    m = re.search(r"\]\s+\.data\s+(\S+)\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)", line)
    if m:
        data_type, data_base, data_size = m.group(1), int(m.group(2), 16), int(m.group(3), 16)
        break
if data_type is None:
    sys.exit("check-data-table-residue: could not parse the .data section header")

syms = []            # (addr, size, name)
for line in open(symbols_f):
    p = line.split()
    if len(p) >= 8 and p[0].endswith(":"):
        try:
            syms.append((int(p[1], 16), int(p[2]), p[7]))
        except ValueError:
            continue
byname = {}
for a, s, n in syms:
    byname.setdefault(n, (a, s))

if data_type != "PROGBITS":
    bad(f".data is {data_type}, not PROGBITS — the loader would not copy these "
        "bytes in before _start and the pin would be unsound")
for s in (GAS_SYM, HND_SYM):
    if s not in byname:
        sys.exit(f"check-data-table-residue: {s} not in the ELF symtab")
lo = byname[GAS_SYM][0]
hi = data_base + data_size
if byname[HND_SYM][0] != lo + TABLE_BYTES:
    bad(f"tables not adjacent: {lo:#x}+{TABLE_BYTES} != {byname[HND_SYM][0]:#x}")
if byname[HND_SYM][0] + TABLE_BYTES != hi:
    bad(f"tables do not end at the top of .data: "
        f"{byname[HND_SYM][0] + TABLE_BYTES:#x} != {hi:#x}")

# The size==0 caveat, stated rather than assumed away.
sized = [(a, s, n) for a, s, n in syms if data_base <= a < hi and s != 0]
interior = sorted({(a, n) for a, s, n in syms
                   if lo < a < hi and n not in (GAS_SYM, HND_SYM)})
if interior:
    for a, n in interior:
        bad(f"symbol {n} at {a:#x} lives inside the pinned table range "
            f"[{lo:#x}, {hi:#x})")
below = sorted(a for a, s, n in syms if data_base <= a < lo)
prev = below[-1] if below else None
prev_names = sorted(n for a, s, n in syms if a == prev) if prev is not None else []
print(f"  OK   layout: .data is PROGBITS at ({data_base:#x}, {data_size}); the "
      f"table pair occupies [{lo:#x}, {hi:#x}) and ends at the top of .data; "
      f"no other symbol address lies inside it")
print(f"       note: {len(sized)} of the {sum(1 for a, s, n in syms if data_base <= a < hi)} "
      f".data symbols carry a nonzero st_size, so extents are NOT readable "
      f"from the symbol table; the nearest object below is "
      f"{'/'.join(prev_names)} at {prev:#x}" if prev is not None else "")

# ---------------------------------------------------------------- leg 2
asm = open(asm_f).read().splitlines()
STORE_MN = re.compile(r"^\s*(sd|sw|sh|sb|fsd|fsw|amo\w+|sc\.\w+)\b")
for sym in (GAS_SYM, HND_SYM):
    hits = [(i, l) for i, l in enumerate(asm) if re.search(rf"\b{sym}\b", l)]
    defs = [(i, l) for i, l in hits if re.match(rf"^\s*{sym}\s*:", l)]
    las = [(i, l) for i, l in hits if re.search(rf"^\s*la\s+\w+\s*,\s*{sym}\s*$", l)]
    if len(hits) != 2 or len(defs) != 1 or len(las) != 1:
        bad(f"{sym}: expected exactly one definition label and one `la` across "
            f"the whole emitted asm, found {len(hits)} mentions "
            f"({len(defs)} labels, {len(las)} `la`s)")
        for i, l in hits:
            print(f"         {asm_f}:{i + 1}: {l.strip()}")
        continue
    i, l = las[0]
    reg = re.match(r"^\s*la\s+(\w+)\s*,", l).group(1)
    # walk forward until the register is redefined; every use must be a read
    consumed_by_load = False
    for j in range(i + 1, min(i + 12, len(asm))):
        line = asm[j]
        if STORE_MN.match(line) and re.search(rf"\({reg}\)", line):
            bad(f"{sym}: `la {reg}` at {asm_f}:{i + 1} feeds a STORE at "
                f"{asm_f}:{j + 1}: {line.strip()}")
            break
        if re.search(rf"^\s*ld\s+\w+\s*,\s*-?\d*\(\s*{reg}\s*\)", line):
            consumed_by_load = True
            break
        if re.match(rf"^\s*\w+\s+{reg}\s*,", line) and not re.match(
                rf"^\s*add\s+{reg}\s*,\s*{reg}\s*,", line):
            break            # register redefined by something other than the index add
    if not consumed_by_load:
        bad(f"{sym}: could not see the `la` at {asm_f}:{i + 1} being consumed by "
            "an `ld` — the read-only argument no longer holds by inspection")
if not fail:
    print(f"  OK   emitted asm: each table symbol appears exactly twice "
          f"(definition + one `la`), and both `la`s feed an `ld`")

# ---------------------------------------------------------------- legs 3-5
INSN = re.compile(r"^\s*([0-9a-f]+):\t(\S+)\s*(.*?)\s*(?:#\s*([0-9a-f]+)\s.*)?$")
LABEL = re.compile(r"^([0-9a-f]{16}) <(.+)>:$")
NOWRITE = {"sd", "sw", "sh", "sb", "fsd", "fsw", "beq", "bne", "blt", "bge",
           "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz", "bgtz",
           "bgt", "ble", "bgtu", "bleu", "j", "ret", "ecall", "ebreak", "nop",
           "fence", "unimp"}
STORES = {"sd", "sw", "sh", "sb", "fsd", "fsw"}

insns = []       # (addr|None, mnemonic, operands, annotation|None, label|None)
for L in open(disasm_f):
    m = INSN.match(L)
    if m:
        insns.append((int(m.group(1), 16), m.group(2), m.group(3).strip(),
                      int(m.group(4), 16) if m.group(4) else None, None))
        continue
    m = LABEL.match(L.strip())
    if m:
        insns.append((None, "LABEL", m.group(2), None, m.group(2)))

targets = set()
for a, mn, ops, _, _ in insns:
    if a is None:
        continue
    for t in re.findall(r"\b([0-9a-f]{8,16})\b <", ops):
        targets.add(int(t, 16))

# leg 3: annotated constants inside the range
cur_label = "?"
label_of = {}
for a, mn, ops, ann, lab in insns:
    if lab is not None:
        cur_label = lab
    elif a is not None:
        label_of[a] = cur_label
inrange = [(a, mn, ops) for a, mn, ops, ann, _ in insns
           if ann is not None and lo <= ann < hi]
if len(inrange) != 2:
    bad(f"expected exactly 2 instructions materialising an address in "
        f"[{lo:#x}, {hi:#x}), found {len(inrange)}")
    for a, mn, ops in inrange:
        print(f"         {a:#x} <{label_of.get(a, '?')}>: {mn} {ops}")
else:
    labs = {label_of.get(a, "?") for a, _, _ in inrange}
    print(f"  OK   linked .text: exactly 2 materialised addresses in the range, "
          f"at {' and '.join(f'{a:#x}' for a, _, _ in inrange)} "
          f"({', '.join(sorted(labs))})")

# leg 4: unpaired high halves
unpaired_reach = []
for i, (a, mn, ops, ann, _) in enumerate(insns):
    if mn not in ("auipc", "lui") or a is None:
        continue
    nxt = insns[i + 1] if i + 1 < len(insns) else None
    if nxt is not None and nxt[3] is not None:
        continue                       # objdump resolved the pair
    m = re.match(r"(\w+),(0x[0-9a-f]+|\d+)$", ops)
    if not m:
        bad(f"unparsable {mn} at {a:#x}: {ops!r} — refusing to certify a range "
            "this gate cannot read")
        continue
    imm = int(m.group(2), 0)
    base = (imm << 12) if mn == "lui" else a + (imm << 12)
    if mn == "lui" and base & (1 << 31):
        base |= ~((1 << 32) - 1)
    base &= M
    if base - 2048 < hi and base + 2047 >= lo:
        unpaired_reach.append((a, mn, ops, base))
if unpaired_reach:
    for a, mn, ops, base in unpaired_reach:
        bad(f"unpaired {mn} at {a:#x} ({ops}) yields {base:#x}; a later `addi` "
            "could reach the pinned range")
else:
    print("  OK   every unpaired auipc/lui has a ±2048 window disjoint from the "
          "range")

# leg 5: store reachability
env = {}
resolved_data, sym_data = [], []
unresolved = exact_elsewhere = total_stores = 0
for a, mn, ops, ann, lab in insns:
    if a is None or a in targets:
        env = {}
    if mn == "LABEL":
        env = {}
        continue
    ps = [x.strip() for x in ops.split(",")]
    try:
        if mn in ("auipc", "lui"):
            imm = int(ps[1], 0)
            v = imm << 12
            if mn == "lui":
                if v & (1 << 31):
                    v |= ~((1 << 32) - 1)
            else:
                v = a + v
            env[ps[0]] = ("C", v & M)
        elif mn in ("addi", "addiw") and len(ps) == 3:
            src, imm = env.get(ps[1]), int(ps[2], 0)
            if src:
                env[ps[0]] = (src[0], (src[1] + imm) & M)
            elif ps[1] == "zero":
                env[ps[0]] = ("C", imm & M)
            else:
                env.pop(ps[0], None)
        elif mn == "li" and len(ps) == 2:
            env[ps[0]] = ("C", int(ps[1], 0) & M)
        elif mn == "mv" and len(ps) == 2:
            if ps[1] in env:
                env[ps[0]] = env[ps[1]]
            else:
                env.pop(ps[0], None)
        elif mn in ("add", "addw") and len(ps) == 3:
            s1, s2 = env.get(ps[1]), env.get(ps[2])
            if s1 and s1[0] == "C" and s2 and s2[0] == "C":
                env[ps[0]] = ("C", (s1[1] + s2[1]) & M)
            elif s1:
                env[ps[0]] = ("S", s1[1])
            elif s2:
                env[ps[0]] = ("S", s2[1])
            else:
                env.pop(ps[0], None)
        elif mn not in NOWRITE and ps and re.match(r"^[a-z]+\d*$", ps[0]):
            env.pop(ps[0], None)
    except (ValueError, IndexError):
        if ps:
            env.pop(ps[0], None)
    if mn in STORES or mn.startswith("amo") or mn.startswith("sc."):
        total_stores += 1
        m = re.match(r"[a-z0-9]+,(-?\d+)\(([a-z0-9]+)\)$", ops)
        if not m:
            unresolved += 1
            continue
        base, off = env.get(m.group(2)), int(m.group(1))
        if base is None:
            unresolved += 1
        elif base[0] == "C":
            tgt = (base[1] + off) & M
            if data_base <= tgt < hi:
                resolved_data.append((a, ops, tgt))
            else:
                exact_elsewhere += 1
        else:
            # base = a known anchor PLUS a runtime term.  An anchor outside
            # `.data` does NOT certify the store: the runtime term is unbounded
            # by this analysis, so these count as uncertified.  What IS a hard
            # failure is an anchor inside `.data` — that is exactly the
            # over-long-write-to-a-neighbour shape.
            anchor = (base[1] + off) & M
            if data_base <= anchor < hi or data_base <= base[1] < hi:
                sym_data.append((a, ops, anchor))
            else:
                unresolved += 1

reaching = [(a, ops, t) for a, ops, t in resolved_data if lo <= t < hi]
for a, ops, t in reaching:
    bad(f"store at {a:#x} ({ops}) resolves to {t:#x}, inside the pinned range")
for a, ops, t in sym_data:
    bad(f"store at {a:#x} ({ops}) has a .data base ({t:#x}) plus a RUNTIME "
        "term — it could reach the tables without naming the symbol")
if not reaching and not sym_data:
    top = max((t for _, _, t in resolved_data), default=data_base)
    certified = len(resolved_data) + exact_elsewhere
    print(f"  OK   stores: of {total_stores} store sites, {certified} have a "
          f"fully constant address; {len(resolved_data)} of those land in "
          f".data, all at or below {top:#x} — {lo - top} bytes clear of the gas "
          f"table — and none has a .data anchor plus a runtime index")
print(f"       gap: {unresolved} of the {total_stores} store sites are NOT "
      "certified by this gate — the base is unresolvable (sp, call-crossing "
      "pointers, values loaded from memory) or is a known anchor plus an "
      "unbounded runtime term. Closing them needs a whole-program write map, "
      "which is why the Lean side STATES the obligation "
      "(GuestImage.guestResidue_rejects_clobbered_tables) rather than proving "
      "it.")

sys.exit(1 if fail else 0)
PY
rc=$?

if [[ "$rc" != "0" ]]; then
  echo "check-data-table-residue: the residue evidence for the .data pin no"
  echo "  longer holds (see above). Either the guest gained a way to reach"
  echo "  [opcode_gas_costs, .data end), or the layout moved; in the first case"
  echo "  EvmAsm/Codegen/Proofs/GuestImage.lean's guestResidue is no longer"
  echo "  defensible and #13229's pin must be revisited."
  exit 1
fi
echo "check-data-table-residue: the pinned .data tables are unreachable by every"
echo "  store this gate can resolve, and referenced exactly twice, both reads"
