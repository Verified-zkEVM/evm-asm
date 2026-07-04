/-
  EvmAsm.Codegen.Proofs.OpcodeTables

  Drift-guarded load spec for the dispatcher's `.data` opcode tables
  (`opcode_handlers` / `opcode_gas_costs`), bead evm-asm-4ch8f.10.2.

  The runtime dispatch loop (EvmAsm/Codegen/Dispatch.lean) fetches an
  opcode byte, then indexes two 256-entry, 8-byte-stride `.data` tables:

      slli x5, x5, 3          -- x5 := op * 8
      la   x6, opcode_gas_costs / opcode_handlers
      add  x6, x6, x5
      ld   xD, 0(x6)          -- xD := table[op]

  Both tables are plain 256 x .dword arrays (`emitGasCostTable`,
  `emitJumpTable`).  This file proves, bottom-up:

  1. A GENERIC, address-free ro-table load lemma (`exec_table_load`):
     for any read-only `Region` whose byte slice at `tOff` mirrors a
     `List Word` as a little-endian dword table (`tableAt`), the
     `slli/add/ld` block loads `entries[op]`.  Reusable over `region`,
     `tOff`, `entries`, `op < entries.length`.

  2. The concrete table mirrors: `opcodeGasCostEntries : List Word`
     (numeric, from `staticGasCost`) and `opcodeHandlerLabels`
     (link-resolved handler labels, from `jumpTargetLabel` over the
     SHIPPED `callFrameGuestRegistry`), each of length 256.  Because the
     handler labels (`h_ADD`, …, `h_invalid`) are NOT `GuestAddrs`
     constants (they are emitted by the raw table string, not a `_prog`),
     the address image is parameterized by an `addrOf : String -> Word`
     resolver (`opcodeHandlerEntries`); a link-layout regen flows through
     the resolver rather than through baked literals.

  3. The `.pre`-witness bridge (`handler_table_load_witness`): the
     `callRegS` obligation `rf.get rs = opcodeHandlerEntries[op]` that
     bead evm-asm-4ch8f.49 consumes.  Stated against the entries list so
     the .10.1 handle family's `entry` fields plug in by list-lookup — no
     existential escape.

  The Lean mirror is kept honest against the shipped ELF by
  `scripts/check-opcode-tables.sh` (the RegionMap drift-guard pattern):
  it reads the 2048 bytes at each symbol and compares them to these defs.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Sym
import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmRegistry

namespace EvmAsm.Codegen.Proofs.OpcodeTables

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

-- ============================================================================
-- Layer 1: generic ro-table load (address-free, reusable)
-- ============================================================================

/-- The little-endian byte image of a dword table mirroring `entries`. -/
def tableBytes (entries : List Word) : List (BitVec 8) :=
  entries.flatMap dwordBytes

@[simp] theorem tableBytes_nil : tableBytes [] = [] := rfl

theorem tableBytes_cons (e : Word) (es : List Word) :
    tableBytes (e :: es) = dwordBytes e ++ tableBytes es := by
  simp [tableBytes]

@[simp] theorem length_tableBytes (entries : List Word) :
    (tableBytes entries).length = 8 * entries.length := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    rw [tableBytes_cons, List.length_append, length_dwordBytes, ih,
      List.length_cons]
    omega

/-- The `i`-th dword of the table image, sliced out as its 8 bytes. -/
theorem tableBytes_slice (entries : List Word) (i : Nat)
    (hi : i < entries.length) :
    ((tableBytes entries).drop (8 * i)).take 8 = dwordBytes entries[i] := by
  induction entries generalizing i with
  | nil => exact absurd hi (by simp)
  | cons e es ih =>
    rw [tableBytes_cons]
    match i with
    | 0 =>
      simp only [Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
      exact take8_dword_append e (tableBytes es)
    | j + 1 =>
      have hj : j < es.length := by
        rw [List.length_cons] at hi; omega
      have h8 : 8 * (j + 1) = 8 + 8 * j := by ring
      rw [h8, drop8_dword_append e (tableBytes es) (8 * j),
        List.getElem_cons_succ]
      exact ih j hj

/-- `tableAt region tOff entries`: the little-endian dword image of
    `entries` is a prefix of the read-only region's bytes starting at
    byte offset `tOff` — i.e. the region's byte slice at `tOff` *is*
    `entries.flatMap dwordBytes` (with whatever `.data` follows the
    table left unconstrained).  This is the `List`-level pinning the
    drift guard checks against the linked ELF. -/
def tableAt (region : Region) (tOff : Nat) (entries : List Word) : Prop :=
  tableBytes entries <+: region.bytes.drop tOff

/-- From the table pinning, read the `i`-th dword's 8 bytes directly out
    of the region bytes at absolute offset `tOff + 8*i`. -/
theorem tableAt_slice {region : Region} {tOff : Nat} {entries : List Word}
    (h : tableAt region tOff entries) (i : Nat) (hi : i < entries.length) :
    (region.bytes.drop (tOff + 8 * i)).take 8 = dwordBytes entries[i] := by
  obtain ⟨rest, hrest⟩ := h
  have hlen : 8 * i ≤ (tableBytes entries).length := by
    rw [length_tableBytes]; omega
  have hlen8 : 8 ≤ ((tableBytes entries).drop (8 * i)).length := by
    rw [List.length_drop, length_tableBytes]; omega
  -- Peel the leading `tOff` bytes, then the first `8*i` table bytes.
  rw [← List.drop_drop, ← hrest,
    List.drop_append_of_le_length hlen,
    List.take_append_of_le_length hlen8]
  exact tableBytes_slice entries i hi

/-- The read-only dword read at `tOff + 8*i` returns `entries[i]`. -/
theorem tableAt_dwordAt {region : Region} {tOff : Nat} {entries : List Word}
    (h : tableAt region tOff entries) (i : Nat) (hi : i < entries.length)
    {addr : Word} (haddr : (addr - region.base).toNat = tOff + 8 * i) :
    region.dwordAt addr = entries[i] := by
  unfold Region.dwordAt
  rw [haddr, tableAt_slice h i hi, packBytes_dwordBytes]

/-- The read-only analog of `execInstrRF_ld_dword`: an `LD` whose address
    misses the writable window reads the read-only region's dword. -/
theorem execInstrRF_ld_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs)
      = (rf.set rd (ro.dwordAt (rf.get rs1 + signExtend12 ofs)), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- `signExtend12 0 = 0` (used to collapse the `ld … 0(rB)` offset). -/
theorem signExtend12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by
  decide

/-- Shift-by-3 realizes the `* 8` index scaling (`slli xI, xI, 3`). -/
theorem ofNat_shiftLeft_three (op : Nat) :
    (BitVec.ofNat 64 op) <<< (3 : Nat) = BitVec.ofNat 64 (op * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega

/-- The `slli/add/ld` table-load block, as executed by the SAsm engine. -/
def tableLoadBlock (idxR baseR dstR : Reg) : List Instr :=
  [.SLLI idxR idxR 3, .ADD baseR baseR idxR, .LD dstR baseR 0]

/-- **Generic ro-table load.**  With the opcode in `idxR`, the table base
    (`region.base + tOff`) in `baseR`, and the table pinned by `tableAt`,
    the `slli/add/ld` block loads `entries[op]` into `dstR` and leaves the
    writable window unchanged.  Address-free: nothing about the linked
    layout appears — `.49` discharges `hbase`/`hnorw` from its region
    setup.  Registers: `idxR` is scaled into the address, so it must
    differ from `baseR`; `baseR` may alias `dstR` (the gas-table load
    reuses `x6`), and `dstR` may alias `idxR`. -/
theorem exec_table_load
    (region : Region) (rwBase : Word) (rf : RegFile) (ws : List (BitVec 8))
    (idxR baseR dstR : Reg) (tOff op : Nat) (entries : List Word)
    (hop : op < entries.length)
    (hidx : rf.get idxR = BitVec.ofNat 64 op)
    (hbase : rf.get baseR = region.base + BitVec.ofNat 64 tOff)
    (htab : tableAt region tOff entries)
    (hfit : tOff + 8 * entries.length ≤ region.bytes.length)
    (hwrap : region.base.toNat + region.bytes.length < 2 ^ 64)
    (hib : idxR ≠ baseR)
    (hidx0 : idxR ≠ .x0) (hbase0 : baseR ≠ .x0) (hdst0 : dstR ≠ .x0)
    (hnorw : ¬ inRw rwBase ws
        (region.base + BitVec.ofNat 64 tOff + BitVec.ofNat 64 (op * 8)) 8) :
    (execBlock region rwBase rf ws (tableLoadBlock idxR baseR dstR)).1.get dstR
        = entries[op]
      ∧ (execBlock region rwBase rf ws (tableLoadBlock idxR baseR dstR)).2 = ws := by
  -- Bounds: the whole indexed access sits inside the region.
  have hlt : tOff + 8 * op < 2 ^ 64 := by
    have : 8 * op < 8 * entries.length := by omega
    omega
  -- After SLLI: idxR holds op * 8.
  have hshift : rf.get idxR <<< (3 : BitVec 6).toNat = BitVec.ofNat 64 (op * 8) := by
    rw [hidx]; exact ofNat_shiftLeft_three op
  -- Address of the LD after SLLI + ADD.
  set addr : Word := region.base + BitVec.ofNat 64 tOff + BitVec.ofNat 64 (op * 8)
    with haddr_def
  have haddr_toNat : (addr - region.base).toNat = tOff + 8 * op := by
    rw [haddr_def]; bv_omega
  -- Execute the three instructions.
  unfold tableLoadBlock
  rw [execBlock_cons]
  -- Step 1: SLLI idxR idxR 3.
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  -- Step 2: ADD baseR baseR idxR.
  dsimp only [execInstrRF, aluSem]
  -- The address materialized in `baseR` after `slli`+`add`.
  set rf2 : RegFile :=
    (rf.set idxR (rf.get idxR <<< (3 : BitVec 6).toNat)).set baseR
      ((rf.set idxR (rf.get idxR <<< (3 : BitVec 6).toNat)).get baseR +
        (rf.set idxR (rf.get idxR <<< (3 : BitVec 6).toNat)).get idxR)
    with hrf2_def
  have hbaseR : rf2.get baseR = addr := by
    rw [hrf2_def, RegFile.get_set_self _ _ _ hbase0,
      RegFile.get_set_ne _ _ _ _ (Ne.symm hib), hbase,
      RegFile.get_set_self _ _ _ hidx0, hshift, haddr_def]
  have hldaddr : rf2.get baseR + signExtend12 (0 : BitVec 12) = addr := by
    rw [hbaseR, signExtend12_zero]; bv_omega
  -- Step 3: LD dstR baseR 0 — misses the window, reads the ro table.
  rw [execBlock_cons, execInstrRF_ld_ro region rwBase rf2 ws dstR baseR 0
      (by rw [hldaddr]; exact hnorw), execBlock_nil]
  refine ⟨?_, rfl⟩
  rw [RegFile.get_set_self _ _ _ hdst0, hldaddr]
  exact tableAt_dwordAt htab op hop haddr_toNat

-- ============================================================================
-- Layer 2: the concrete table mirrors (drift-guarded against the ELF)
-- ============================================================================

/-- The 256-entry static gas-cost table as a `List Word`, mirroring
    `emitGasCostTable` (`.dword {staticGasCost b}` for `b = 0..255`).
    Fully concrete — the drift guard compares these numbers against the
    dwords at the `opcode_gas_costs` symbol. -/
def opcodeGasCostEntries : List Word :=
  (List.range 256).map (fun b => BitVec.ofNat 64 (staticGasCost b))

/-- The 256 handler labels the jump table dispatches to, mirroring
    `emitJumpTable callFrameGuestRegistry` (`.dword {jumpTargetLabel …}`
    for `b = 0..255`).  Derived from the SHIPPED guest registry, so a
    link-layout regen changes only the *addresses* the labels resolve to,
    never this list.  The labels (`h_ADD`, …, `h_invalid`) are not
    `GuestAddrs` constants (they are emitted by the raw table string, not
    a converted `_prog`), so the addressed image is a function of the
    link-time resolver — see `opcodeHandlerEntries`. -/
def opcodeHandlerLabels : List String :=
  (List.range 256).map (fun b => jumpTargetLabel callFrameGuestRegistry b)

/-- The `opcode_handlers` table as a `List Word`, resolved through a
    link-address map `addrOf : String → Word`.  The drift guard supplies
    `addrOf` = the ELF symbol table; bead evm-asm-4ch8f.49 supplies
    `addrOf` = the .10.1 handle family's entry map (so
    `opcodeHandlerEntries addrOf` and `handlers` agree by list-lookup). -/
def opcodeHandlerEntries (addrOf : String → Word) : List Word :=
  opcodeHandlerLabels.map addrOf

-- Both tables are exactly 256 entries — the invariant the emitter
-- (`List.range 256`) and the ELF (2 KiB / 8) both hold.
#guard opcodeGasCostEntries.length = 256
#guard opcodeHandlerLabels.length = 256

@[simp] theorem length_opcodeGasCostEntries :
    opcodeGasCostEntries.length = 256 := by
  simp [opcodeGasCostEntries]

@[simp] theorem length_opcodeHandlerLabels :
    opcodeHandlerLabels.length = 256 := by
  simp [opcodeHandlerLabels]

@[simp] theorem length_opcodeHandlerEntries (addrOf : String → Word) :
    (opcodeHandlerEntries addrOf).length = 256 := by
  simp [opcodeHandlerEntries]

/-- The `op`-th handler entry is the resolved address of the `op`-th
    label — the equation bead evm-asm-4ch8f.49 connects to a handle's
    `entry` field. -/
theorem opcodeHandlerEntries_get (addrOf : String → Word) (op : Nat)
    (hop : op < 256) :
    (opcodeHandlerEntries addrOf)[op]'(by simp [hop])
      = addrOf (opcodeHandlerLabels[op]'(by simp [hop])) := by
  simp only [opcodeHandlerEntries, List.getElem_map]

-- ============================================================================
-- Layer 4: the `.pre`-witness bridge consumed by bead evm-asm-4ch8f.49
-- ============================================================================

/-- **Handler-table load witness.**  Specializes `exec_table_load` to the
    `opcode_handlers` mirror: after the dispatch loop's `slli/add/ld`, the
    handler-address register `dstR` holds `opcodeHandlerEntries addrOf`'s
    `op`-th entry.  This is the `callRegS` `.pre` obligation
    (`rf.get dstR = opcodeHandlerEntries[op]`); no existential — the
    entry is a concrete list lookup, so a `.10.1` handle whose `entry`
    equals this value plugs in by `rfl`/`opcodeHandlerEntries_get`. -/
theorem handler_table_load_witness
    (region : Region) (rwBase : Word) (rf : RegFile) (ws : List (BitVec 8))
    (idxR baseR dstR : Reg) (tOff op : Nat) (addrOf : String → Word)
    (hop : op < 256)
    (hidx : rf.get idxR = BitVec.ofNat 64 op)
    (hbase : rf.get baseR = region.base + BitVec.ofNat 64 tOff)
    (htab : tableAt region tOff (opcodeHandlerEntries addrOf))
    (hfit : tOff + 8 * 256 ≤ region.bytes.length)
    (hwrap : region.base.toNat + region.bytes.length < 2 ^ 64)
    (hib : idxR ≠ baseR)
    (hidx0 : idxR ≠ .x0) (hbase0 : baseR ≠ .x0) (hdst0 : dstR ≠ .x0)
    (hnorw : ¬ inRw rwBase ws
        (region.base + BitVec.ofNat 64 tOff + BitVec.ofNat 64 (op * 8)) 8) :
    (execBlock region rwBase rf ws (tableLoadBlock idxR baseR dstR)).1.get dstR
      = addrOf (opcodeHandlerLabels[op]'(by simp [hop])) := by
  have hoplen : op < (opcodeHandlerEntries addrOf).length := by
    rw [length_opcodeHandlerEntries]; exact hop
  have hfit' : tOff + 8 * (opcodeHandlerEntries addrOf).length
      ≤ region.bytes.length := by
    rw [length_opcodeHandlerEntries]; exact hfit
  have h := (exec_table_load region rwBase rf ws idxR baseR dstR tOff op
    (opcodeHandlerEntries addrOf) hoplen hidx hbase htab hfit' hwrap
    hib hidx0 hbase0 hdst0 hnorw).1
  rw [h, opcodeHandlerEntries_get addrOf op hop]
