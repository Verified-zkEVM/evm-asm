/-
  EvmAsm.Rv64.SAsm.GlobalData

  **The global-data footprint model** (bead evm-asm-85699; subsumes
  4ch8f.59.1.1 "AUIPC in SAsm blocks").

  Routines on the parser/secp/field layer reference global `.data` —
  read-only constants (`secp256k1_p_be`, …) and RW scratch cells
  (`rfu_offset`, `mle_*`/`mee_*` out cells) — materialized with the `la`
  idiom (`auipc`+`addi`, resolved by `EvmAsm/Rv64/LaResolve.lean`).  Two
  pieces here:

  ## 1. The PC-aware block engine (`execInstrRFAt`/`blockVCsAt`)

  The existing SAsm block engine (`execInstrRF`/`execBlock`/`blockVCs`) is
  PC-blind, so it cannot step `AUIPC`.  This module adds a PARALLEL
  PC-threaded engine — the original defs are untouched, so every existing
  block verifies exactly as before (conservativity is also proven:
  `execBlockAt_eq_execBlock` / `blockVCsAt_iff_blockVCs` on AUIPC-free
  blocks) — with `AUIPC` executed against the instruction's own address
  (blocks are contiguous, so instruction `k` of a block at `base` sits at
  `base + 4k`).  `execBlockAt_sound` is the block-soundness theorem at
  `cpsTripleWithin` level, the PC-aware analogue of `execBlock_sound`.

  ## 2. Global-data region assertions

  Plain separation-logic packaging for `.data` footprints, composable
  through `**` with `frameSlotsOwn`/`stackFree`/caller regions (they sit at
  fixed link addresses, disjointness is by the separating conjunction —
  no new hole):

  * `globalConst addr bs` — a read-only constant global: the routine's pre
    AND post carry the same known bytes, so any spec built over it
    genuinely preserves the constant;
  * `globalCellIs addr v` / `globalCellOwn addr` — an RW scratch dword
    cell with known / arbitrary content.  Writes require the cell atom in
    the pre — there is no ambient "any `.data`" access.

  Demo: `GlobalDataDemo.lean` (la-load a const, read it, la-load an RW
  cell, write it — genuine post, `#guard` byte-identity).  Real discharge:
  `Evm64/Terminating/ReturnHaltResolved.lean` retires RETURN's `hla*`.
-/

import EvmAsm.Rv64.SAsm.BlockSound
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

-- ============================================================================
-- §1  The PC-aware block engine
-- ============================================================================

/-- Is this instruction an `AUIPC`? (the only PC-reading block leaf) -/
def _root_.EvmAsm.Rv64.Instr.isAuipc : Instr → Bool
  | .AUIPC _ _ => true
  | _ => false

/-- One PC-aware engine step: `AUIPC` reads the instruction's address;
    everything else delegates to the PC-blind engine. -/
def execInstrRFAt (ro : Region) (rwBase : Word) (pc : Word) (rf : RegFile)
    (ws : List (BitVec 8)) : Instr → RegFile × List (BitVec 8)
  | .AUIPC rd imm =>
      (rf.set rd (pc + ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64), ws)
  | i => execInstrRF ro rwBase rf ws i

/-- Supported-and-exposed check, extended with `AUIPC` (writes an exposed
    register; reads only the PC). -/
def instrOkAt (i : Instr) : Bool :=
  match i with
  | .AUIPC rd _ => Reg.isExposed rd
  | i => instrOk i

/-- Every instruction of the block is a supported PC-aware leaf. -/
def blockOkAt (instrs : List Instr) : Bool :=
  instrs.all instrOkAt

/-- PC-threaded forward symbolic execution: instruction `k` executes at
    `pc + 4k`. -/
def execBlockAt (ro : Region) (rwBase : Word) (pc : Word) (rf : RegFile)
    (ws : List (BitVec 8)) : List Instr → RegFile × List (BitVec 8)
  | [] => (rf, ws)
  | i :: is =>
      execBlockAt ro rwBase (pc + 4) (execInstrRFAt ro rwBase pc rf ws i).1
        (execInstrRFAt ro rwBase pc rf ws i).2 is

/-- PC-threaded load/store side conditions: `AUIPC` has none; everything
    else matches `blockVCs` step for step. -/
def blockVCsAt (ro : Region) (rwBase : Word) (pc : Word) (rf : RegFile)
    (ws : List (BitVec 8)) : List Instr → Prop
  | [] => True
  | i :: is =>
      (match loadSem i with
       | some l =>
           let a := rf.get l.rs1 + signExtend12 l.ofs
           if inRw rwBase ws a l.nbytes
           then (Region.mk rwBase ws).loadOk a l.nbytes
           else ro.loadOk a l.nbytes
       | none =>
         match storeSem i with
         | some st =>
             let a := rf.get st.rs1 + signExtend12 st.ofs
             inRw rwBase ws a st.nbytes ∧ st.nbytes ∣ (a - rwBase).toNat
         | none => True)
      ∧ blockVCsAt ro rwBase (pc + 4) (execInstrRFAt ro rwBase pc rf ws i).1
          (execInstrRFAt ro rwBase pc rf ws i).2 is

-- ----------------------------------------------------------------------------
-- Conservativity: on AUIPC-free instructions/blocks the PC-aware engine
-- IS the PC-blind engine (existing blocks are unaffected; the original
-- defs are not touched at all).
-- ----------------------------------------------------------------------------

theorem execInstrRFAt_eq_execInstrRF (ro : Region) (rwBase pc : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (i : Instr)
    (h : i.isAuipc = false) :
    execInstrRFAt ro rwBase pc rf ws i = execInstrRF ro rwBase rf ws i := by
  cases i <;> first | rfl | simp [Instr.isAuipc] at h

theorem instrOkAt_eq_instrOk (i : Instr) (h : i.isAuipc = false) :
    instrOkAt i = instrOk i := by
  cases i <;> first | rfl | simp [Instr.isAuipc] at h

theorem execBlockAt_eq_execBlock (ro : Region) (rwBase : Word)
    (instrs : List Instr) (h : instrs.all (fun i => !i.isAuipc) = true) :
    ∀ (pc : Word) (rf : RegFile) (ws : List (BitVec 8)),
      execBlockAt ro rwBase pc rf ws instrs = execBlock ro rwBase rf ws instrs := by
  induction instrs with
  | nil => intro pc rf ws; rfl
  | cons i is ih =>
      intro pc rf ws
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
      show execBlockAt ro rwBase (pc + 4) _ _ is = _
      rw [execInstrRFAt_eq_execInstrRF ro rwBase pc rf ws i h.1]
      exact ih (by simp only [List.all_eq_true] at h ⊢; exact h.2) (pc + 4) _ _

theorem blockVCsAt_iff_blockVCs (ro : Region) (rwBase : Word)
    (instrs : List Instr) (h : instrs.all (fun i => !i.isAuipc) = true) :
    ∀ (pc : Word) (rf : RegFile) (ws : List (BitVec 8)),
      blockVCsAt ro rwBase pc rf ws instrs ↔ blockVCs ro rwBase rf ws instrs := by
  induction instrs with
  | nil => intro pc rf ws; rfl
  | cons i is ih =>
      intro pc rf ws
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
      show (_ ∧ blockVCsAt ro rwBase (pc + 4) _ _ is) ↔ (_ ∧ blockVCs ro rwBase _ _ is)
      rw [execInstrRFAt_eq_execInstrRF ro rwBase pc rf ws i h.1]
      exact and_congr Iff.rfl
        (ih (by simp only [List.all_eq_true] at h ⊢; exact h.2) (pc + 4) _ _)

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

/-- `AUIPC` at the register-file granularity: the machine step writes
    `pc + sext32→64(imm << 12)` into an exposed `rd`. -/
theorem regFile_auipc_spec_within (rd : Reg) (imm : BitVec 20) (rf : RegFile)
    (base : Word) (hrd : Reg.isExposed rd = true) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.AUIPC rd imm))
      (regFileIs rf)
      (regFileIs (rf.set rd
        (base + ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.AUIPC rd imm) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hstep' : step s = some (execInstrBr s (.AUIPC rd imm)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.AUIPC rd imm)
      = (s.setReg rd
          (s.pc + ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)).setPC
        (s.pc + 4) := by
    simp [execInstrBr]
  refine ⟨1, Nat.le_refl 1,
    (s.setReg rd
      (s.pc + ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)).setPC
      (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regFileIs _) hR)
      (holdsFor_sepConj_regFileIs_setReg hrd hPR)

/-- Single-instruction PC-aware spec: `AUIPC` via `regFile_auipc_spec_within`
    (regions framed), everything else via `execInstrRF_sound`. -/
theorem execInstrRFAt_sound {i : Instr} (ro : Region) (rw : RwRegion)
    (hro : ro.wf) (hrw : rw.wf)
    (hok : instrOkAt i = true)
    (rf : RegFile) (ws : List (BitVec 8)) (hws : ws.length = rw.len)
    (base : Word)
    (hvc : match loadSem i with
      | some l =>
          if inRw rw.base ws (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes
          then (Region.mk rw.base ws).loadOk
            (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes
          else ro.loadOk (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes
      | none =>
        match storeSem i with
        | some st =>
            inRw rw.base ws (rf.get st.rs1 + signExtend12 st.ofs) st.nbytes
              ∧ st.nbytes ∣ ((rf.get st.rs1 + signExtend12 st.ofs) - rw.base).toNat
        | none => True) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base i)
      ((regFileIs rf) ** (bytesRegion ro.base ro.bytes ** bytesRegion rw.base ws))
      ((regFileIs (execInstrRFAt ro rw.base base rf ws i).1) **
        (bytesRegion ro.base ro.bytes **
          bytesRegion rw.base (execInstrRFAt ro rw.base base rf ws i).2)) := by
  by_cases hau : i.isAuipc = true
  · obtain ⟨rd, imm, rfl⟩ : ∃ rd imm, i = .AUIPC rd imm := by
      cases i <;> simp [Instr.isAuipc] at hau
      exact ⟨_, _, rfl⟩
    have hrd : Reg.isExposed rd = true := by
      simpa [instrOkAt] using hok
    show cpsTripleWithin 1 base (base + 4) _ _
      ((regFileIs (rf.set rd
        (base + ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64))) **
        (bytesRegion ro.base ro.bytes ** bytesRegion rw.base ws))
    exact cpsTripleWithin_frameR
      (bytesRegion ro.base ro.bytes ** bytesRegion rw.base ws)
      (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
      (regFile_auipc_spec_within rd imm rf base hrd)
  · have hau' : i.isAuipc = false := by simpa using hau
    rw [show (execInstrRFAt ro rw.base base rf ws i)
      = execInstrRF ro rw.base rf ws i from
      execInstrRFAt_eq_execInstrRF ro rw.base base rf ws i hau']
    exact execInstrRF_sound ro rw hro hrw
      (by rw [← instrOkAt_eq_instrOk i hau']; exact hok) rf ws hws base hvc

/-- The PC-aware engine step never changes the writable window's length. -/
theorem execInstrRFAt_ws_length (ro : Region) (rwBase pc : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (i : Instr) :
    (execInstrRFAt ro rwBase pc rf ws i).2.length = ws.length := by
  by_cases hau : i.isAuipc = true
  · obtain ⟨rd, imm, rfl⟩ : ∃ rd imm, i = .AUIPC rd imm := by
      cases i <;> simp [Instr.isAuipc] at hau
      exact ⟨_, _, rfl⟩
    rfl
  · rw [execInstrRFAt_eq_execInstrRF ro rwBase pc rf ws i (by simpa using hau)]
    exact execInstrRF_ws_length ro rwBase rf ws i

/-- **PC-aware block soundness** — the `execBlock_sound` analogue: a
    supported straight-line block (now possibly containing `AUIPC`, i.e.
    `la` pairs) satisfies a bounded CPS triple under its own
    `CodeReq.ofProg`, with the engine threading each instruction's real
    address. -/
theorem execBlockAt_sound (ro : Region) (rw : RwRegion) (instrs : List Instr)
    (rf : RegFile) (ws : List (BitVec 8)) (base : Word)
    (hro : ro.wf) (hrw : rw.wf) (hws : ws.length = rw.len)
    (hok : blockOkAt instrs = true)
    (hvcs : blockVCsAt ro rw.base base rf ws instrs)
    (hlen : 4 * instrs.length < 2 ^ 64) :
    cpsTripleWithin instrs.length base (base + BitVec.ofNat 64 (4 * instrs.length))
      (CodeReq.ofProg base instrs)
      ((regFileIs rf) ** (bytesRegion ro.base ro.bytes ** bytesRegion rw.base ws))
      ((regFileIs (execBlockAt ro rw.base base rf ws instrs).1) **
        (bytesRegion ro.base ro.bytes **
          bytesRegion rw.base (execBlockAt ro rw.base base rf ws instrs).2)) := by
  induction instrs generalizing rf ws base with
  | nil =>
      intro R hR s hcr hPR hpc
      refine ⟨0, Nat.le_refl 0, s, rfl, ?_, hPR⟩
      simpa using hpc
  | cons i rest ih =>
      simp only [blockOkAt, List.all_cons, Bool.and_eq_true] at hok
      obtain ⟨hoki, hokr⟩ := hok
      obtain ⟨hvc1, hvcr⟩ := hvcs
      have hlenr : 4 * rest.length < 2 ^ 64 := by
        simp only [List.length_cons] at hlen; omega
      have h1 := execInstrRFAt_sound ro rw hro hrw hoki rf ws hws base hvc1
      have h2 := ih (execInstrRFAt ro rw.base base rf ws i).1
        (execInstrRFAt ro rw.base base rf ws i).2 (base + 4)
        (by rw [execInstrRFAt_ws_length]; exact hws)
        hokr hvcr hlenr
      have hd : (CodeReq.singleton base i).Disjoint
          (CodeReq.ofProg (base + 4) rest) := by
        intro a
        by_cases ha : a = base
        · subst ha
          refine Or.inr (CodeReq.ofProg_none_range _ _ (fun k hk heq => ?_))
          have hk4 : 4 + 4 * k < 2 ^ 64 := by omega
          bv_omega
        · left
          simp [CodeReq.singleton, ha]
      have h3 := cpsTripleWithin_seq hd h1 h2
      rw [CodeReq.ofProg_cons]
      have hexit : (base + 4) + BitVec.ofNat 64 (4 * rest.length)
          = base + BitVec.ofNat 64 (4 * (rest.length + 1)) := by
        bv_omega
      rw [hexit] at h3
      simpa [List.length_cons, Nat.add_comm] using h3

-- ============================================================================
-- §2  Global-data region assertions
-- ============================================================================

/-- A read-only constant global (e.g. `secp256k1_p_be`): known bytes at a
    fixed link address.  Read-only by DISCIPLINE OF THE SPEC: carry the
    same `globalConst` atom in pre and post (frame it with
    `cpsTripleWithin_frameR`), so the constant provably survives.  Reads go
    through the usual `Region`/`bytesRegion` load primitives
    (`Region.loadOk_slot`/`dwordAt_slot`, `lbu`/`ld` atom specs). -/
def globalConst (addr : Word) (bs : List (BitVec 8)) : Assertion :=
  bytesRegion addr bs

/-- An RW scratch dword cell (e.g. `rfu_offset`) with KNOWN content. -/
def globalCellIs (addr v : Word) : Assertion := addr ↦ₘ v

/-- An RW scratch dword cell with arbitrary (owned) content.  A write
    requires this atom (or `globalCellIs`) in the pre — there is no
    ambient "any `.data` address" access. -/
def globalCellOwn (addr : Word) : Assertion := memOwn addr

theorem pcFree_globalConst (addr : Word) (bs : List (BitVec 8)) :
    (globalConst addr bs).pcFree := bytesRegion_pcFree _ _

theorem pcFree_globalCellIs (addr v : Word) : (globalCellIs addr v).pcFree :=
  pcFree_memIs

theorem pcFree_globalCellOwn (addr : Word) : (globalCellOwn addr).pcFree :=
  pcFree_memOwn

/-- Release a known cell to ownership (post-side weakening at a merge). -/
theorem globalCellIs_to_own (addr v : Word) :
    ∀ h, globalCellIs addr v h → globalCellOwn addr h :=
  fun _ hh => memIs_implies_memOwn _ hh

#print axioms execBlockAt_sound
#print axioms regFile_auipc_spec_within

end EvmAsm.Rv64.SAsm
