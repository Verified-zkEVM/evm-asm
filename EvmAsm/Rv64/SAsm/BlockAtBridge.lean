/-
  EvmAsm.Rv64.SAsm.BlockAtBridge

  **The structured-layer bridge for `AUIPC` blocks** (bead evm-asm-4ch8f.56.7.1;
  completes #10059 into the layer ports actually go through).

  #10059 added `AUIPC` to the PARALLEL PC-threaded engine
  (`execInstrRFAt`/`execBlockAt`/`blockVCsAt` + `execBlockAt_sound`), leaving
  the original PC-agnostic `execBlock`/`blockOk`/`Stmt.sound` untouched (it
  CANNOT step a PC-relative instruction, which is why `blockOk` rejects
  `AUIPC`).  This module bridges the two worlds so a leaf/block containing
  `AUIPC` — the `la`/global-materialization idiom — is proven via the
  At-engine and composes UNCHANGED with the existing frame / loop / call /
  join machinery at `cpsTripleWithin` level:

  * `blockAt_flat_spec` — `execBlockAt_sound` restated at the EXPOSED-ATOM
    granularity (`regAtoms rf exposedRegs` = the fifteen `↦ᵣ` atoms, via
    `regFileIs_eq_regAtoms`), the same currency the `abiFrame_spec` /
    `frame_call` / `countup_loop` / `RetForwardJoin` consumers trade in — a
    bridged block is interchangeable with a `blockOk`-proven one;

  * `blockAt_regs_spec` — the memory-free special case (pure address
    arithmetic, the `la` shape): regions instantiated empty and cleaned
    away, VCs discharged by `blockVCsAt_of_not_hasLoad`;

  * conservativity is inherited from #10059 (`execBlockAt_eq_execBlock` /
    `blockVCsAt_iff_blockVCs` on AUIPC-free blocks) — the original engine
    is not touched here at all.

  The `AUIPC`-materialized address itself is PROVEN by `la_resolve`
  (`Rv64/LaResolve.lean`), not assumed; the const/RW `.data` the address
  points at is modeled by #10059's `globalConst`/`globalCellIs`/
  `globalCellOwn`.  Acceptance consumer: `frame_base`
  (`Codegen/Programs/CallFrameBaseSAsm.lean`).
-/

import EvmAsm.Rv64.SAsm.GlobalData
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-- Blocks without memory accesses have no PC-threaded memory side
    conditions (the `blockVCs_of_not_hasLoad` analogue). -/
theorem blockVCsAt_of_not_hasLoad (ro : Region) (rwBase pc : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (instrs : List Instr)
    (h : hasLoad instrs = false) :
    blockVCsAt ro rwBase pc rf ws instrs := by
  induction instrs generalizing pc rf ws with
  | nil => trivial
  | cons i is ih =>
      simp only [hasLoad, List.any_cons, Bool.or_eq_false_iff] at h
      refine ⟨?_, ih (h := by simp [hasLoad, h.2]) _ _ _⟩
      cases hl : loadSem i with
      | none =>
          cases hst : storeSem i with
          | none => trivial
          | some st => simp [hl, hst] at h
      | some l => simp [hl] at h

/-- The PC-threaded engine never changes the window length. -/
theorem execBlockAt_ws_length (ro : Region) (rwBase : Word)
    (instrs : List Instr) :
    ∀ (pc : Word) (rf : RegFile) (ws : List (BitVec 8)),
      (execBlockAt ro rwBase pc rf ws instrs).2.length = ws.length := by
  induction instrs with
  | nil => intro pc rf ws; rfl
  | cons i is ih =>
      intro pc rf ws
      show (execBlockAt ro rwBase (pc + 4) _ _ is).2.length = _
      rw [ih, execInstrRFAt_ws_length]

/-- **The bridge, general form**: `execBlockAt_sound` at the exposed-ATOM
    granularity.  `regAtoms rf exposedRegs` is definitionally the fifteen
    `↦ᵣ` atoms (`regAtoms_eq_regAtomsOf` + `regAtomsOf_cons`), so this
    triple plugs into the same `cpsTripleWithin` compositions
    (`abiFrame_spec`, `frame_call`, the loop lemmas, `RetForwardJoin`) as a
    `blockOk`-proven block — with `AUIPC` allowed. -/
theorem blockAt_flat_spec (ro : Region) (rw : RwRegion) (instrs : List Instr)
    (rf : RegFile) (ws : List (BitVec 8)) (base : Word)
    (hro : ro.wf) (hrw : rw.wf) (hws : ws.length = rw.len)
    (hok : blockOkAt instrs = true)
    (hvcs : blockVCsAt ro rw.base base rf ws instrs)
    (hlen : 4 * instrs.length < 2 ^ 64) :
    cpsTripleWithin instrs.length base (base + BitVec.ofNat 64 (4 * instrs.length))
      (CodeReq.ofProg base instrs)
      ((regAtoms rf exposedRegs) **
        (bytesRegion ro.base ro.bytes ** bytesRegion rw.base ws))
      ((regAtoms (execBlockAt ro rw.base base rf ws instrs).1 exposedRegs) **
        (bytesRegion ro.base ro.bytes **
          bytesRegion rw.base (execBlockAt ro rw.base base rf ws instrs).2)) := by
  rw [← regFileIs_eq_regAtoms, ← regFileIs_eq_regAtoms]
  exact execBlockAt_sound ro rw instrs rf ws base hro hrw hws hok hvcs hlen

/-- **The bridge, memory-free form** (the `la`/address-arithmetic shape,
    e.g. `frame_base`'s `[ADDI, LUI, MUL, AUIPC, ADDI, ADD]`): no regions
    to thread, no memory VCs — just the exposed register file moving to its
    PC-threaded symbolic image. -/
theorem blockAt_regs_spec (instrs : List Instr) (rf : RegFile) (base : Word)
    (hok : blockOkAt instrs = true)
    (hnl : hasLoad instrs = false)
    (hlen : 4 * instrs.length < 2 ^ 64) :
    cpsTripleWithin instrs.length base (base + BitVec.ofNat 64 (4 * instrs.length))
      (CodeReq.ofProg base instrs)
      (regAtoms rf exposedRegs)
      (regAtoms (execBlockAt Region.empty RwRegion.empty.base base rf [] instrs).1
        exposedRegs) := by
  have h := blockAt_flat_spec Region.empty RwRegion.empty instrs rf [] base
    Region.empty_wf RwRegion.empty_wf rfl hok
    (blockVCsAt_of_not_hasLoad Region.empty RwRegion.empty.base base rf [] instrs hnl)
    hlen
  have hws2 : (execBlockAt Region.empty RwRegion.empty.base base rf [] instrs).2
      = [] := by
    have := execBlockAt_ws_length Region.empty RwRegion.empty.base instrs base rf []
    exact List.eq_nil_of_length_eq_zero (by simpa using this)
  rw [hws2] at h
  refine cpsTripleWithin_weaken (fun h' hp => ?_) (fun h' hq => ?_) h
  · rw [show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil, bytesRegion_nil, sepConj_emp_right', sepConj_emp_right']
    exact hp
  · rw [show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil, bytesRegion_nil, sepConj_emp_right', sepConj_emp_right'] at hq
    exact hq

#print axioms blockAt_flat_spec
#print axioms blockAt_regs_spec

end EvmAsm.Rv64.SAsm
