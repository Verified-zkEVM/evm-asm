/-
  EvmAsm.Rv64.SailEquiv.StepProofs

  PC-aware step equivalence: the capstone that finally makes the **program
  counter** part of the Rv64 ↔ SAIL comparison for control-flow instructions.

  The per-instruction `*_sail_equiv` theorems relate the SAIL `execute_*`
  computation to `execInstrBr`, but `execute_*` only writes SAIL's `nextPC`
  (it does not commit `PC`).  Our `execInstrBr` writes the committed next-PC
  straight into `pc`.  The two are reconciled by composing `execute_* ; tick_pc`
  — `tick_pc` performs the SAIL `PC := nextPC` commit — after which the committed
  SAIL `PC` equals the Rv64 `pc`, i.e. the post state satisfies the PC-aware
  relation `StateRelPC`.

  `step_of_execute` is the generic glue: any instruction whose `execute_*`
  theorem exposes `nextPC = (post Rv64 state).pc` yields, after `; tick_pc`, a
  `StateRelPC`-related post state.  The branch/jump capstones below instantiate
  it, so BEQ/BNE/BLT/BGE/BLTU/BGEU/JAL/JALR now have their **target PC** verified
  against the SAIL golden model — previously the branch proofs were vacuous on PC.
-/

import EvmAsm.Rv64.SailEquiv.BranchProofs

open Out.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

/-- Generic `execute ; tick_pc` glue.  If a SAIL computation `m` reduces to a
    state `sSail'` that agrees with the post Rv64 state `sRv'` on registers and
    memory (`StateRel`) and whose `nextPC` is the post Rv64 `pc`, then running
    `m >>= tick_pc` commits that `nextPC` into `PC`, landing in a state that is
    `StateRelPC`-related to `sRv'` (registers, memory, and the committed PC all
    agree). -/
theorem step_of_execute {α : Type} {sRv' : MachineState} {sSail sSail' : SailState}
    {m : SailM α} {a : α}
    (h_exec : runSail m sSail = some (a, sSail'))
    (h_rel : StateRel sRv' sSail')
    (h_nextpc : sSail'.regs.get? Register.nextPC = some sRv'.pc) :
    ∃ sSail'',
      runSail (m >>= fun _ => tick_pc ()) sSail = some ((), sSail'') ∧
      StateRelPC sRv' sSail'' := by
  have h1 : runSail (m >>= fun _ => tick_pc ()) sSail
      = some ((), { sSail' with regs := sSail'.regs.insert Register.PC sRv'.pc }) := by
    rw [runSail_bind, h_exec]; exact runSail_tick_pc h_nextpc
  exact ⟨_, h1, { toStateRel := stateRel_PC_insert h_rel _,
                  pc_agree := by simp [Std.ExtDHashMap.get?_insert_self] }⟩

-- ============================================================================
-- Conditional-branch step capstones (execute_BTYPE ; tick_pc)
-- ============================================================================

theorem beq_step_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrelpc : StateRelPC sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail'',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BEQ
        >>= fun _ => tick_pc ()) sSail = some ((), sSail'') ∧
      StateRelPC (execInstrBr sRv (.BEQ rs1 rs2 offset)) sSail'' := by
  obtain ⟨sSail', h_exec, h_rel, h_np⟩ :=
    beq_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc h_misa rs1 rs2 offset h_align
  exact step_of_execute h_exec h_rel h_np

theorem bne_step_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrelpc : StateRelPC sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail'',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BNE
        >>= fun _ => tick_pc ()) sSail = some ((), sSail'') ∧
      StateRelPC (execInstrBr sRv (.BNE rs1 rs2 offset)) sSail'' := by
  obtain ⟨sSail', h_exec, h_rel, h_np⟩ :=
    bne_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc h_misa rs1 rs2 offset h_align
  exact step_of_execute h_exec h_rel h_np

theorem blt_step_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrelpc : StateRelPC sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail'',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLT
        >>= fun _ => tick_pc ()) sSail = some ((), sSail'') ∧
      StateRelPC (execInstrBr sRv (.BLT rs1 rs2 offset)) sSail'' := by
  obtain ⟨sSail', h_exec, h_rel, h_np⟩ :=
    blt_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc h_misa rs1 rs2 offset h_align
  exact step_of_execute h_exec h_rel h_np

theorem bge_step_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrelpc : StateRelPC sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail'',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGE
        >>= fun _ => tick_pc ()) sSail = some ((), sSail'') ∧
      StateRelPC (execInstrBr sRv (.BGE rs1 rs2 offset)) sSail'' := by
  obtain ⟨sSail', h_exec, h_rel, h_np⟩ :=
    bge_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc h_misa rs1 rs2 offset h_align
  exact step_of_execute h_exec h_rel h_np

theorem bltu_step_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrelpc : StateRelPC sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail'',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLTU
        >>= fun _ => tick_pc ()) sSail = some ((), sSail'') ∧
      StateRelPC (execInstrBr sRv (.BLTU rs1 rs2 offset)) sSail'' := by
  obtain ⟨sSail', h_exec, h_rel, h_np⟩ :=
    bltu_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc h_misa rs1 rs2 offset h_align
  exact step_of_execute h_exec h_rel h_np

theorem bgeu_step_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrelpc : StateRelPC sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail'',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGEU
        >>= fun _ => tick_pc ()) sSail = some ((), sSail'') ∧
      StateRelPC (execInstrBr sRv (.BGEU rs1 rs2 offset)) sSail'' := by
  obtain ⟨sSail', h_exec, h_rel, h_np⟩ :=
    bgeu_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc h_misa rs1 rs2 offset h_align
  exact step_of_execute h_exec h_rel h_np

-- ============================================================================
-- Unconditional-jump step capstones (execute_JAL/JALR ; tick_pc)
-- ============================================================================

theorem jal_step_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrelpc : StateRelPC sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rd : Reg) (offset : BitVec 21)
    (h_align : (sRv.pc + signExtend21 offset) &&& 3 = 0) :
    ∃ sSail'',
      runSail (execute_JAL offset (regToRegidx rd) >>= fun _ => tick_pc ()) sSail
        = some ((), sSail'') ∧
      StateRelPC (execInstrBr sRv (.JAL rd offset)) sSail'' := by
  obtain ⟨sSail', h_exec, h_rel, h_np⟩ :=
    jal_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc h_misa rd offset h_align
  exact step_of_execute h_exec h_rel h_np

theorem jalr_step_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (h_elp : ∃ s_mid, update_elp_state (regToRegidx rs1) sSail = .ok () s_mid ∧
      StateRel sRv s_mid ∧
      s_mid.regs.get? Register.PC = some sRv.pc ∧
      s_mid.regs.get? Register.nextPC = some (sRv.pc + 4) ∧
      (∃ v, s_mid.regs.get? Register.misa = some v))
    (h_align : ((sRv.getReg rs1 + signExtend12 offset) &&& ~~~1#64) &&& 3 = 0) :
    ∃ sSail'',
      runSail (execute_JALR offset (regToRegidx rs1) (regToRegidx rd) >>= fun _ => tick_pc ()) sSail
        = some ((), sSail'') ∧
      StateRelPC (execInstrBr sRv (.JALR rd rs1 offset)) sSail'' := by
  obtain ⟨sSail', h_exec, h_rel, h_np⟩ :=
    jalr_sail_equiv sRv sSail rd rs1 offset h_elp h_align
  exact step_of_execute h_exec h_rel h_np

end EvmAsm.Rv64.SailEquiv
