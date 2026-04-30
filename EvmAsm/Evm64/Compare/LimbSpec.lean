/-
  EvmAsm.Evm64.Compare.LimbSpec

  Shared per-limb comparison specs used by Lt, Gt, Slt, Sgt.
  - lt_limb0_spec, lt_limb_carry_spec: borrow propagation
  - beq_eq_spec, beq_ne_spec: BEQ branch helpers (for SLT/SGT)
  - slt_msb_load_spec: MSB limb load (for SLT/SGT)
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Per-limb Specs: LT (borrow propagation without storing results)
-- ============================================================================

/-- LT limb 0 spec (3 instructions): LD, LD, SLTU.
    Computes initial borrow = (a < b ? 1 : 0). Does NOT modify memory. -/
theorem lt_limb0_spec_within (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 v5 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let borrow := if BitVec.ult aLimb bLimb then (1 : Word) else 0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
       (CodeReq.singleton (base + 8) (.SLTU .x5 .x7 .x6)))
    cpsTripleWithin 3 base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ aLimb) ** (.x6 ↦ᵣ bLimb) ** (.x5 ↦ᵣ borrow) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb)) := by
  intro memA memB borrow
  have L0 := ld_spec_gen_within .x7 .x12 sp v7 aLimb offA base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x12 sp v6 bLimb offB (base + 4) (by nofun)
  have S := sltu_spec_gen_within .x5 .x7 .x6 v5 aLimb bLimb (base + 8) (by nofun)
  runBlock L0 L1 S


/-- LT carry limb spec (6 instructions): LD, LD, SLTU, SUB, SLTU, OR.
    Propagates borrow without storing result. Memory is NOT modified. -/
theorem lt_limb_carry_spec_within (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 borrowIn v11 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let borrow1 := if BitVec.ult aLimb bLimb then (1 : Word) else 0
    let temp := aLimb - bLimb
    let borrow2 := if BitVec.ult temp borrowIn then (1 : Word) else 0
    let borrowOut := borrow1 ||| borrow2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x11 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x6 .x7 .x5))
       (CodeReq.singleton (base + 20) (.OR .x5 .x11 .x6))))))
    cpsTripleWithin 6 base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ v11) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrowOut) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb)) := by
  intro memA memB borrow1 temp borrow2 borrowOut
  have L0 := ld_spec_gen_within .x7 .x12 sp v7 aLimb offA base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x12 sp v6 bLimb offB (base + 4) (by nofun)
  have S0 := sltu_spec_gen_within .x11 .x7 .x6 v11 aLimb bLimb (base + 8) (by nofun)
  have Sub := sub_spec_gen_rd_eq_rs1_within .x7 .x6 aLimb bLimb (base + 12) (by nofun)
  have S1 := sltu_spec_gen_within .x6 .x7 .x5 bLimb temp borrowIn (base + 16) (by nofun)
  have O := or_spec_gen_within .x5 .x11 .x6 borrowIn borrow1 borrow2 (base + 20) (by nofun)
  runBlock L0 L1 S0 Sub S1 O


-- ============================================================================
-- BEQ helper specs (single-path, for SLT/SGT composition)
-- ============================================================================

/-- BEQ when values are equal: always taken (jump to PC + signExtend13 offset).
    BEQ only modifies PC; all pcFree assertions are preserved. -/
theorem beq_eq_spec_within (rs1 rs2 : Reg) (offset : BitVec 13)
    (v : Word) (base : Word) :
    cpsTripleWithin 1 base (base + signExtend13 offset)
      (CodeReq.singleton base (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v))
      ((rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 rs2 offset) :=
    hcr s.pc (.BEQ rs1 rs2 offset) (CodeReq.singleton_get s.pc (.BEQ rs1 rs2 offset))
  have hrs1 : s.getReg rs1 = v :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 rs2 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
    simp [execInstrBr, hrs1, hrs2]
  refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj pcFree_regIs pcFree_regIs) hR) hPR


/-- BEQ when values are not equal: never taken (fall through to PC + 4).
    BEQ only modifies PC; all pcFree assertions are preserved. -/
theorem beq_ne_spec_within (rs1 rs2 : Reg) (offset : BitVec 13)
    (v1 v2 : Word) (hne : v1 ≠ v2) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 rs2 offset) :=
    hcr s.pc (.BEQ rs1 rs2 offset) (CodeReq.singleton_get s.pc (.BEQ rs1 rs2 offset))
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 rs2 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + 4) := by
    simp [execInstrBr, hrs1, hrs2, hne]
  refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj pcFree_regIs pcFree_regIs) hR) hPR


-- ============================================================================
-- Per-limb Specs: SLT (MSB load + signed comparison)
-- ============================================================================

/-- SLT MSB load spec (2 instructions): LD x7, LD x6.
    Loads the MSB limbs (limb 3) of both operands into x7 and x6. -/
theorem slt_msb_load_spec_within (offA offB : BitVec 12)
    (sp a3 b3 v7 v6 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
       (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
    cpsTripleWithin 2 base (base + 8) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (memA ↦ₘ a3) ** (memB ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
       (memA ↦ₘ a3) ** (memB ↦ₘ b3)) := by
  intro memA memB
  have L0 := ld_spec_gen_within .x7 .x12 sp v7 a3 offA base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x12 sp v6 b3 offB (base + 4) (by nofun)
  runBlock L0 L1


end EvmAsm.Evm64
