/-
  EvmAsm.Rv64.InstructionSpecs

  Separation logic specifications for each RISC-V (RV64) instruction using
  bounded CPS specs.

  Code is accessed via CodeReq.singleton side-condition (not instrAt in P/Q).

  Proofs delegate to the generic lemmas in GenericSpecs.lean.

  Ported from EvmAsm.InstructionSpecs (RV32) with the following changes:
  - LUI/AUIPC: postcondition uses signExtend 64 of the 32-bit shifted value
  - LW/SW specs removed (RV64 LW uses getWord32, not getMem)
  - LD/SD specs added using generic_ld_spec/generic_sd_spec
-/

-- `GenericSpecs` transitively imports `Basic`, `Instructions`, `SepLogic`,
-- `Execution`, and `CPSSpec`.
import EvmAsm.Rv64.GenericSpecs

namespace EvmAsm.Rv64

-- ============================================================================
-- ALU Instructions (Register-Register): All Distinct Case
-- ============================================================================

/-- ADD rd, rs1, rs2: rd := rs1 + rs2 (all registers distinct) -/
theorem add_spec_within (rd rs1 rs2 : Reg) (v1 v2 vOld : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADD rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 + v2))) :=
  generic_3reg_spec_within (.ADD rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ base hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem add_spec_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADD rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.ADD rd rd rs2) rd rs2 v1 v2 _ base hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem add_spec_rd_eq_rs2_within (rd rs1 : Reg) (v1 v2 : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADD rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + v2))) :=
  generic_2reg_spec_within (.ADD rd rs1 rd) rs1 rd v1 v2 (v1 + v2) base hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem add_spec_all_same_within (rd : Reg) (v : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADD rd rd rd))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v + v)) :=
  generic_1reg_spec_within (.ADD rd rd rd) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem sub_spec_within (rd rs1 rs2 : Reg) (v1 v2 vOld : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SUB rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 - v2))) :=
  generic_3reg_spec_within (.SUB rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ base hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem sub_spec_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SUB rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.SUB rd rd rs2) rd rs2 v1 v2 _ base hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem sub_spec_all_same_within (rd : Reg) (v : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SUB rd rd rd))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v - v)) :=
  generic_1reg_spec_within (.SUB rd rd rd) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem addi_spec_within (rd rs1 : Reg) (v1 vOld : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADDI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) :=
  generic_2reg_spec_within (.ADDI rd rs1 imm) rs1 rd v1 vOld (v1 + signExtend12 imm) base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem addi_spec_same_within (rd : Reg) (v : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADDI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v + signExtend12 imm)) :=
  generic_1reg_spec_within (.ADDI rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem ori_spec_within (rd rs1 : Reg) (v1 vOld : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ORI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 ||| signExtend12 imm))) :=
  generic_2reg_spec_within (.ORI rd rs1 imm) rs1 rd v1 vOld (v1 ||| signExtend12 imm) base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem ori_spec_same_within (rd : Reg) (v : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ORI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v ||| signExtend12 imm)) :=
  generic_1reg_spec_within (.ORI rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem slti_spec_within (rd rs1 : Reg) (v1 vOld : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SLTI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.slt v1 (signExtend12 imm) then 1 else 0))) :=
  generic_2reg_spec_within (.SLTI rd rs1 imm) rs1 rd v1 vOld _ base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem slti_spec_same_within (rd : Reg) (v : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SLTI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (if BitVec.slt v (signExtend12 imm) then 1 else 0)) :=
  generic_1reg_spec_within (.SLTI rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem addiw_spec_within (rd rs1 : Reg) (v1 vOld : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADDIW rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ ((v1.truncate 32 + (signExtend12 imm).truncate 32 : BitVec 32).signExtend 64))) :=
  generic_2reg_spec_within (.ADDIW rd rs1 imm) rs1 rd v1 vOld _ base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem addiw_spec_same_within (rd : Reg) (v : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADDIW rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ ((v.truncate 32 + (signExtend12 imm).truncate 32 : BitVec 32).signExtend 64)) :=
  generic_1reg_spec_within (.ADDIW rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem lui_spec_within (rd : Reg) (vOld : Word) (imm : BitVec 20) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LUI rd imm))
      (rd ↦ᵣ vOld)
      (rd ↦ᵣ ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) :=
  generic_1reg_spec_within (.LUI rd imm) rd vOld _ base hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem auipc_spec_within (rd : Reg) (vOld : Word) (imm : BitVec 20) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.AUIPC rd imm))
      (rd ↦ᵣ vOld)
      (rd ↦ᵣ (base + ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) :=
  generic_1reg_spec_within (.AUIPC rd imm) rd vOld _ base hrd_ne_x0
    (by intro s hpc _; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem ld_spec_within (rd rs1 : Reg) (v_addr vOld memVal : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LD rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** ((v_addr + signExtend12 offset) ↦ₘ memVal))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ memVal) ** ((v_addr + signExtend12 offset) ↦ₘ memVal)) :=
  generic_ld_spec_within rd rs1 v_addr vOld memVal offset base hrd_ne_x0
theorem ld_spec_same_within (rd : Reg) (v_addr memVal : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LD rd rd offset))
      ((rd ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ memVal))
      ((rd ↦ᵣ memVal) ** ((v_addr + signExtend12 offset) ↦ₘ memVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LD rd rd offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrd : s.getReg rd = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hmem_piece := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)
  have hmem : s.getMem (v_addr + signExtend12 offset) = memVal :=
    holdsFor_memIs_getMem hmem_piece
  have hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true :=
    holdsFor_memIs_isValidDwordAccess hmem_piece
  have hstep' : step s = some (execInstrBr s (.LD rd rd offset)) :=
    step_ld hfetch (hrd ▸ hvalid)
  have hexec' : execInstrBr s (.LD rd rd offset) = (s.setReg rd memVal).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrd, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd memVal).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pre: (rd ** mem) ** R → assoc → rd ** (mem ** R)
    have h1 := holdsFor_sepConj_assoc.mp hPR
    -- Update rd: rd ** (mem ** R) → rd' ** (mem ** R)
    have h2 := holdsFor_sepConj_regIs_setReg (v' := memVal) hrd_ne_x0 h1
    -- Reassociate: rd' ** (mem ** R) → (rd' ** mem) ** R
    have h3 := holdsFor_sepConj_assoc.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h3
theorem sd_spec_within (rs1 rs2 : Reg) (v_addr v_data memOld : Word) (offset : BitVec 12) (base : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ memOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) :=
  generic_sd_spec_within rs1 rs2 v_addr v_data memOld offset base
theorem sd_spec_same_within (rs : Reg) (v : Word) (memOld : Word) (offset : BitVec 12) (base : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SD rs rs offset))
      ((rs ↦ᵣ v) ** ((v + signExtend12 offset) ↦ₘ memOld))
      ((rs ↦ᵣ v) ** ((v + signExtend12 offset) ↦ₘ v)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SD rs rs offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs : s.getReg rs = v :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hvalid : isValidDwordAccess (v + signExtend12 offset) = true :=
    holdsFor_memIs_isValidDwordAccess (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.SD rs rs offset)) :=
    step_sd hfetch (hrs ▸ hvalid)
  have hexec' : execInstrBr s (.SD rs rs offset) =
      (s.setMem (v + signExtend12 offset) v).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs]
  refine ⟨1, Nat.le_refl 1, (s.setMem (v + signExtend12 offset) v).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_memIs_setMem (v' := v) h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h3
theorem beq_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) :=
  generic_beq_spec_within rs1 rs2 offset v1 v2 base
theorem beq_spec_same_within (rs : Reg) (offset : BitVec 13) (v : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BEQ rs rs offset))
      (rs ↦ᵣ v)
      (base + signExtend13 offset) (rs ↦ᵣ v)
      (base + 4) (rs ↦ᵣ v) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs rs offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs : s.getReg rs = v :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.BEQ rs rs offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs rs offset) = s.setPC (s.pc + signExtend13 offset) := by
    simp only [execInstrBr, hrs, beq_self_eq_true, ite_true]
  refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) hPR
theorem bne_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BNE rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) :=
  generic_bne_spec_within rs1 rs2 offset v1 v2 base
theorem bne_spec_same_within (rs : Reg) (offset : BitVec 13) (v : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BNE rs rs offset))
      (rs ↦ᵣ v)
      (base + signExtend13 offset) (rs ↦ᵣ v)
      (base + 4) (rs ↦ᵣ v) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BNE rs rs offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs : s.getReg rs = v :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.BNE rs rs offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BNE rs rs offset) = s.setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
  refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) hPR
theorem bgeu_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BGEU rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.ult v1 v2⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.ult v1 v2⌝) :=
  generic_bgeu_spec_within rs1 rs2 offset v1 v2 base
theorem jal_spec_within (rd : Reg) (vOld : Word) (offset : BitVec 21) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + signExtend21 offset) (CodeReq.singleton base (.JAL rd offset))
      (rd ↦ᵣ vOld)
      (rd ↦ᵣ (base + 4)) :=
  generic_jal_spec_within rd vOld offset base hrd_ne_x0
theorem jalr_spec_within (rd rs1 : Reg) (v1 vOld : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base ((v1 + signExtend12 offset) &&& (~~~1)) (CodeReq.singleton base (.JALR rd rs1 offset))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))) :=
  generic_jalr_spec_within rd rs1 v1 vOld offset base hrd_ne_x0
theorem jalr_spec_same_within (rd : Reg) (v : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base ((v + signExtend12 offset) &&& (~~~1)) (CodeReq.singleton base (.JALR rd rd offset))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (base + 4)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JALR rd rd offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrd : s.getReg rd = v :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.JALR rd rd offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.JALR rd rd offset) =
      (s.setReg rd (s.pc + 4)).setPC ((v + signExtend12 offset) &&& ~~~1) := by
    simp only [execInstrBr, hrd]; rfl
  refine ⟨1, Nat.le_refl 1, (s.setReg rd (s.pc + 4)).setPC ((v + signExtend12 offset) &&& ~~~1), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h1
theorem mv_spec_within (rd rs : Reg) (v vOld : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.MV rd rs))
      ((rs ↦ᵣ v) ** (rd ↦ᵣ vOld))
      ((rs ↦ᵣ v) ** (rd ↦ᵣ v)) :=
  generic_2reg_spec_within (.MV rd rs) rs rd v vOld v base hrd_ne_x0
    (by intro s _ hrs _; simp [execInstrBr, hrs])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem li_spec_within (rd : Reg) (vOld imm : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LI rd imm))
      (rd ↦ᵣ vOld)
      (rd ↦ᵣ imm) :=
  generic_1reg_spec_within (.LI rd imm) rd vOld _ base hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem nop_spec_within (base : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base .NOP)
      empAssertion
      empAssertion :=
  generic_nop_spec_within .NOP
    (by intro s hpc; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
theorem fence_spec_within (base : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base .FENCE)
      empAssertion
      empAssertion :=
  generic_nop_spec_within .FENCE
    (by intro s hpc; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
end EvmAsm.Rv64
