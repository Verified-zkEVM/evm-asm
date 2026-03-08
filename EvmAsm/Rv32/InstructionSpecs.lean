/-
  EvmAsm.Rv32.InstructionSpecs

  Separation logic specifications for each RISC-V instruction using cpsTriple
  (or cpsBranch for conditional branches).

  Each spec now includes `instrAt` in both pre and postconditions, which is
  required after the CodeMem unification (commit c7f0159).

  Proofs delegate to the generic lemmas in GenericSpecs.lean.
-/

import EvmAsm.Rv32.Basic
import EvmAsm.Rv32.Instructions
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.GenericSpecs

namespace EvmAsm

-- ============================================================================
-- ALU Instructions (Register-Register): All Distinct Case
-- ============================================================================

/-- ADD rd, rs1, rs2: rd := rs1 + rs2 (all registers distinct) -/
theorem add_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADD rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .ADD rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 + v2))) :=
  generic_3reg_spec (.ADD rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ base hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADD rd, rd, rs2: rd := rd + rs2 (rd = rs1, rs2 distinct) -/
theorem add_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADD rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((base ↦ᵢ .ADD rd rd rs2) ** (rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.ADD rd rd rs2) rd rs2 v1 v2 _ base hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADD rd, rs1, rd: rd := rs1 + rd (rd = rs2, rs1 distinct) -/
theorem add_spec_rd_eq_rs2 (rd rs1 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hne : rs1 ≠ rd) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADD rd rs1 rd) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((base ↦ᵢ .ADD rd rs1 rd) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + v2))) :=
  generic_2reg_spec (.ADD rd rs1 rd) rs1 rd v1 v2 (v1 + v2) base hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADD rd, rd, rd: rd := rd + rd = 2 * rd (all same) -/
theorem add_spec_all_same (rd : Reg) (v : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADD rd rd rd) ** (rd ↦ᵣ v))
      ((base ↦ᵢ .ADD rd rd rd) ** (rd ↦ᵣ (v + v))) :=
  generic_1reg_spec (.ADD rd rd rd) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB rd, rs1, rs2: rd := rs1 - rs2 (all registers distinct) -/
theorem sub_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .SUB rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .SUB rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 - v2))) :=
  generic_3reg_spec (.SUB rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ base hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB rd, rd, rs2: rd := rd - rs2 -/
theorem sub_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .SUB rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((base ↦ᵢ .SUB rd rd rs2) ** (rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SUB rd rd rs2) rd rs2 v1 v2 _ base hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB rd, rd, rd: rd := rd - rd = 0 -/
theorem sub_spec_all_same (rd : Reg) (v : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .SUB rd rd rd) ** (rd ↦ᵣ v))
      ((base ↦ᵢ .SUB rd rd rd) ** (rd ↦ᵣ (v - v))) :=
  generic_1reg_spec (.SUB rd rd rd) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- ALU Instructions (Immediate)
-- ============================================================================

/-- ADDI rd, rs1, imm: rd := rs1 + sext(imm) (registers distinct) -/
theorem addi_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .ADDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) :=
  generic_2reg_spec (.ADDI rd rs1 imm) rs1 rd v1 v_old (v1 + signExtend12 imm) base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADDI rd, rd, imm: rd := rd + sext(imm) (same register) -/
theorem addi_spec_same (rd : Reg) (v : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADDI rd rd imm) ** (rd ↦ᵣ v))
      ((base ↦ᵢ .ADDI rd rd imm) ** (rd ↦ᵣ (v + signExtend12 imm))) :=
  generic_1reg_spec (.ADDI rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Upper Immediate Instructions
-- ============================================================================

/-- LUI rd, imm: rd := imm << 12 -/
theorem lui_spec (rd : Reg) (v_old : Word) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .LUI rd imm) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .LUI rd imm) ** (rd ↦ᵣ ((imm.zeroExtend 32 : Word) <<< 12))) :=
  generic_1reg_spec (.LUI rd imm) rd v_old _ base hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- AUIPC rd, imm: rd := PC + (imm << 12) -/
theorem auipc_spec (rd : Reg) (v_old : Word) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .AUIPC rd imm) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .AUIPC rd imm) ** (rd ↦ᵣ (base + ((imm.zeroExtend 32 : Word) <<< 12)))) :=
  generic_1reg_spec (.AUIPC rd imm) rd v_old _ base hrd_ne_x0
    (by intro s hpc _; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Memory Instructions
-- ============================================================================

/-- LW rd, offset(rs1): rd := mem[rs1 + sext(offset)] (registers distinct) -/
theorem lw_spec (rd rs1 : Reg) (v_addr v_old mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .LW rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((base ↦ᵢ .LW rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) :=
  generic_lw_spec rd rs1 v_addr v_old mem_val offset base hrd_ne_x0 hvalid

/-- LW rd, offset(rd): rd := mem[rd + sext(offset)] (same register) -/
theorem lw_spec_same (rd : Reg) (v_addr mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .LW rd rd offset) ** (rd ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((base ↦ᵢ .LW rd rd offset) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) := by
  intro R hR s hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LW rd rd offset) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrd : s.getReg rd = v_addr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem (v_addr + signExtend12 offset) = mem_val :=
    (holdsFor_memIs _ _ s).mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LW rd rd offset)) :=
    step_lw s rd rd offset hfetch (hrd ▸ hvalid)
  have hexec' : execInstrBr s (.LW rd rd offset) = (s.setReg rd mem_val).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrd, hmem]
  refine ⟨1, (s.setReg rd mem_val).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg (v' := mem_val) hrd_ne_x0 h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h4

/-- SW rs2, offset(rs1): mem[rs1 + sext(offset)] := rs2 (registers distinct) -/
theorem sw_spec (rs1 rs2 : Reg) (v_addr v_data mem_old : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .SW rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((base ↦ᵢ .SW rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) :=
  generic_sw_spec rs1 rs2 v_addr v_data mem_old offset base hvalid

/-- SW rs, offset(rs): mem[rs + sext(offset)] := rs (same register) -/
theorem sw_spec_same (rs : Reg) (v : Word) (mem_old : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .SW rs rs offset) ** (rs ↦ᵣ v) ** ((v + signExtend12 offset) ↦ₘ mem_old))
      ((base ↦ᵢ .SW rs rs offset) ** (rs ↦ᵣ v) ** ((v + signExtend12 offset) ↦ₘ v)) := by
  intro R hR s hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SW rs rs offset) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs : s.getReg rs = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.SW rs rs offset)) :=
    step_sw s rs rs offset hfetch (hrs ▸ hvalid)
  have hexec' : execInstrBr s (.SW rs rs offset) =
      (s.setMem (v + signExtend12 offset) v).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs]
  refine ⟨1, (s.setMem (v + signExtend12 offset) v).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIs_setMem (v' := v) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h5

-- ============================================================================
-- Branch Instructions (use cpsBranch for two exits)
-- ============================================================================

/-- BEQ rs1, rs2, offset: branch if rs1 = rs2 (registers distinct) -/
theorem beq_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    cpsBranch base
      ((base ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset) ((base ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (base + 4) ((base ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) :=
  generic_beq_spec rs1 rs2 offset v1 v2 base

/-- BEQ rs, rs, offset: branch if rs = rs (always taken, same register) -/
theorem beq_spec_same (rs : Reg) (offset : BitVec 13) (v : Word) (base : Addr) :
    cpsBranch base
      ((base ↦ᵢ .BEQ rs rs offset) ** (rs ↦ᵣ v))
      (base + signExtend13 offset) ((base ↦ᵢ .BEQ rs rs offset) ** (rs ↦ᵣ v))
      (base + 4) ((base ↦ᵢ .BEQ rs rs offset) ** (rs ↦ᵣ v)) := by
  intro R hR s hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs rs offset) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs : s.getReg rs = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BEQ rs rs offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs rs offset) = s.setPC (s.pc + signExtend13 offset) := by
    simp only [execInstrBr, hrs, beq_self_eq_true, ite_true]
  refine ⟨1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ hPR

/-- BNE rs1, rs2, offset: branch if rs1 ≠ rs2 (registers distinct) -/
theorem bne_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    cpsBranch base
      ((base ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset) ((base ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (base + 4) ((base ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) :=
  generic_bne_spec rs1 rs2 offset v1 v2 base

/-- BNE rs, rs, offset: branch if rs ≠ rs (never taken, same register) -/
theorem bne_spec_same (rs : Reg) (offset : BitVec 13) (v : Word) (base : Addr) :
    cpsBranch base
      ((base ↦ᵢ .BNE rs rs offset) ** (rs ↦ᵣ v))
      (base + signExtend13 offset) ((base ↦ᵢ .BNE rs rs offset) ** (rs ↦ᵣ v))
      (base + 4) ((base ↦ᵢ .BNE rs rs offset) ** (rs ↦ᵣ v)) := by
  intro R hR s hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BNE rs rs offset) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs : s.getReg rs = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BNE rs rs offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BNE rs rs offset) = s.setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
  refine ⟨1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ hPR

-- ============================================================================
-- Jump Instructions
-- ============================================================================

/-- JAL rd, offset: rd := PC + 4; PC := PC + sext(offset) -/
theorem jal_spec (rd : Reg) (v_old : Word) (offset : BitVec 21) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + signExtend21 offset)
      ((base ↦ᵢ .JAL rd offset) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .JAL rd offset) ** (rd ↦ᵣ (base + 4))) :=
  generic_jal_spec rd v_old offset base hrd_ne_x0

/-- JALR rd, rs1, offset: rd := PC + 4; PC := (rs1 + sext(offset)) & ~1 (distinct) -/
theorem jalr_spec (rd rs1 : Reg) (v1 v_old : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base ((v1 + signExtend12 offset) &&& (~~~1))
      ((base ↦ᵢ .JALR rd rs1 offset) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .JALR rd rs1 offset) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))) :=
  generic_jalr_spec rd rs1 v1 v_old offset base hrd_ne_x0

/-- JALR rd, rd, offset: rd := PC + 4; PC := (rd + sext(offset)) & ~1 (same) -/
theorem jalr_spec_same (rd : Reg) (v : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base ((v + signExtend12 offset) &&& (~~~1))
      ((base ↦ᵢ .JALR rd rd offset) ** (rd ↦ᵣ v))
      ((base ↦ᵢ .JALR rd rd offset) ** (rd ↦ᵣ (base + 4))) := by
  intro R hR s hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JALR rd rd offset) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrd : s.getReg rd = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.JALR rd rd offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.JALR rd rd offset) =
      (s.setReg rd (s.pc + 4)).setPC ((v + signExtend12 offset) &&& ~~~1) := by
    simp only [execInstrBr, hrd]; rfl
  refine ⟨1, (s.setReg rd (s.pc + 4)).setPC ((v + signExtend12 offset) &&& ~~~1), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4) hrd_ne_x0 h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h3

-- ============================================================================
-- Pseudo Instructions
-- ============================================================================

/-- MV rd, rs: rd := rs (pseudo for ADDI rd, rs, 0) -/
theorem mv_spec (rd rs : Reg) (v v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .MV rd rs) ** (rs ↦ᵣ v) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .MV rd rs) ** (rs ↦ᵣ v) ** (rd ↦ᵣ v)) :=
  generic_2reg_spec (.MV rd rs) rs rd v v_old v base hrd_ne_x0
    (by intro s _ hrs _; simp [execInstrBr, hrs])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- LI rd, imm: rd := imm (pseudo for loading immediate) -/
theorem li_spec (rd : Reg) (v_old imm : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .LI rd imm) ** (rd ↦ᵣ v_old))
      ((base ↦ᵢ .LI rd imm) ** (rd ↦ᵣ imm)) :=
  generic_1reg_spec (.LI rd imm) rd v_old _ base hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- NOP: no operation (pseudo for ADDI x0, x0, 0) -/
theorem nop_spec (base : Addr) :
    cpsTriple base (base + 4)
      (base ↦ᵢ .NOP)
      (base ↦ᵢ .NOP) :=
  generic_nop_spec .NOP base (base + 4)
    (by intro s hpc; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- System Instructions
-- ============================================================================

/-- FENCE: memory fence (NOP in single-hart zkVM) -/
theorem fence_spec (base : Addr) :
    cpsTriple base (base + 4)
      (base ↦ᵢ .FENCE)
      (base ↦ᵢ .FENCE) :=
  generic_nop_spec .FENCE base (base + 4)
    (by intro s hpc; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Summary
-- ============================================================================

/-!
  ## Instruction Specifications Summary

  This module provides separation logic specifications for RISC-V instructions
  using CPS-style specifications with built-in frame rule.

  All specs include `instrAt` (base ↦ᵢ instr) in both pre and postconditions,
  required after the CodeMem unification.
-/

end EvmAsm
