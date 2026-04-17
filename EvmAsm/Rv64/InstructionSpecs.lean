/-
  EvmAsm.Rv64.InstructionSpecs

  Separation logic specifications for each RISC-V (RV64) instruction using cpsTriple
  (or cpsBranch for conditional branches).

  Code is accessed via CodeReq.singleton side-condition (not instrAt in P/Q).

  Proofs delegate to the generic lemmas in GenericSpecs.lean.

  Ported from EvmAsm.InstructionSpecs (RV32) with the following changes:
  - LUI/AUIPC: postcondition uses signExtend 64 of the 32-bit shifted value
  - LW/SW specs removed (RV64 LW uses getWord32, not getMem)
  - LD/SD specs added using generic_ld_spec/generic_sd_spec
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.GenericSpecs

namespace EvmAsm.Rv64

-- ============================================================================
-- ALU Instructions (Register-Register): All Distinct Case
-- ============================================================================

/-- ADD rd, rs1, rs2: rd := rs1 + rs2 (all registers distinct) -/
theorem add_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADD rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 + v2))) :=
  generic_3reg_spec (.ADD rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ base hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADD rd, rd, rs2: rd := rd + rs2 (rd = rs1, rs2 distinct) -/
theorem add_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADD rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.ADD rd rd rs2) rd rs2 v1 v2 _ base hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADD rd, rs1, rd: rd := rs1 + rd (rd = rs2, rs1 distinct) -/
theorem add_spec_rd_eq_rs2 (rd rs1 : Reg) (v1 v2 : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADD rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + v2))) :=
  generic_2reg_spec (.ADD rd rs1 rd) rs1 rd v1 v2 (v1 + v2) base hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADD rd, rd, rd: rd := rd + rd = 2 * rd (all same) -/
theorem add_spec_all_same (rd : Reg) (v : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADD rd rd rd))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v + v)) :=
  generic_1reg_spec (.ADD rd rd rd) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB rd, rs1, rs2: rd := rs1 - rs2 (all registers distinct) -/
theorem sub_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.SUB rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 - v2))) :=
  generic_3reg_spec (.SUB rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ base hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB rd, rd, rs2: rd := rd - rs2 -/
theorem sub_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.SUB rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SUB rd rd rs2) rd rs2 v1 v2 _ base hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB rd, rd, rd: rd := rd - rd = 0 -/
theorem sub_spec_all_same (rd : Reg) (v : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.SUB rd rd rd))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v - v)) :=
  generic_1reg_spec (.SUB rd rd rd) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- ALU Instructions (Immediate)
-- ============================================================================

/-- ADDI rd, rs1, imm: rd := rs1 + sext(imm) (registers distinct) -/
theorem addi_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADDI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) :=
  generic_2reg_spec (.ADDI rd rs1 imm) rs1 rd v1 v_old (v1 + signExtend12 imm) base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADDI rd, rd, imm: rd := rd + sext(imm) (same register) -/
theorem addi_spec_same (rd : Reg) (v : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADDI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v + signExtend12 imm)) :=
  generic_1reg_spec (.ADDI rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- ALU Instructions (Immediate): ORI
-- ============================================================================

/-- ORI rd, rs1, imm: rd := rs1 | sext(imm) (registers distinct) -/
theorem ori_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ORI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 ||| signExtend12 imm))) :=
  generic_2reg_spec (.ORI rd rs1 imm) rs1 rd v1 v_old (v1 ||| signExtend12 imm) base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ORI rd, rd, imm: rd := rd | sext(imm) (same register) -/
theorem ori_spec_same (rd : Reg) (v : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ORI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v ||| signExtend12 imm)) :=
  generic_1reg_spec (.ORI rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- ALU Instructions (Immediate): SLTI
-- ============================================================================

/-- SLTI rd, rs1, imm: rd := (rs1 <s sext(imm)) ? 1 : 0 (registers distinct) -/
theorem slti_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.SLTI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.slt v1 (signExtend12 imm) then 1 else 0))) :=
  generic_2reg_spec (.SLTI rd rs1 imm) rs1 rd v1 v_old _ base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SLTI rd, rd, imm: rd := (rd <s sext(imm)) ? 1 : 0 (same register) -/
theorem slti_spec_same (rd : Reg) (v : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.SLTI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (if BitVec.slt v (signExtend12 imm) then 1 else 0)) :=
  generic_1reg_spec (.SLTI rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- RV64I Word Instructions: ADDIW
-- ============================================================================

/-- ADDIW rd, rs1, imm: rd := signExtend64(truncate32(rs1) + truncate32(sext(imm))) (registers distinct) -/
theorem addiw_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADDIW rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ ((v1.truncate 32 + (signExtend12 imm).truncate 32 : BitVec 32).signExtend 64))) :=
  generic_2reg_spec (.ADDIW rd rs1 imm) rs1 rd v1 v_old _ base hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADDIW rd, rd, imm: rd := signExtend64(truncate32(rd) + truncate32(sext(imm))) (same register) -/
theorem addiw_spec_same (rd : Reg) (v : Word) (imm : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADDIW rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ ((v.truncate 32 + (signExtend12 imm).truncate 32 : BitVec 32).signExtend 64)) :=
  generic_1reg_spec (.ADDIW rd rd imm) rd v _ base hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Upper Immediate Instructions
-- ============================================================================

/-- LUI rd, imm: rd := signExtend64(imm << 12)
    In RV64, LUI sign-extends the 32-bit result to 64 bits. -/
theorem lui_spec (rd : Reg) (v_old : Word) (imm : BitVec 20) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.LUI rd imm))
      (rd ↦ᵣ v_old)
      (rd ↦ᵣ ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) :=
  generic_1reg_spec (.LUI rd imm) rd v_old _ base hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- AUIPC rd, imm: rd := PC + signExtend64(imm << 12)
    In RV64, AUIPC sign-extends the 32-bit shifted value before adding to PC. -/
theorem auipc_spec (rd : Reg) (v_old : Word) (imm : BitVec 20) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.AUIPC rd imm))
      (rd ↦ᵣ v_old)
      (rd ↦ᵣ (base + ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) :=
  generic_1reg_spec (.AUIPC rd imm) rd v_old _ base hrd_ne_x0
    (by intro s hpc _; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Memory Instructions (LD/SD for 64-bit doubleword access)
-- ============================================================================

/-- LD rd, offset(rs1): rd := mem[rs1 + sext(offset)] (registers distinct) -/
theorem ld_spec (rd rs1 : Reg) (v_addr v_old mem_val : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.LD rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) :=
  generic_ld_spec rd rs1 v_addr v_old mem_val offset base hrd_ne_x0

/-- LD rd, offset(rd): rd := mem[rd + sext(offset)] (same register) -/
theorem ld_spec_same (rd : Reg) (v_addr mem_val : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.LD rd rd offset))
      ((rd ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LD rd rd offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.LD rd rd offset) s).mp hcr
  have hrd : s.getReg rd = v_addr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hmem_piece := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)
  have hmem : s.getMem (v_addr + signExtend12 offset) = mem_val :=
    holdsFor_memIs_getMem hmem_piece
  have hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true :=
    holdsFor_memIs_isValidDwordAccess hmem_piece
  have hstep' : step s = some (execInstrBr s (.LD rd rd offset)) :=
    step_ld s rd rd offset hfetch (hrd ▸ hvalid)
  have hexec' : execInstrBr s (.LD rd rd offset) = (s.setReg rd mem_val).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrd, hmem]
  refine ⟨1, (s.setReg rd mem_val).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pre: (rd ** mem) ** R → assoc → rd ** (mem ** R)
    have h1 := holdsFor_sepConj_assoc.mp hPR
    -- Update rd: rd ** (mem ** R) → rd' ** (mem ** R)
    have h2 := holdsFor_sepConj_regIs_setReg (v' := mem_val) hrd_ne_x0 h1
    -- Reassociate: rd' ** (mem ** R) → (rd' ** mem) ** R
    have h3 := holdsFor_sepConj_assoc.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h3

/-- SD rs2, offset(rs1): mem[rs1 + sext(offset)] := rs2 (registers distinct) -/
theorem sd_spec (rs1 rs2 : Reg) (v_addr v_data mem_old : Word) (offset : BitVec 12) (base : Word) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) :=
  generic_sd_spec rs1 rs2 v_addr v_data mem_old offset base

/-- SD rs, offset(rs): mem[rs + sext(offset)] := rs (same register) -/
theorem sd_spec_same (rs : Reg) (v : Word) (mem_old : Word) (offset : BitVec 12) (base : Word) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.SD rs rs offset))
      ((rs ↦ᵣ v) ** ((v + signExtend12 offset) ↦ₘ mem_old))
      ((rs ↦ᵣ v) ** ((v + signExtend12 offset) ↦ₘ v)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SD rs rs offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.SD rs rs offset) s).mp hcr
  have hrs : s.getReg rs = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hvalid : isValidDwordAccess (v + signExtend12 offset) = true :=
    holdsFor_memIs_isValidDwordAccess (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.SD rs rs offset)) :=
    step_sd s rs rs offset hfetch (hrs ▸ hvalid)
  have hexec' : execInstrBr s (.SD rs rs offset) =
      (s.setMem (v + signExtend12 offset) v).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs]
  refine ⟨1, (s.setMem (v + signExtend12 offset) v).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_memIs_setMem (v' := v) h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h3

-- ============================================================================
-- Branch Instructions (use cpsBranch for two exits)
-- ============================================================================

/-- BEQ rs1, rs2, offset: branch if rs1 = rs2 (registers distinct) -/
theorem beq_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranch base (CodeReq.singleton base (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) :=
  generic_beq_spec rs1 rs2 offset v1 v2 base

/-- BEQ rs, rs, offset: branch if rs = rs (always taken, same register) -/
theorem beq_spec_same (rs : Reg) (offset : BitVec 13) (v : Word) (base : Word) :
    cpsBranch base (CodeReq.singleton base (.BEQ rs rs offset))
      (rs ↦ᵣ v)
      (base + signExtend13 offset) (rs ↦ᵣ v)
      (base + 4) (rs ↦ᵣ v) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs rs offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.BEQ rs rs offset) s).mp hcr
  have hrs : s.getReg rs = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.BEQ rs rs offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs rs offset) = s.setPC (s.pc + signExtend13 offset) := by
    simp only [execInstrBr, hrs, beq_self_eq_true, ite_true]
  refine ⟨1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ hPR

/-- BNE rs1, rs2, offset: branch if rs1 ≠ rs2 (registers distinct) -/
theorem bne_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranch base (CodeReq.singleton base (.BNE rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) :=
  generic_bne_spec rs1 rs2 offset v1 v2 base

/-- BNE rs, rs, offset: branch if rs ≠ rs (never taken, same register) -/
theorem bne_spec_same (rs : Reg) (offset : BitVec 13) (v : Word) (base : Word) :
    cpsBranch base (CodeReq.singleton base (.BNE rs rs offset))
      (rs ↦ᵣ v)
      (base + signExtend13 offset) (rs ↦ᵣ v)
      (base + 4) (rs ↦ᵣ v) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BNE rs rs offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.BNE rs rs offset) s).mp hcr
  have hrs : s.getReg rs = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.BNE rs rs offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BNE rs rs offset) = s.setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
  refine ⟨1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ hPR

-- ============================================================================
-- Branch Instructions: BGEU
-- ============================================================================

/-- BGEU rs1, rs2, offset: branch if rs1 >=u rs2 (registers distinct) -/
theorem bgeu_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranch base (CodeReq.singleton base (.BGEU rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.ult v1 v2⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.ult v1 v2⌝) :=
  generic_bgeu_spec rs1 rs2 offset v1 v2 base

-- ============================================================================
-- Jump Instructions
-- ============================================================================

/-- JAL rd, offset: rd := PC + 4; PC := PC + sext(offset) -/
theorem jal_spec (rd : Reg) (v_old : Word) (offset : BitVec 21) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + signExtend21 offset) (CodeReq.singleton base (.JAL rd offset))
      (rd ↦ᵣ v_old)
      (rd ↦ᵣ (base + 4)) :=
  generic_jal_spec rd v_old offset base hrd_ne_x0

/-- JALR rd, rs1, offset: rd := PC + 4; PC := (rs1 + sext(offset)) & ~1 (distinct) -/
theorem jalr_spec (rd rs1 : Reg) (v1 v_old : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base ((v1 + signExtend12 offset) &&& (~~~1)) (CodeReq.singleton base (.JALR rd rs1 offset))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))) :=
  generic_jalr_spec rd rs1 v1 v_old offset base hrd_ne_x0

/-- JALR rd, rd, offset: rd := PC + 4; PC := (rd + sext(offset)) & ~1 (same) -/
theorem jalr_spec_same (rd : Reg) (v : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base ((v + signExtend12 offset) &&& (~~~1)) (CodeReq.singleton base (.JALR rd rd offset))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (base + 4)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JALR rd rd offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.JALR rd rd offset) s).mp hcr
  have hrd : s.getReg rd = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.JALR rd rd offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.JALR rd rd offset) =
      (s.setReg rd (s.pc + 4)).setPC ((v + signExtend12 offset) &&& ~~~1) := by
    simp only [execInstrBr, hrd]; rfl
  refine ⟨1, (s.setReg rd (s.pc + 4)).setPC ((v + signExtend12 offset) &&& ~~~1), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h1

-- ============================================================================
-- Pseudo Instructions
-- ============================================================================

/-- MV rd, rs: rd := rs (pseudo for ADDI rd, rs, 0) -/
theorem mv_spec (rd rs : Reg) (v v_old : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.MV rd rs))
      ((rs ↦ᵣ v) ** (rd ↦ᵣ v_old))
      ((rs ↦ᵣ v) ** (rd ↦ᵣ v)) :=
  generic_2reg_spec (.MV rd rs) rs rd v v_old v base hrd_ne_x0
    (by intro s _ hrs _; simp [execInstrBr, hrs])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- LI rd, imm: rd := imm (pseudo for loading immediate) -/
theorem li_spec (rd : Reg) (v_old imm : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.LI rd imm))
      (rd ↦ᵣ v_old)
      (rd ↦ᵣ imm) :=
  generic_1reg_spec (.LI rd imm) rd v_old _ base hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- NOP: no operation (pseudo for ADDI x0, x0, 0) -/
theorem nop_spec (base : Word) :
    cpsTriple base (base + 4) (CodeReq.singleton base .NOP)
      empAssertion
      empAssertion :=
  generic_nop_spec .NOP base (base + 4)
    (by intro s hpc; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- System Instructions
-- ============================================================================

/-- FENCE: memory fence (NOP in single-hart zkVM) -/
theorem fence_spec (base : Word) :
    cpsTriple base (base + 4) (CodeReq.singleton base .FENCE)
      empAssertion
      empAssertion :=
  generic_nop_spec .FENCE base (base + 4)
    (by intro s hpc; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Summary
-- ============================================================================

/-!
  ## Instruction Specifications Summary

  This module provides separation logic specifications for RV64 instructions
  using CPS-style specifications with built-in frame rule.

  Code is accessed via CodeReq.singleton side-condition (not instrAt in P/Q).

  Differences from the RV32 version (EvmAsm.InstructionSpecs):
  - LUI/AUIPC: result is sign-extended from 32 bits to 64 bits
  - LW/SW specs removed (RV64 LW uses getWord32 + signExtend, not getMem/setMem)
  - LD/SD specs added for 64-bit doubleword memory access using isValidDwordAccess
-/

end EvmAsm.Rv64
