/-
  EvmAsm.Rv32.GenericSpecs

  Parametric (generic) separation-logic specifications for single-instruction
  execution patterns.  Each lemma factors out the common proof shape:

    1. Extract code fetch from CodeReq side-condition.
    2. Extract register / memory values from the precondition.
    3. Show `step s = some nextState` using the extracted values.
    4. Rearrange the separating conjunction to apply the update lemma.
    5. Update the PC using `holdsFor_pcFree_setPC`.

  Concrete per-instruction specs (in InstructionSpecs.lean and SyscallSpecs.lean)
  are one-line applications of these generic lemmas.
-/

import EvmAsm.Rv32.Basic
import EvmAsm.Rv32.Instructions
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.CPSSpec

namespace EvmAsm

-- ============================================================================
-- Group 1: Single register (rd only), setReg rd result
-- Used for: ADDI same, XORI same, SLTIU same, SRLI same, LUI, AUIPC, LI
-- ============================================================================

/-- Generic spec for instructions that read/write a single register rd.
    Pre:  (rd ↦ᵣ v)
    Post: (rd ↦ᵣ result)
    Code requirement: CodeReq.singleton base instr
    The `hexec` hypothesis relates `execInstrBr` to `setReg rd result` given
    that `s.pc = base` and `s.getReg rd = v`. -/
theorem generic_1reg_spec (instr : Instr) (rd : Reg) (v result : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hexec : ∀ s, s.pc = base → s.getReg rd = v →
      execInstrBr s instr = (s.setReg rd result).setPC (s.pc + 4))
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base instr)
      (rd ↦ᵣ v)
      (rd ↦ᵣ result) := by
  intro R hR s hcr hPR hpc; subst hpc
  -- Extract code fetch from CodeReq
  have hfetch : s.code s.pc = some instr :=
    (CodeReq.singleton_satisfiedBy s.pc instr s).mp hcr
  have hrd : s.getReg rd = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left hPR)
  -- Compute next state
  have hexec' := hexec s rfl hrd
  have hstep' := hstep s hfetch
  -- Witness: 1 step
  refine ⟨1, (s.setReg rd result).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · -- stepN 1 s = some nextState
    show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Postcondition
    have h2 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR) _ _ h2

-- ============================================================================
-- Group 2: Two registers, rd ≠ rs1 (rs1 preserved, rd updated)
-- Used for: ADDI, ANDI, SLTIU (rd ≠ rs1), SUB rd=rs2, MV, ADDI gen
-- ============================================================================

/-- Generic spec for instructions with two distinct registers (rs source, rd dest).
    Pre:  (rs ↦ᵣ v_src) ** (rd ↦ᵣ v_old)
    Post: (rs ↦ᵣ v_src) ** (rd ↦ᵣ result) -/
theorem generic_2reg_spec (instr : Instr) (rs rd : Reg)
    (v_src v_old result : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hexec : ∀ s, s.pc = base → s.getReg rs = v_src → s.getReg rd = v_old →
      execInstrBr s instr = (s.setReg rd result).setPC (s.pc + 4))
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base instr)
      ((rs ↦ᵣ v_src) ** (rd ↦ᵣ v_old))
      ((rs ↦ᵣ v_src) ** (rd ↦ᵣ result)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some instr :=
    (CodeReq.singleton_satisfiedBy s.pc instr s).mp hcr
  have hrs : s.getReg rs = v_src :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrd : s.getReg rd = v_old :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hexec' := hexec s rfl hrs hrd
  have hstep' := hstep s hfetch
  refine ⟨1, (s.setReg rd result).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 2) to front
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    -- h1 : (rd ** (rs ** R))
    have h2 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    -- h3 : ((rs ** rd) ** R), apply setPC
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs v_src) (pcFree_regIs rd result)) hR) _ _ h3

-- ============================================================================
-- Group 3: Two registers, rd = rs1 (rd updated, rs2 preserved)
-- Used for: ADD rd=rs1, SUB rd=rs1, AND/OR/XOR/SLTU/SRL/SLL rd=rs1
-- ============================================================================

/-- Generic spec for ALU instructions where rd = rs1 (2 registers: rd, rs2).
    Pre:  (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    Post: (rd ↦ᵣ result) ** (rs2 ↦ᵣ v2) -/
theorem generic_2reg_rd_eq_rs1_spec (instr : Instr) (rd rs2 : Reg)
    (v1 v2 result : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hexec : ∀ s, s.pc = base → s.getReg rd = v1 → s.getReg rs2 = v2 →
      execInstrBr s instr = (s.setReg rd result).setPC (s.pc + 4))
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base instr)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ result) ** (rs2 ↦ᵣ v2)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some instr :=
    (CodeReq.singleton_satisfiedBy s.pc instr s).mp hcr
  have hrd : s.getReg rd = v1 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hexec' := hexec s rfl hrd hrs2
  have hstep' := hstep s hfetch
  refine ⟨1, (s.setReg rd result).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 1) to front, assoc then update
    have h1a := holdsFor_sepConj_assoc.mp hPR
    -- h1a : (rd ** (rs2 ** R))
    have h2 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 h1a
    -- Rearrange back: (rd' ** (rs2 ** R)) → ((rd' ** rs2) ** R)
    have h3 := holdsFor_sepConj_assoc.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_regIs rs2 v2)) hR) _ _ h3

-- ============================================================================
-- Group 4: Three distinct registers (rs1, rs2 preserved, rd updated)
-- Used for: ADD, SUB, AND, OR, XOR, SLTU (all distinct)
-- ============================================================================

/-- Generic spec for ALU instructions with 3 distinct registers.
    Pre:  (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old)
    Post: (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ result) -/
theorem generic_3reg_spec (instr : Instr) (rs1 rs2 rd : Reg)
    (v1 v2 v_old result : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hexec : ∀ s, s.pc = base → s.getReg rs1 = v1 → s.getReg rs2 = v2 →
      execInstrBr s instr = (s.setReg rd result).setPC (s.pc + 4))
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base instr)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ result)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some instr :=
    (CodeReq.singleton_satisfiedBy s.pc instr s).mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hexec' := hexec s rfl hrs1 hrs2
  have hstep' := hstep s hfetch
  refine ⟨1, (s.setReg rd result).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 3 in inner) to front: 2 pull_seconds
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    -- h2 : (rd ** (rs2 ** (rs1 ** R)))
    have h3 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_sepConj (pcFree_regIs rs2 v2) (pcFree_regIs rd result))) hR) _ _ h5

-- ============================================================================
-- Group 5: NOP-like (just PC advance, no register/memory changes)
-- Used for: NOP, FENCE, JAL x0
-- ============================================================================

/-- Generic spec for instructions that only advance PC without changing state.
    Pre/Post: empAssertion  [frame handles the rest] -/
theorem generic_nop_spec (instr : Instr) (base exit_ : Addr)
    (hexec : ∀ s, s.pc = base → execInstrBr s instr = s.setPC exit_)
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTriple base exit_
      (CodeReq.singleton base instr)
      empAssertion
      empAssertion := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some instr :=
    (CodeReq.singleton_satisfiedBy s.pc instr s).mp hcr
  have hexec' := hexec s rfl
  have hstep' := hstep s hfetch
  refine ⟨1, s.setPC exit_, ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree_emp hR) _ _ hPR

-- ============================================================================
-- Group 6: LW (memory load, rd ≠ rs1)
-- ============================================================================

/-- Generic spec for LW: load word from memory.
    Pre:  (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** (addr ↦ₘ mem_val)
    Post: (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    where addr = v_addr + signExtend12 offset -/
theorem generic_lw_spec (rd rs1 : Reg) (v_addr v_old mem_val : Word)
    (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.LW rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LW rd rs1 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.LW rd rs1 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem (v_addr + signExtend12 offset) = mem_val :=
    (holdsFor_memIs _ _ s).mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  -- Step proof using step_lw
  have hstep' : step s = some (execInstrBr s (.LW rd rs1 offset)) :=
    step_lw s rd rs1 offset hfetch (hrs1 ▸ hvalid)
  -- execInstrBr s (.LW rd rs1 offset) = (s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 offset))).setPC (s.pc + 4)
  have hexec' : execInstrBr s (.LW rd rs1 offset) = (s.setReg rd mem_val).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hmem]
  refine ⟨1, (s.setReg rd mem_val).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 2) to front: 1 pull_second + assoc
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    -- h1 : ((rd ** mem) ** (rs1 ** R))
    -- Need to separate rd from mem first
    have h2 := holdsFor_sepConj_assoc.mp h1
    -- h2 : (rd ** (mem ** (rs1 ** R)))
    have h3 := holdsFor_sepConj_regIs_setReg (v' := mem_val) hrd_ne_x0 h2
    have h4 := holdsFor_sepConj_assoc.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v_addr) (pcFree_sepConj (pcFree_regIs rd mem_val) (pcFree_memIs _ _))) hR) _ _ h5

-- ============================================================================
-- Group 7: SW (memory store, all distinct registers)
-- ============================================================================

/-- Generic spec for SW: store word to memory.
    Pre:  (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ mem_old)
    Post: (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data)
    where addr = v_addr + signExtend12 offset -/
theorem generic_sw_spec (rs1 rs2 : Reg) (v_addr v_data mem_old : Word)
    (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.SW rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SW rs1 rs2 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.SW rs1 rs2 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  -- Step proof using step_sw
  have hstep' : step s = some (execInstrBr s (.SW rs1 rs2 offset)) :=
    step_sw s rs1 rs2 offset hfetch (hrs1 ▸ hvalid)
  -- execInstrBr: setMem then setPC
  have hexec' : execInstrBr s (.SW rs1 rs2 offset) =
      (s.setMem (v_addr + signExtend12 offset) v_data).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2]
  refine ⟨1, (s.setMem (v_addr + signExtend12 offset) v_data).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull mem (position 3) to front: 2 pull_seconds
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    -- h2 : (mem ** (rs2 ** (rs1 ** R)))
    have h3 := holdsFor_sepConj_memIs_setMem (v' := v_data) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v_addr) (pcFree_sepConj (pcFree_regIs rs2 v_data) (pcFree_memIs _ _))) hR) _ _ h5

-- ============================================================================
-- Group 8: SW with x0 (stores 0, no x0 register in pre/post)
-- ============================================================================

/-- Generic spec for SW with rs2 = x0: store 0 to memory.
    Pre:  (rs1 ↦ᵣ v_addr) ** (addr ↦ₘ mem_old)
    Post: (rs1 ↦ᵣ v_addr) ** (addr ↦ₘ 0) -/
theorem generic_sw_x0_spec (rs1 : Reg) (v_addr mem_old : Word)
    (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.SW rs1 .x0 offset))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ (0 : Word))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SW rs1 .x0 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.SW rs1 .x0 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.SW rs1 .x0 offset)) :=
    step_sw s rs1 .x0 offset hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.SW rs1 .x0 offset) =
      (s.setMem (v_addr + signExtend12 offset) 0).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1]; rfl
  refine ⟨1, (s.setMem (v_addr + signExtend12 offset) 0).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_memIs_setMem (v' := (0 : Word)) h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v_addr) (pcFree_memIs _ _)) hR) _ _ h3

-- ============================================================================
-- Group 9: Branch (BNE/BEQ) — cpsBranch
-- ============================================================================

/-- Generic spec for BNE: branch if not equal.
    Pre:  (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    Taken (v1 ≠ v2): PC = base + signExtend13 offset, post includes ⌜v1 ≠ v2⌝
    Not taken (v1 = v2): PC = base + 4, post includes ⌜v1 = v2⌝ -/
theorem generic_bne_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    cpsBranch base
      (CodeReq.singleton base (.BNE rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (base + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BNE rs1 rs2 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.BNE rs1 rs2 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BNE rs1 rs2 offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  -- Case split on v1 = v2
  by_cases heq : v1 = v2
  · -- Not taken: v1 = v2
    have hexec' : execInstrBr s (.BNE rs1 rs2 offset) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1, hrs2, heq, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
    refine ⟨1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · -- Add pure assertion ⌜v1 = v2⌝
      have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_regIs rs2 v2)) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free s (s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right _ _ h1b).mpr ⟨hRs2, heq⟩⟩, hR2⟩
  · -- Taken: v1 ≠ v2
    have hexec' : execInstrBr s (.BNE rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
      simp only [execInstrBr, hrs1, hrs2, bne_iff_ne, ne_eq, heq, not_false_eq_true, ite_true]
    refine ⟨1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_regIs rs2 v2)) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free s (s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right _ _ h1b).mpr ⟨hRs2, heq⟩⟩, hR2⟩

/-- Generic spec for BEQ: branch if equal. -/
theorem generic_beq_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    cpsBranch base
      (CodeReq.singleton base (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (base + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 rs2 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.BEQ rs1 rs2 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 rs2 offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  by_cases heq : v1 = v2
  · -- Taken: v1 = v2
    have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
      simp only [execInstrBr, hrs1, hrs2, heq, beq_self_eq_true, ite_true]
    refine ⟨1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_regIs rs2 v2)) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free s (s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right _ _ h1b).mpr ⟨hRs2, heq⟩⟩, hR2⟩
  · -- Not taken: v1 ≠ v2
    have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1, hrs2, beq_iff_eq, heq, ite_false]
    refine ⟨1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_regIs rs2 v2)) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free s (s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right _ _ h1b).mpr ⟨hRs2, heq⟩⟩, hR2⟩

-- ============================================================================
-- Group 10: JAL (jump and link)
-- ============================================================================

/-- Generic spec for JAL: rd := PC + 4, PC := PC + sext(offset).
    Pre:  (rd ↦ᵣ v_old)
    Post: (rd ↦ᵣ (base + 4)) -/
theorem generic_jal_spec (rd : Reg) (v_old : Word) (offset : BitVec 21) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base (base + signExtend21 offset)
      (CodeReq.singleton base (.JAL rd offset))
      (rd ↦ᵣ v_old)
      (rd ↦ᵣ (base + 4)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JAL rd offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.JAL rd offset) s).mp hcr
  have hstep' : step s = some (execInstrBr s (.JAL rd offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  -- execInstrBr s (.JAL rd offset) = (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 offset)
  refine ⟨1, (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 offset), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep']; rfl
  · have h1 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd (s.pc + 4)) hR) _ _ h1

/-- Generic spec for JALR: rd := PC + 4, PC := (rs1 + sext(offset)) & ~1.
    Pre:  (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)
    Post: (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4)) -/
theorem generic_jalr_spec (rd rs1 : Reg) (v1 v_old : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple base ((v1 + signExtend12 offset) &&& ~~~1)
      (CodeReq.singleton base (.JALR rd rs1 offset))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JALR rd rs1 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.JALR rd rs1 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.JALR rd rs1 offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.JALR rd rs1 offset) =
      (s.setReg rd (s.pc + 4)).setPC ((v1 + signExtend12 offset) &&& ~~~1) := by
    simp only [execInstrBr, hrs1]; rfl
  refine ⟨1, (s.setReg rd (s.pc + 4)).setPC ((v1 + signExtend12 offset) &&& ~~~1), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 2) to front
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4) hrd_ne_x0 h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_regIs rd (s.pc + 4))) hR) _ _ h3

end EvmAsm
