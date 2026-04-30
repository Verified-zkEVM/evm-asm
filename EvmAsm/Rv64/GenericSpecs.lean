/-
  EvmAsm.Rv64.GenericSpecs

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

-- `CPSSpec` transitively imports `Basic`, `SepLogic`, `Execution`, and
-- (via `Execution`) `Instructions`.
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64

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
theorem generic_1reg_spec_within (instr : Instr) (rd : Reg) (v result : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (hexec : ∀ s, s.pc = base → s.getReg rd = v →
      execInstrBr s instr = (s.setReg rd result).setPC (s.pc + 4))
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base instr)
      (rd ↦ᵣ v)
      (rd ↦ᵣ result) := by
  intro R hR s hcr hPR hpc; subst hpc
  -- Extract code fetch from CodeReq
  have hfetch : s.code s.pc = some instr :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrd : s.getReg rd = v :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  -- Compute next state
  have hexec' := hexec s rfl hrd
  have hstep' := hstep s hfetch
  -- Witness: 1 step
  refine ⟨1, Nat.le_refl 1, (s.setReg rd result).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · -- stepN 1 s = some nextState
    show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Postcondition
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h1

-- ============================================================================
-- Group 2: Two registers, rd ≠ rs1 (rs1 preserved, rd updated)
-- Used for: ADDI, ANDI, SLTIU (rd ≠ rs1), SUB rd=rs2, MV, ADDI gen
-- ============================================================================

/-- Generic spec for instructions with two distinct registers (rs source, rd dest).
    Pre:  (rs ↦ᵣ v_src) ** (rd ↦ᵣ vOld)
    Post: (rs ↦ᵣ v_src) ** (rd ↦ᵣ result) -/
theorem generic_2reg_spec_within (instr : Instr) (rs rd : Reg)
    (v_src vOld result : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (hexec : ∀ s, s.pc = base → s.getReg rs = v_src → s.getReg rd = vOld →
      execInstrBr s instr = (s.setReg rd result).setPC (s.pc + 4))
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base instr)
      ((rs ↦ᵣ v_src) ** (rd ↦ᵣ vOld))
      ((rs ↦ᵣ v_src) ** (rd ↦ᵣ result)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some instr :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs : s.getReg rs = v_src :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrd : s.getReg rd = vOld :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hexec' := hexec s rfl hrs hrd
  have hstep' := hstep s hfetch
  refine ⟨1, Nat.le_refl 1, (s.setReg rd result).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 2) to front
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    -- h1 : (rd ** (rs ** R))
    have h2 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h3

-- ============================================================================
-- Group 3: Two registers, rd = rs1 (rd updated, rs2 preserved)
-- Used for: ADD rd=rs1, SUB rd=rs1, AND/OR/XOR/SLTU/SRL/SLL rd=rs1
-- ============================================================================

/-- Generic spec for ALU instructions where rd = rs1 (2 registers: rd, rs2).
    Pre:  (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    Post: (rd ↦ᵣ result) ** (rs2 ↦ᵣ v2) -/
theorem generic_2reg_rd_eq_rs1_spec_within (instr : Instr) (rd rs2 : Reg)
    (v1 v2 result : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (hexec : ∀ s, s.pc = base → s.getReg rd = v1 → s.getReg rs2 = v2 →
      execInstrBr s instr = (s.setReg rd result).setPC (s.pc + 4))
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base instr)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ result) ** (rs2 ↦ᵣ v2)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some instr :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrd : s.getReg rd = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hexec' := hexec s rfl hrd hrs2
  have hstep' := hstep s hfetch
  refine ⟨1, Nat.le_refl 1, (s.setReg rd result).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 1) to front, assoc then update
    have h1a := holdsFor_sepConj_assoc.mp hPR
    -- h1a : (rd ** (rs2 ** R))
    have h2 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 h1a
    -- Rearrange back: (rd' ** (rs2 ** R)) → ((rd' ** rs2) ** R)
    have h3 := holdsFor_sepConj_assoc.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h3

-- ============================================================================
-- Group 4: Three distinct registers (rs1, rs2 preserved, rd updated)
-- Used for: ADD, SUB, AND, OR, XOR, SLTU (all distinct)
-- ============================================================================

/-- Generic spec for ALU instructions with 3 distinct registers.
    Pre:  (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld)
    Post: (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ result) -/
theorem generic_3reg_spec_within (instr : Instr) (rs1 rs2 rd : Reg)
    (v1 v2 vOld result : Word) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (hexec : ∀ s, s.pc = base → s.getReg rs1 = v1 → s.getReg rs2 = v2 →
      execInstrBr s instr = (s.setReg rd result).setPC (s.pc + 4))
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base instr)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ result)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some instr :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hexec' := hexec s rfl hrs1 hrs2
  have hstep' := hstep s hfetch
  refine ⟨1, Nat.le_refl 1, (s.setReg rd result).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 3 in inner) to front: 2 pull_seconds
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    -- h2 : (rd ** (rs2 ** (rs1 ** R)))
    have h3 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h5

-- ============================================================================
-- Group 5: NOP-like (just PC advance, no register/memory changes)
-- Used for: NOP, FENCE, JAL x0
-- ============================================================================

/-- Generic spec for instructions that only advance PC without changing state.
    Pre/Post: empAssertion  [frame handles the rest] -/
theorem generic_nop_spec_within (instr : Instr) {base exit_ : Word}
    (hexec : ∀ s, s.pc = base → execInstrBr s instr = s.setPC exit_)
    (hstep : ∀ s, s.code s.pc = some instr → step s = some (execInstrBr s instr)) :
    cpsTripleWithin 1 base exit_ (CodeReq.singleton base instr)
      empAssertion
      empAssertion := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some instr :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hexec' := hexec s rfl
  have hstep' := hstep s hfetch
  refine ⟨1, Nat.le_refl 1, s.setPC exit_, ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree_emp hR) hPR

-- NOTE: LW/SW generic specs omitted for RV64.
-- In RV64, LW uses getWord32 + signExtend and SW uses setWord32 + truncate,
-- which don't match the 64-bit separation logic memory model (getMem/setMem).
-- EVM64 operations use LD/SD exclusively (Groups 11-12 below).

-- ============================================================================
-- Group 9: Branch (BNE/BEQ) — bounded two-exit CPS specs
-- ============================================================================

/-- Generic spec for BNE: branch if not equal.
    Pre:  (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    Taken (v1 ≠ v2): PC = base + signExtend13 offset, post includes ⌜v1 ≠ v2⌝
    Not taken (v1 = v2): PC = base + 4, post includes ⌜v1 = v2⌝ -/
theorem generic_bne_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BNE rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (base + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BNE rs1 rs2 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BNE rs1 rs2 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  -- Case split on v1 = v2
  by_cases heq : v1 = v2
  · -- Not taken: v1 = v2
    have hexec' : execInstrBr s (.BNE rs1 rs2 offset) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1, hrs2, heq, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · -- Add pure assertion ⌜v1 = v2⌝
      have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, heq⟩⟩, hR2⟩
  · -- Taken: v1 ≠ v2
    have hexec' : execInstrBr s (.BNE rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
      simp only [execInstrBr, hrs1, hrs2, bne_iff_ne, ne_eq, heq, not_false_eq_true, ite_true]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, heq⟩⟩, hR2⟩

/-- Generic spec for BEQ: branch if equal. -/
theorem generic_beq_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (base + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 rs2 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 rs2 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  by_cases heq : v1 = v2
  · -- Taken: v1 = v2
    have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
      simp only [execInstrBr, hrs1, hrs2, heq, beq_self_eq_true, ite_true]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, heq⟩⟩, hR2⟩
  · -- Not taken: v1 ≠ v2
    have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1, hrs2, beq_iff_eq, heq, ite_false]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, heq⟩⟩, hR2⟩

-- ============================================================================
-- Group 9b: Branch (BLTU) — bounded two-exit CPS specs (unsigned less than)
-- ============================================================================

/-- Generic spec for BLTU: branch if unsigned less than.
    Taken (ult v1 v2): PC = base + signExtend13 offset
    Not taken (¬ult v1 v2): PC = base + 4 -/
theorem generic_bltu_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BLTU rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.ult v1 v2⌝)
      (base + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.ult v1 v2⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BLTU rs1 rs2 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BLTU rs1 rs2 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  by_cases hlt : BitVec.ult v1 v2
  · -- Taken: v1 <u v2
    have hexec' : execInstrBr s (.BLTU rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
      simp [execInstrBr, hrs1, hrs2, hlt]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, hlt⟩⟩, hR2⟩
  · -- Not taken: ¬(v1 <u v2)
    have hexec' : execInstrBr s (.BLTU rs1 rs2 offset) = s.setPC (s.pc + 4) := by
      simp [execInstrBr, hrs1, hrs2, hlt]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, hlt⟩⟩, hR2⟩

-- ============================================================================
-- Group 9c: Branch (BGE) — bounded two-exit CPS specs (signed greater or equal)
-- ============================================================================

/-- Generic spec for BGE: branch if signed greater or equal.
    Taken (¬slt v1 v2): PC = base + signExtend13 offset
    Not taken (slt v1 v2): PC = base + 4 -/
theorem generic_bge_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BGE rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.slt v1 v2⌝)
      (base + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.slt v1 v2⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BGE rs1 rs2 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BGE rs1 rs2 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  by_cases hlt : BitVec.slt v1 v2
  · -- Not taken: slt v1 v2 → ¬(¬slt), so BGE falls through
    have hexec' : execInstrBr s (.BGE rs1 rs2 offset) = s.setPC (s.pc + 4) := by
      simp [execInstrBr, hrs1, hrs2, hlt]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, hlt⟩⟩, hR2⟩
  · -- Taken: ¬slt v1 v2 → BGE branches
    have hexec' : execInstrBr s (.BGE rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
      simp [execInstrBr, hrs1, hrs2, hlt]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, hlt⟩⟩, hR2⟩

-- ============================================================================
-- Group 9d: Branch (BLT) — bounded two-exit CPS specs (signed less than)
-- ============================================================================

/-- Generic spec for BLT: branch if signed less than.
    Taken (slt v1 v2): PC = base + signExtend13 offset
    Not taken (¬slt v1 v2): PC = base + 4 -/
theorem generic_blt_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BLT rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.slt v1 v2⌝)
      (base + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.slt v1 v2⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BLT rs1 rs2 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BLT rs1 rs2 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  by_cases hlt : BitVec.slt v1 v2
  · -- Taken: slt v1 v2
    have hexec' : execInstrBr s (.BLT rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
      simp [execInstrBr, hrs1, hrs2, hlt]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, hlt⟩⟩, hR2⟩
  · -- Not taken: ¬slt v1 v2
    have hexec' : execInstrBr s (.BLT rs1 rs2 offset) = s.setPC (s.pc + 4) := by
      simp [execInstrBr, hrs1, hrs2, hlt]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, hlt⟩⟩, hR2⟩

-- ============================================================================
-- Group 9e: Branch (BGEU) — bounded two-exit CPS specs (unsigned greater or equal)
-- ============================================================================

/-- Generic spec for BGEU: branch if unsigned greater or equal.
    Taken (¬ult v1 v2): PC = base + signExtend13 offset
    Not taken (ult v1 v2): PC = base + 4 -/
theorem generic_bgeu_spec_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BGEU rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (base + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.ult v1 v2⌝)
      (base + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.ult v1 v2⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BGEU rs1 rs2 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BGEU rs1 rs2 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  by_cases hlt : BitVec.ult v1 v2
  · -- Not taken: ult v1 v2 → ¬(¬ult), so BGEU falls through
    have hexec' : execInstrBr s (.BGEU rs1 rs2 offset) = s.setPC (s.pc + 4) := by
      simp [execInstrBr, hrs1, hrs2, hlt]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, hlt⟩⟩, hR2⟩
  · -- Taken: ¬ult v1 v2 → BGEU branches
    have hexec' : execInstrBr s (.BGEU rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
      simp [execInstrBr, hrs1, hrs2, hlt]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : (((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R).pcFree :=
        pcFree_sepConj (by pcFree) hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR'
      obtain ⟨h1a, h1b, hd1, hu1, hRs1, hRs2⟩ := hP1
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨h1a, h1b, hd1, hu1, hRs1,
         (sepConj_pure_right h1b).mpr ⟨hRs2, hlt⟩⟩, hR2⟩

-- ============================================================================
-- Group 10: JAL (jump and link)
-- ============================================================================

/-- Generic spec for JAL: rd := PC + 4, PC := PC + sext(offset).
    Pre:  (rd ↦ᵣ vOld)
    Post: (rd ↦ᵣ (base + 4)) -/
theorem generic_jal_spec_within (rd : Reg) (vOld : Word) (offset : BitVec 21) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + signExtend21 offset) (CodeReq.singleton base (.JAL rd offset))
      (rd ↦ᵣ vOld)
      (rd ↦ᵣ (base + 4)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JAL rd offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hstep' : step s = some (execInstrBr s (.JAL rd offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  -- execInstrBr s (.JAL rd offset) = (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 offset)
  refine ⟨1, Nat.le_refl 1, (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 offset), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep']; rfl
  · have h1 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h1

/-- Generic spec for JALR: rd := PC + 4, PC := (rs1 + sext(offset)) & ~1.
    Pre:  (rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld)
    Post: (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4)) -/
theorem generic_jalr_spec_within (rd rs1 : Reg) (v1 vOld : Word) (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base ((v1 + signExtend12 offset) &&& ~~~1) (CodeReq.singleton base (.JALR rd rs1 offset))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JALR rd rs1 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.JALR rd rs1 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.JALR rd rs1 offset) =
      (s.setReg rd (s.pc + 4)).setPC ((v1 + signExtend12 offset) &&& ~~~1) := by
    simp only [execInstrBr, hrs1]; rfl
  refine ⟨1, Nat.le_refl 1, (s.setReg rd (s.pc + 4)).setPC ((v1 + signExtend12 offset) &&& ~~~1), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 2) to front
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    -- h1 : (rd ** (rs1 ** R))
    have h2 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4) hrd_ne_x0 h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h3

-- ============================================================================
-- Group 11: LD (doubleword memory load)
-- ============================================================================

/-- Generic spec for LD: load doubleword from memory.
    Pre:  (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (addr ↦ₘ memVal)
    Post: (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ memVal) ** (addr ↦ₘ memVal)
    where addr = v_addr + signExtend12 offset -/
theorem generic_ld_spec_within (rd rs1 : Reg) (v_addr vOld memVal : Word)
    (offset : BitVec 12) (base : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LD rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** ((v_addr + signExtend12 offset) ↦ₘ memVal))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ memVal) ** ((v_addr + signExtend12 offset) ↦ₘ memVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LD rd rs1 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem_piece := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem (v_addr + signExtend12 offset) = memVal :=
    holdsFor_memIs_getMem hmem_piece
  have hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true :=
    holdsFor_memIs_isValidDwordAccess hmem_piece
  -- Step proof using step_ld
  have hstep' : step s = some (execInstrBr s (.LD rd rs1 offset)) :=
    step_ld hfetch (hrs1 ▸ hvalid)
  -- execInstrBr s (.LD rd rs1 offset) = (s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 offset))).setPC (s.pc + 4)
  have hexec' : execInstrBr s (.LD rd rs1 offset) = (s.setReg rd memVal).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd memVal).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull rd (position 2) to front: 1 pull_second + assoc
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    -- h1 : ((rd ** mem) ** (rs1 ** R))
    -- Need to separate rd from mem first
    have h1a := holdsFor_sepConj_assoc.mp h1
    -- h1a : (rd ** (mem ** (rs1 ** R)))
    have h2 := holdsFor_sepConj_regIs_setReg (v' := memVal) hrd_ne_x0 h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h4

-- ============================================================================
-- Group 12: SD (doubleword memory store)
-- ============================================================================

/-- Generic spec for SD: store doubleword to memory.
    Pre:  (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ memOld)
    Post: (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data)
    where addr = v_addr + signExtend12 offset -/
theorem generic_sd_spec_within (rs1 rs2 : Reg) (v_addr v_data memOld : Word)
    (offset : BitVec 12) (base : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ memOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SD rs1 rs2 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true :=
    holdsFor_memIs_isValidDwordAccess (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  -- Step proof using step_sd
  have hstep' : step s = some (execInstrBr s (.SD rs1 rs2 offset)) :=
    step_sd hfetch (hrs1 ▸ hvalid)
  -- execInstrBr: setMem then setPC
  have hexec' : execInstrBr s (.SD rs1 rs2 offset) =
      (s.setMem (v_addr + signExtend12 offset) v_data).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2]
  refine ⟨1, Nat.le_refl 1, (s.setMem (v_addr + signExtend12 offset) v_data).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · -- Pull mem (position 3) to front: 2 pull_seconds
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    -- h2 : (mem ** (rs2 ** (rs1 ** R)))
    have h3 := holdsFor_sepConj_memIs_setMem (v' := v_data) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h5

-- ============================================================================
-- Group 8: SD with x0 (stores 0, no x0 register in pre/post)
-- ============================================================================

/-- Generic spec for SD with rs2 = x0: store 0 to memory.
    Pre:  (rs1 ↦ᵣ v_addr) ** (addr ↦ₘ memOld)
    Post: (rs1 ↦ᵣ v_addr) ** (addr ↦ₘ 0) -/
theorem generic_sd_x0_spec_within (rs1 : Reg) (v_addr memOld : Word)
    (offset : BitVec 12) (base : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.SD rs1 .x0 offset))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ memOld))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ (0 : Word))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SD rs1 .x0 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true :=
    holdsFor_memIs_isValidDwordAccess (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.SD rs1 .x0 offset)) :=
    step_sd hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.SD rs1 .x0 offset) =
      (s.setMem (v_addr + signExtend12 offset) 0).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1]; rfl
  refine ⟨1, Nat.le_refl 1, (s.setMem (v_addr + signExtend12 offset) 0).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_memIs_setMem (v' := (0 : Word)) h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h3

-- ============================================================================
-- Compatibility wrappers: forget the explicit step bound.
-- ============================================================================
end EvmAsm.Rv64
