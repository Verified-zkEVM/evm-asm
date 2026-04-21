/-
  EvmAsm.Rv64.ControlFlow

  Control flow macros using branch and jump instructions, with CPS-style
  specifications.  (64-bit RISC-V port)

  This module provides:
  - if_eq: a conditional macro (if rs1 = rs2 then ... else ...)
  - CPS specifications for the macro
  - Concrete examples verified by decide
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.Tactics.SpecDb

namespace EvmAsm.Rv64

-- ============================================================================
-- if_eq macro
-- ============================================================================

/-- Conditional macro: if rs1 = rs2 then then_body else else_body.

    Code layout (addresses relative to base):
      base:              BNE rs1 rs2 else_offset    -- to else if ≠
      base+4:            <then_body>                 -- t instructions
      base+4+4t:         JAL x0 end_offset           -- skip else
      base+4+4t+4:       <else_body>                 -- e instructions
      base+4+4t+4+4e:    (exit point)               -- merged exit

    Offsets:
      else_offset = 4*(t+1)+4  (skip then_body + JAL, in bytes)
      end_offset  = 4*e+4      (skip else_body, in bytes)        -/
def if_eq (rs1 rs2 : Reg) (then_body else_body : Program) : Program :=
  let t := then_body.length
  let e := else_body.length
  let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (t + 1) + 4)
  let end_off  : BitVec 21 := BitVec.ofNat 21 (4 * e + 4)
  let bne : Program := [Instr.BNE rs1 rs2 else_off]
  let jal : Program := [Instr.JAL .x0 end_off]
  bne ++ then_body ++ jal ++ else_body

-- ============================================================================
-- Concrete examples
-- ============================================================================

/-- Concrete example: if x10 = x11 then x12 := 1 else x12 := 0 -/
def if_eq_example : Program :=
  if_eq .x10 .x11
    [Instr.LI .x12 1]      -- then: x12 := 1
    [Instr.LI .x12 0]      -- else: x12 := 0

/-- A test state for the if_eq example. -/
def mkTestState (x10val x11val : Word) (pc : Word := 0) : MachineState where
  regs := fun r =>
    match r with
    | .x10 => x10val
    | .x11 => x11val
    | _    => 0
  mem := fun _ => 0
  pc := pc

-- ============================================================================
-- Testing via step-based execution
-- ============================================================================

/-- Execute the if_eq_example program using step-based execution.
    We load the program at address 0 and run stepN. -/
def runIfEqExample (x10val x11val : Word) (steps : Nat) : Option MachineState :=
  let s := { mkTestState x10val x11val with code := loadProgram 0 if_eq_example }
  stepN steps s

-- When x10 = x11 = 42: BNE not taken → LI x12 1 → JAL (skip else)
-- Program: [BNE, LI 1, JAL, LI 0]  (4 instructions)
-- Equal case: BNE(not taken) → PC=4, LI x12 1 → PC=8, JAL x0 8 → PC=16
-- That's 3 steps to reach exit at PC=16

/-- When x10 = x11 = 42, after 3 steps x12 should be 1. -/
example : (runIfEqExample 42 42 3).bind (fun s => some (s.getReg .x12)) = some 1 := by
  decide

/-- When x10 = x11 = 42, after 3 steps PC should be at exit (16). -/
example : (runIfEqExample 42 42 3).bind (fun s => some s.pc) = some 16 := by
  decide

-- Unequal case: BNE(taken, offset=4*(1+1)+4=12) → PC=12, LI x12 0 → PC=16
-- That's 2 steps to reach exit at PC=16

/-- When x10 = 42, x11 = 99, after 2 steps x12 should be 0. -/
example : (runIfEqExample 42 99 2).bind (fun s => some (s.getReg .x12)) = some 0 := by
  decide

/-- When x10 = 42, x11 = 99, after 2 steps PC should be at exit (16). -/
example : (runIfEqExample 42 99 2).bind (fun s => some s.pc) = some 16 := by
  decide

-- ============================================================================
-- Additional examples: larger bodies
-- ============================================================================

/-- A more complex if_eq: if x10 = x11 then x12 := x10 + x11 else x12 := x10 - x11 -/
def if_eq_arith : Program :=
  if_eq .x10 .x11
    [Instr.ADD .x12 .x10 .x11]     -- then: x12 := x10 + x11
    [Instr.SUB .x12 .x10 .x11]     -- else: x12 := x10 - x11

def runIfEqArith (x10val x11val : Word) (steps : Nat) : Option MachineState :=
  let s := { mkTestState x10val x11val with code := loadProgram 0 if_eq_arith }
  stepN steps s

/-- When x10 = x11 = 5: takes then-branch, x12 := 5 + 5 = 10. -/
example : (runIfEqArith 5 5 3).bind (fun s => some (s.getReg .x12)) = some 10 := by
  decide

/-- When x10 = 10, x11 = 3: takes else-branch, x12 := 10 - 3 = 7. -/
example : (runIfEqArith 10 3 2).bind (fun s => some (s.getReg .x12)) = some 7 := by
  decide

-- ============================================================================
-- Helper lemmas for symbolic proofs
-- ============================================================================

/-- A predicate on MachineState is PC-independent: it holds regardless of the PC value. -/
def pcIndep (P : MachineState → Prop) : Prop := ∀ s v, P s → P (s.setPC v)

theorem pcIndep_and {P Q : MachineState → Prop} (hP : pcIndep P) (hQ : pcIndep Q) :
    pcIndep (fun s => P s ∧ Q s) := by
  intro s v ⟨hp, hq⟩
  exact ⟨hP s v hp, hQ s v hq⟩

theorem pcIndep_holdsFor_regIs {r : Reg} {val : Word} :
    pcIndep (regIs r val).holdsFor := by
  intro s v h
  simp only [holdsFor_regIs, MachineState.getReg_setPC] at *; exact h

theorem pcIndep_holdsFor_memIs {a : Word} {val : Word} :
    pcIndep (memIs a val).holdsFor := by
  intro s v h
  simp only [holdsFor_memIs, MachineState.getMem, MachineState.setPC] at *; exact h

theorem pcIndep_committedIs {vals : List (Word × Word)} :
    pcIndep (MachineState.committedIs vals) := by
  intro s v h
  simp only [MachineState.committedIs, MachineState.committed_setPC] at *; exact h

theorem pcIndep_publicValuesIs {vals : List (BitVec 8)} :
    pcIndep (MachineState.publicValuesIs vals) := by
  intro s v h
  simp only [MachineState.publicValuesIs, MachineState.publicValues_setPC] at *; exact h

theorem pcIndep_privateInputIs {vals : List (BitVec 8)} :
    pcIndep (MachineState.privateInputIs vals) := by
  intro s v h
  simp only [MachineState.privateInputIs, MachineState.privateInput_setPC] at *; exact h

theorem pcIndep_holdsFor_sepConj {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    pcIndep ((P ** Q).holdsFor) := by
  intro s v ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
  refine ⟨h, ?_, h1, h2, hd, hunion, hp1, hp2⟩
  have hpc_none := pcFree_sepConj hP hQ h ⟨h1, h2, hd, hunion, hp1, hp2⟩
  rw [← hunion] at hpc_none hcompat ⊢
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r' v' hv => by rw [MachineState.getReg_setPC]; exact hr r' v' hv,
         fun a' v' hv => by simp [MachineState.getMem, MachineState.setPC]; exact hm a' v' hv,
         fun a' i' hv => by rw [MachineState.code_setPC]; exact hc a' i' hv,
         fun v' hv => by rw [hpc_none] at hv; simp at hv,
         fun v' hv => by simp [MachineState.setPC] at *; exact hpv v' hv,
         fun v' hv => by simp [MachineState.setPC] at *; exact hpi v' hv⟩

/-- Sign-extend a small 13-bit value (MSB clear) to 64 bits. -/
theorem signExtend13_ofNat_small {n : Nat} (h : n < 2^12) :
    signExtend13 (BitVec.ofNat 13 n) = BitVec.ofNat 64 n := by
  unfold signExtend13
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

/-- Sign-extend a small 21-bit value (MSB clear) to 64 bits. -/
theorem signExtend21_ofNat_small {n : Nat} (h : n < 2^20) :
    signExtend21 (BitVec.ofNat 21 n) = BitVec.ofNat 64 n := by
  unfold signExtend21
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

/-- Load the first instruction from a program at its base address. -/
theorem loadProgram_at_base (base : Word) (instr : Instr) (rest : List Instr) :
    loadProgram base (instr :: rest) base = some instr := by
  simp [loadProgram, BitVec.sub_self]

/-- Load instruction k from a program at address base + 4*k. -/
theorem loadProgram_at_index (base : Word) (prog : List Instr) (k : Nat)
    (hk : k < prog.length) (h4k : 4 * k < 2^64) :
    loadProgram base prog (base + BitVec.ofNat 64 (4 * k)) = prog[k]? := by
  simp [loadProgram]
  have hbase := base.isLt
  have : (18446744073709551616 - BitVec.toNat base + (BitVec.toNat base + 4 * k)) % 18446744073709551616
       = 4 * k := by omega
  rw [this]; simp [hk]; omega

/-- The length of an if_eq program. -/
theorem if_eq_length (rs1 rs2 : Reg) (tb eb : Program) :
    (if_eq rs1 rs2 tb eb).length = tb.length + eb.length + 2 := by
  simp only [if_eq, Program.length_append, List.length_cons, List.length_nil]; omega

/-- JAL x0 executes as a pure PC update (x0 write is dropped). -/
theorem execInstrBr_jal_x0 (s : MachineState) (off : BitVec 21) :
    execInstrBr s (Instr.JAL .x0 off) = s.setPC (s.pc + signExtend21 off) := by
  simp [execInstrBr, MachineState.setReg, MachineState.setPC]

/-- JAL x0 spec for any code memory: pure PC jump, no register/memory changes.
    Since x0 writes are dropped, JAL x0 just updates PC. -/
@[spec_gen_rv64] theorem jal_x0_spec_gen (offset : BitVec 21) (addr : Word) :
    cpsTriple addr (addr + signExtend21 offset)
      (CodeReq.singleton addr (.JAL .x0 offset))
      empAssertion
      empAssertion :=
  generic_nop_spec (.JAL .x0 offset) addr (addr + signExtend21 offset)
    (by intro s hpc; simp [execInstrBr, MachineState.setReg, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s hfetch (by nofun) (by nofun) (by rfl))

/-- JALR x0 executes as a pure PC update (x0 write is dropped). -/
theorem execInstrBr_jalr_x0 (s : MachineState) (rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (Instr.JALR .x0 rs1 off) = s.setPC ((s.getReg rs1 + signExtend12 off) &&& ~~~1) := by
  simp [execInstrBr, MachineState.setReg, MachineState.setPC]

/-- JALR x0 spec: pure PC jump to (rs1 + sext(offset)) & ~1, no register changes. -/
@[spec_gen_rv64] theorem jalr_x0_spec_gen (rs1 : Reg) (v : Word)
    (offset : BitVec 12) (addr : Word) :
    cpsTriple addr ((v + signExtend12 offset) &&& ~~~1)
      (CodeReq.singleton addr (.JALR .x0 rs1 offset))
      (rs1 ↦ᵣ v)
      (rs1 ↦ᵣ v) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JALR .x0 rs1 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  have hexec : execInstrBr s (.JALR .x0 rs1 offset) = s.setPC ((v + signExtend12 offset) &&& ~~~1) := by
    rw [execInstrBr_jalr_x0, hrs1]
  have hstep : step s = some (execInstrBr s (.JALR .x0 rs1 offset)) :=
    step_non_ecall_non_mem s hfetch (by nofun) (by nofun) (by rfl)
  refine ⟨1, s.setPC ((v + signExtend12 offset) &&& ~~~1), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep, hexec]; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) hPR

-- ============================================================================
-- CPS specification for if_eq
-- ============================================================================

/-- Helper: add a true pure assertion to the right of an aAnd chain.
    If P holds on h and prop is true, then (P ⋒ ⌜prop⌝) holds on h. -/
private theorem aAnd_pure_right_of_true {P : Assertion} {prop : Prop}
    (hprop : prop) : ∀ h, P h → (P ⋒ ⌜prop⌝) h := by
  intro h hp
  exact ⟨h, PartialState.empty, ⟨fun _ _ _ _ h2 => by simp [PartialState.empty] at h2,
    fun _ _ _ _ h2 => by simp [PartialState.empty] at h2,
    fun _ _ _ _ h2 => by simp [PartialState.empty] at h2,
    fun _ _ _ h2 => by simp [PartialState.empty] at h2,
    fun _ _ _ h2 => by simp [PartialState.empty] at h2,
    fun _ _ _ h2 => by simp [PartialState.empty] at h2⟩,
    PartialState.union_empty_right, hp, rfl, hprop⟩

/-- The if_eq macro satisfies a cpsBranch spec: it either goes to
    the then-body entry (base+4) with equality, or to the else-body
    entry (base+4+4*t+4) with inequality, in exactly one step.

    Uses additive conjunction (⊓) so rs1 and rs2 may be the same register.
    BNE only modifies PC, so all assertions are preserved through setPC.
    The branch condition is encoded as a pure assertion on v1, v2.

    Requires instrAt for the BNE instruction at base. -/
theorem if_eq_branch_step (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body : Program)
    (base : Word) (P : Assertion)
    (hP : P.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12) :
    let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)
    let bneInstr := Instr.BNE rs1 rs2 else_off
    let thenEntry := base + 4
    let elseEntry := base + 4 + BitVec.ofNat 64 (4 * then_body.length) + 4
    let pre := (base ↦ᵢ bneInstr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))
    cpsBranch base CodeReq.empty pre
      thenEntry ((base ↦ᵢ bneInstr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝))
      elseEntry ((base ↦ᵢ bneInstr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝)) := by
  simp only
  intro R hR s _hcr hPR hpc; subst hpc
  -- Extract instrAt from the precondition
  have hfetch : s.code s.pc = some (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) :=
    holdsFor_instrAt.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  -- Extract register values from the aAnd part
  have haAnd := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (aAnd_holdsFor_elim (aAnd_holdsFor_elim haAnd).2).1
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (aAnd_holdsFor_elim (aAnd_holdsFor_elim haAnd).2).2
  -- Execute the BNE instruction
  have hstep' : step s = some (execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)))) :=
    step_non_ecall_non_mem s hfetch (by nofun) (by nofun) (by rfl)
  -- The entire precondition (P ** R form from cpsBranch) is pcFree
  have hpcfree : (((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))) ** R).pcFree :=
    pcFree_sepConj (pcFree_sepConj pcFree_instrAt (pcFree_aAnd hP (pcFree_aAnd pcFree_regIs pcFree_regIs))) hR
  -- Case split on v1 = v2
  by_cases heq : v1 = v2
  · -- Not taken: v1 = v2 → PC = s.pc + 4 = thenEntry (exit_t)
    have hexec' : execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1, hrs2, heq, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
    refine ⟨1, s.setPC (s.pc + 4), ?_, Or.inl ⟨by simp [MachineState.setPC], ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · -- Preserve assertions through setPC and add ⌜v1 = v2⌝
      have hPR' := holdsFor_pcFree_setPC hpcfree (v := s.pc + 4) hPR
      -- Strengthen the aAnd part: add ⌜v1 = v2⌝ to inner sepConj
      obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨ha, hb, hda, hua, hinstr, haand⟩, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨ha, hb, hda, hua, hinstr, aAnd_mono_right (aAnd_mono_right (aAnd_pure_right_of_true heq)) hb haand⟩, hR2⟩
  · -- Taken: v1 ≠ v2 → PC = s.pc + signExtend13(else_off) = elseEntry (exit_f)
    have hexec' : execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) =
        s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) := by
      simp only [execInstrBr, hrs1, hrs2, bne_iff_ne, ne_eq, heq, not_false_eq_true, ite_true]
    -- Show that signExtend13(else_off) = 4*(t+1)+4
    have hse : signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)) =
        BitVec.ofNat 64 (4 * (then_body.length + 1) + 4) :=
      signExtend13_ofNat_small ht_small
    -- Show that s.pc + 4*(t+1)+4 = s.pc + 4 + 4*t + 4
    have haddr : s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)) =
        s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length) + 4 := by
      rw [hse]; bv_omega
    refine ⟨1, s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))), ?_,
      Or.inr ⟨by simp [MachineState.setPC]; exact haddr, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · -- Preserve assertions through setPC and add ⌜v1 ≠ v2⌝
      have hPR' := holdsFor_pcFree_setPC hpcfree
        (v := s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨ha, hb, hda, hua, hinstr, haand⟩, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨ha, hb, hda, hua, hinstr, aAnd_mono_right (aAnd_mono_right (aAnd_pure_right_of_true heq)) hb haand⟩, hR2⟩

/-- Full CPS specification for if_eq: given that the then-body is correct
    under equality and the else-body is correct under inequality,
    the whole if_eq is a cpsTriple from entry to exit.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register.

    Requires instrAt for both the BNE at base and the JAL at thenExit. -/
theorem if_eq_spec (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Word) (P Q : Assertion)
    (hP : P.pcFree) (hQ : Q.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12)
    (he_small : 4 * (else_body.length) + 4 < 2^20) :
    let prog := if_eq rs1 rs2 then_body else_body
    let exit_ := base + BitVec.ofNat 64 (4 * prog.length)
    let thenEntry := base + 4
    let thenExit  := base + 4 + BitVec.ofNat 64 (4 * then_body.length)
    let elseEntry := thenExit + 4
    let elseExit  := exit_
    let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)
    let end_off  : BitVec 21 := BitVec.ofNat 21 (4 * else_body.length + 4)
    let bneInstr := Instr.BNE rs1 rs2 else_off
    let jalInstr := Instr.JAL .x0 end_off
    let pre := (base ↦ᵢ bneInstr) ** (thenExit ↦ᵢ jalInstr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))
    (cpsTriple thenEntry thenExit CodeReq.empty
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) Q) →
    (cpsTriple elseEntry elseExit CodeReq.empty
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) Q) →
    cpsTriple base exit_ CodeReq.empty pre Q := by
  simp only
  intro hthen helse R hR s _hcr hPR hpc; subst hpc
  -- hPR : ((bne ** (jal ** aAnd)) ** R).holdsFor s
  -- Extract instrAt facts
  have hfetch_bne : s.code s.pc = some (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) :=
    holdsFor_instrAt.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  -- Extract register values from the aAnd part
  have haAnd := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (aAnd_holdsFor_elim (aAnd_holdsFor_elim haAnd).2).1
  have hrs2 : s.getReg rs2 = v2 :=
    holdsFor_regIs.mp (aAnd_holdsFor_elim (aAnd_holdsFor_elim haAnd).2).2
  -- Execute BNE
  have hstep' : step s = some (execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)))) :=
    step_non_ecall_non_mem s hfetch_bne (by nofun) (by nofun) (by rfl)
  -- pcFree for the full precondition with frame
  have hpcfree_all : (((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
      ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))) ** R).pcFree :=
    pcFree_sepConj (pcFree_sepConj pcFree_instrAt
      (pcFree_sepConj pcFree_instrAt
        (pcFree_aAnd hP (pcFree_aAnd pcFree_regIs pcFree_regIs)))) hR
  -- Body-triple frame: bne ** jal ** R (pcFree)
  have hframe_pcfree : ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
      ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R).pcFree :=
    pcFree_sepConj pcFree_instrAt (pcFree_sepConj pcFree_instrAt hR)
  -- Helper: rearranging ** chains
  -- (bne ** (jal ** aand)) ** R = (aand ** (bne ** (jal ** R))) as assertions
  have hassert_perm : (((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
      ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))) ** R) =
    ((P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)) **
      ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
       ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)) := by
    funext h; exact propext ⟨fun hp => by sep_perm hp, fun hp => by sep_perm hp⟩
  -- Case split on v1 = v2
  by_cases heq : v1 = v2
  · -- BNE not taken: v1 = v2, PC -> s.pc + 4 = thenEntry
    have hexec' : execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1, hrs2, heq, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
    -- After BNE: all pcFree assertions preserved
    have hPR1 := holdsFor_pcFree_setPC hpcfree_all (v := s.pc + 4) hPR
    -- Rearrange to (aand ** (bne ** jal ** R)), then strengthen aand with ⌜v1 = v2⌝
    have hPR1' : ((P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
         ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)).holdsFor
          (s.setPC (s.pc + 4)) := by
      obtain ⟨hp, hcompat, hpq⟩ := hPR1
      rw [hassert_perm] at hpq
      obtain ⟨h1', h2', hd', hu', haand_h, hframe_h⟩ := hpq
      exact ⟨hp, hcompat, h1', h2', hd', hu',
        aAnd_mono_right (aAnd_mono_right (aAnd_pure_right_of_true heq)) h1' haand_h, hframe_h⟩
    -- Apply then-body triple
    obtain ⟨k2, s2, hstep2, hpc2, hQR2⟩ := hthen _ hframe_pcfree
      (s.setPC (s.pc + 4)) (CodeReq.empty_satisfiedBy _) hPR1' rfl
    -- hQR2 : (Q ** (bne ** jal ** R)).holdsFor s2 at s2.pc = thenExit
    -- Rearrange for JAL: (Q ** (bne ** (jal ** R))) -> (jal ** (bne ** Q ** R))
    have hassert_perm2 :
      (Q ** ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
           ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)) =
      (((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) ** Q ** R)) := by
      funext h; exact propext ⟨fun hp => by sep_perm hp, fun hp => by sep_perm hp⟩
    have hQR2' : (((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) ** Q ** R)).holdsFor s2 := by
      obtain ⟨hp, hcompat, hpq⟩ := hQR2
      exact ⟨hp, hcompat, hassert_perm2 ▸ hpq⟩
    -- Apply JAL spec
    -- Frame for jal_x0_spec_gen: the full (jal ** bne ** Q ** R) conjunction
    have hjal_pcfree : (((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) ** Q ** R)).pcFree :=
      pcFree_sepConj pcFree_instrAt (pcFree_sepConj pcFree_instrAt (pcFree_sepConj hQ hR))
    have hjal_cr : (CodeReq.singleton (s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length))
        (Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4)))).SatisfiedBy s2 :=
      instrAt_singleton_satisfiedBy _ _ _ (holdsFor_sepConj_elim_left hQR2')
    -- Convert hQR2' for jal_x0_spec_gen (empAssertion pre/post; frame is jal ** bne ** Q ** R)
    have hQR2_emp : (empAssertion **
        (((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
          ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) ** Q ** R))).holdsFor s2 := by
      simp only [sepConj_emp_left']; exact hQR2'
    obtain ⟨k3, s3, hstep3, hpc3, hQR3⟩ := jal_x0_spec_gen
      (BitVec.ofNat 21 (4 * else_body.length + 4))
      (s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length))
      _ hjal_pcfree s2 hjal_cr hQR2_emp hpc2
    -- hQR3 : (empAssertion ** (jal ** (bne ** Q ** R))).holdsFor s3
    -- Extract (Q ** R) by stripping empAssertion then two instrAt's
    have hQR3_flat : (((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) ** Q ** R)).holdsFor s3 := by
      simp only [sepConj_emp_left'] at hQR3; exact hQR3
    have hQR3' : (Q ** R).holdsFor s3 :=
      holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hQR3_flat)
    -- The exit address: thenExit + signExtend21(end_off) = exit_
    have hexit : (s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) + signExtend21 (BitVec.ofNat 21 (4 * else_body.length + 4)) =
        s.pc + BitVec.ofNat 64 (4 * (if_eq rs1 rs2 then_body else_body).length) := by
      rw [signExtend21_ofNat_small he_small]
      simp only [if_eq_length]; bv_omega
    rw [hexit] at hpc3
    have hstep1 : stepN 1 s = some (s.setPC (s.pc + 4)) := by
      show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    exact ⟨1 + (k2 + k3), s3,
      stepN_add_eq hstep1
        (stepN_add_eq hstep2 hstep3),
      hpc3, hQR3'⟩
  · -- BNE taken: v1 /= v2, PC -> elseEntry
    have hexec' : execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) =
        s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) := by
      simp only [execInstrBr, hrs1, hrs2, bne_iff_ne, ne_eq, heq, not_false_eq_true, ite_true]
    have hse : signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)) =
        BitVec.ofNat 64 (4 * (then_body.length + 1) + 4) :=
      signExtend13_ofNat_small ht_small
    have haddr : s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)) =
        s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length) + 4 := by
      rw [hse]; bv_omega
    -- After BNE
    have hPR1 := holdsFor_pcFree_setPC hpcfree_all
      (v := s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) hPR
    -- Rearrange to (aand_ne ** (bne ** jal ** R))
    have hPR1' : ((P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
         ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)).holdsFor
          (s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)))) := by
      obtain ⟨hp, hcompat, hpq⟩ := hPR1
      rw [hassert_perm] at hpq
      obtain ⟨h1', h2', hd', hu', haand_h, hframe_h⟩ := hpq
      exact ⟨hp, hcompat, h1', h2', hd', hu',
        aAnd_mono_right (aAnd_mono_right (aAnd_pure_right_of_true heq)) h1' haand_h, hframe_h⟩
    -- Apply else-body triple with frame = (bne ** jal ** R)
    obtain ⟨k2, s2, hstep2, hpc2, hQR2⟩ := helse _ hframe_pcfree
      (s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))))
      (CodeReq.empty_satisfiedBy _) hPR1' (by simp [MachineState.setPC]; exact haddr)
    -- hQR2 : (Q ** (bne ** jal ** R)).holdsFor s2
    -- Extract (Q ** R) from (Q ** (bne ** (jal ** R)))
    have hassert_else :
      (Q ** ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
           ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)) =
      (((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
           ((s.pc + 4 + BitVec.ofNat 64 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4)))) ** (Q ** R)) := by
      funext h; exact propext ⟨fun hp => by sep_perm hp, fun hp => by sep_perm hp⟩
    have hQR2' : (Q ** R).holdsFor s2 := by
      obtain ⟨hp, hcompat, hpq⟩ := hQR2
      exact holdsFor_sepConj_elim_right ⟨hp, hcompat, hassert_else ▸ hpq⟩
    have hstep1 : stepN 1 s = some (s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)))) := by
      show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    exact ⟨1 + k2, s2,
      stepN_add_eq hstep1 hstep2,
      hpc2, hQR2'⟩

-- ============================================================================
-- N-exit CPS specifications for if_eq
-- ============================================================================

/-- The if_eq macro satisfies a cpsNBranch spec with two exits,
    derived from the existing cpsBranch spec.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register. -/
theorem if_eq_branch_step_n (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body : Program)
    (base : Word) (P : Assertion)
    (hP : P.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12) :
    let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)
    let bneInstr := Instr.BNE rs1 rs2 else_off
    let thenEntry := base + 4
    let elseEntry := base + 4 + BitVec.ofNat 64 (4 * then_body.length) + 4
    let pre := (base ↦ᵢ bneInstr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))
    cpsNBranch base CodeReq.empty pre
      [ (thenEntry, (base ↦ᵢ bneInstr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝)),
        (elseEntry, (base ↦ᵢ bneInstr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝)) ] := by
  simp only
  exact cpsBranch_to_cpsNBranch
    (if_eq_branch_step rs1 rs2 v1 v2 then_body base P hP ht_small)

/-- Full N-exit CPS specification for if_eq, using cpsNBranch_merge.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register.

    Requires instrAt for both the BNE at base and the JAL at thenExit.
    Same statement as if_eq_spec; provided for API symmetry with if_eq_branch_step_n. -/
theorem if_eq_spec_n (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Word) (P Q : Assertion)
    (hP : P.pcFree) (hQ : Q.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12)
    (he_small : 4 * (else_body.length) + 4 < 2^20) :
    let prog := if_eq rs1 rs2 then_body else_body
    let exit_ := base + BitVec.ofNat 64 (4 * prog.length)
    let thenEntry := base + 4
    let thenExit  := base + 4 + BitVec.ofNat 64 (4 * then_body.length)
    let elseEntry := thenExit + 4
    let elseExit  := exit_
    let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)
    let end_off  : BitVec 21 := BitVec.ofNat 21 (4 * else_body.length + 4)
    let bneInstr := Instr.BNE rs1 rs2 else_off
    let jalInstr := Instr.JAL .x0 end_off
    let pre := (base ↦ᵢ bneInstr) ** (thenExit ↦ᵢ jalInstr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))
    (cpsTriple thenEntry thenExit CodeReq.empty
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) Q) →
    (cpsTriple elseEntry elseExit CodeReq.empty
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) Q) →
    cpsTriple base exit_ CodeReq.empty pre Q := by
  exact if_eq_spec rs1 rs2 v1 v2 then_body else_body base P Q hP hQ ht_small he_small

-- ============================================================================
-- Summary
-- ============================================================================

/-!
  ## Control Flow Macros (64-bit RISC-V)

  The `if_eq` macro demonstrates the CPS approach to branching:

  1. **Macro definition**: `if_eq` produces a flat list of instructions
     with computed byte offsets for branches.

  2. **Step-based execution**: Using `loadProgram` + `stepN`, we can
     execute the branching code correctly (verified by `decide`).

  3. **CPS specification**: `cpsBranch` captures the two-exit nature
     of conditional code. `cpsBranch_merge` composes it back into
     a single-exit `cpsTriple`.

  4. **Symbolic proofs**: `if_eq_branch_step` proves the BNE dispatch,
     and `if_eq_spec` composes the full correctness specification
     from branch-level and body-level specs.

  ### pcFree / pcIndep

  The `pcFree` predicate marks assertions as PC-independent (don't own the PC),
  which is needed because branch/jump instructions only modify PC.
  The `pcIndep` predicate is the MachineState-level equivalent for `holdsFor`.
-/

-- ============================================================================
-- Countdown loop: backward branch test
-- ============================================================================

/-- Countdown loop: while x10 ≠ 0, decrement x10.
    base:     BEQ x10 x0 12     -- exit if x10 = 0
    base+4:   ADDI x10 x10 -1   -- decrement
    base+8:   JAL x0 -8          -- back to base
    base+12:  (exit) -/
def countdown_loop : Program := [
  Instr.BEQ .x10 .x0 (12 : BitVec 13),
  Instr.ADDI .x10 .x10 (BitVec.ofNat 12 (2^12 - 1)),  -- -1
  Instr.JAL .x0 (BitVec.ofNat 21 (2^21 - 8))           -- -8
]

/-- Execute countdown loop from a given initial x10 value. -/
def runCountdown (x10val : Word) (steps : Nat) : Option MachineState :=
  let s := { mkTestState x10val 0 with code := loadProgram 0 countdown_loop }
  stepN steps s

-- x10=0: BEQ taken immediately → PC=12 in 1 step
/-- When x10 = 0, exits immediately (1 step, PC=12). -/
example : (runCountdown 0 1).bind (fun s => some s.pc) = some 12 := by
  decide

/-- When x10 = 0, x10 stays 0. -/
example : (runCountdown 0 1).bind (fun s => some (s.getReg .x10)) = some 0 := by
  decide

-- x10=1: BEQ not taken → ADDI (x10=0) → JAL (back to 0) → BEQ taken → PC=12
-- That's 4 steps per iteration + 1 for final exit = 4 steps total
/-- When x10 = 1, exits after 4 steps (PC=12, x10=0). -/
example : (runCountdown 1 4).bind (fun s => some s.pc) = some 12 := by
  decide

example : (runCountdown 1 4).bind (fun s => some (s.getReg .x10)) = some 0 := by
  decide

-- x10=3: 3 iterations × 3 steps + 1 final BEQ = 10 steps
/-- When x10 = 3, exits after 10 steps (PC=12, x10=0). -/
example : (runCountdown 3 10).bind (fun s => some s.pc) = some 12 := by
  decide

example : (runCountdown 3 10).bind (fun s => some (s.getReg .x10)) = some 0 := by
  decide

end EvmAsm.Rv64
