/-
  EvmAsm.Rv32.ControlFlow

  Control flow macros using branch and jump instructions, with CPS-style
  specifications.

  This module provides:
  - if_eq: a conditional macro (if rs1 = rs2 then ... else ...)
  - CPS specifications for the macro
  - Concrete examples verified by native_decide
-/

import EvmAsm.Rv32.Basic
import EvmAsm.Rv32.Instructions
import EvmAsm.Rv32.Program
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.SyscallSpecs

namespace EvmAsm

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
  native_decide

/-- When x10 = x11 = 42, after 3 steps PC should be at exit (16). -/
example : (runIfEqExample 42 42 3).bind (fun s => some s.pc) = some 16 := by
  native_decide

-- Unequal case: BNE(taken, offset=4*(1+1)+4=12) → PC=12, LI x12 0 → PC=16
-- That's 2 steps to reach exit at PC=16

/-- When x10 = 42, x11 = 99, after 2 steps x12 should be 0. -/
example : (runIfEqExample 42 99 2).bind (fun s => some (s.getReg .x12)) = some 0 := by
  native_decide

/-- When x10 = 42, x11 = 99, after 2 steps PC should be at exit (16). -/
example : (runIfEqExample 42 99 2).bind (fun s => some s.pc) = some 16 := by
  native_decide

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
  native_decide

/-- When x10 = 10, x11 = 3: takes else-branch, x12 := 10 - 3 = 7. -/
example : (runIfEqArith 10 3 2).bind (fun s => some (s.getReg .x12)) = some 7 := by
  native_decide

-- ============================================================================
-- Helper lemmas for symbolic proofs
-- ============================================================================

/-- A predicate on MachineState is PC-independent: it holds regardless of the PC value. -/
def pcIndep (P : MachineState → Prop) : Prop := ∀ s v, P s → P (s.setPC v)

theorem pcIndep_and {P Q : MachineState → Prop} (hP : pcIndep P) (hQ : pcIndep Q) :
    pcIndep (fun s => P s ∧ Q s) := by
  intro s v ⟨hp, hq⟩
  exact ⟨hP s v hp, hQ s v hq⟩

theorem pcIndep_holdsFor_regIs (r : Reg) (val : Word) :
    pcIndep (regIs r val).holdsFor := by
  intro s v h
  simp only [holdsFor_regIs, MachineState.getReg_setPC] at *; exact h

theorem pcIndep_holdsFor_memIs (a : Addr) (val : Word) :
    pcIndep (memIs a val).holdsFor := by
  intro s v h
  simp only [holdsFor_memIs, MachineState.getMem, MachineState.setPC] at *; exact h

theorem pcIndep_committedIs (vals : List (Word × Word)) :
    pcIndep (MachineState.committedIs vals) := by
  intro s v h
  simp only [MachineState.committedIs, MachineState.committed_setPC] at *; exact h

theorem pcIndep_publicValuesIs (vals : List (BitVec 8)) :
    pcIndep (MachineState.publicValuesIs vals) := by
  intro s v h
  simp only [MachineState.publicValuesIs, MachineState.publicValues_setPC] at *; exact h

theorem pcIndep_privateInputIs (vals : List (BitVec 8)) :
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

/-- Sign-extend a small 13-bit value (MSB clear) to 32 bits. -/
theorem signExtend13_ofNat_small (n : Nat) (h : n < 2^12) :
    signExtend13 (BitVec.ofNat 13 n) = BitVec.ofNat 32 n := by
  unfold signExtend13
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

/-- Sign-extend a small 21-bit value (MSB clear) to 32 bits. -/
theorem signExtend21_ofNat_small (n : Nat) (h : n < 2^20) :
    signExtend21 (BitVec.ofNat 21 n) = BitVec.ofNat 32 n := by
  unfold signExtend21
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

/-- Load the first instruction from a program at its base address. -/
theorem loadProgram_at_base (base : Addr) (instr : Instr) (rest : List Instr) :
    loadProgram base (instr :: rest) base = some instr := by
  simp [loadProgram, BitVec.sub_self]

/-- Load instruction k from a program at address base + 4*k. -/
theorem loadProgram_at_index (base : Addr) (prog : List Instr) (k : Nat)
    (hk : k < prog.length) (h4k : 4 * k < 2^32) :
    loadProgram base prog (base + BitVec.ofNat 32 (4 * k)) = prog[k]? := by
  simp [loadProgram]
  have hbase := base.isLt
  have : (4294967296 - BitVec.toNat base + (BitVec.toNat base + 4 * k)) % 4294967296
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
    PartialState.union_empty_right h, hp, rfl, hprop⟩

/-- The if_eq macro satisfies a cpsBranch spec: it either goes to
    the then-body entry (base+4) with equality, or to the else-body
    entry (base+4+4*t+4) with inequality, in exactly one step.

    Uses additive conjunction (⊓) so rs1 and rs2 may be the same register.
    BNE only modifies PC, so all assertions are preserved through setPC.
    The branch condition is encoded as a pure assertion on v1, v2.

    Requires instrAt for the BNE instruction at base. -/
theorem if_eq_branch_step (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Addr) (P : Assertion)
    (hP : P.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12) :
    let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)
    let bne_instr := Instr.BNE rs1 rs2 else_off
    let then_entry := base + 4
    let else_entry := base + 4 + BitVec.ofNat 32 (4 * then_body.length) + 4
    let pre := (base ↦ᵢ bne_instr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))
    cpsBranch base pre
      then_entry ((base ↦ᵢ bne_instr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝))
      else_entry ((base ↦ᵢ bne_instr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝)) := by
  simp only
  intro R hR s hPR hpc; subst hpc
  -- Extract instrAt from the precondition
  have hfetch : s.code s.pc = some (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  -- Extract register values from the aAnd part
  have haAnd := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)
  have hrs1 : s.getReg rs1 = v1 :=
    (holdsFor_regIs _ _ s).mp (aAnd_holdsFor_elim (aAnd_holdsFor_elim haAnd).2).1
  have hrs2 : s.getReg rs2 = v2 :=
    (holdsFor_regIs _ _ s).mp (aAnd_holdsFor_elim (aAnd_holdsFor_elim haAnd).2).2
  -- Execute the BNE instruction
  have hstep' : step s = some (execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)))) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  -- The entire precondition (P ** R form from cpsBranch) is pcFree
  have hpcfree : (((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))) ** R).pcFree :=
    pcFree_sepConj (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_aAnd hP (pcFree_aAnd (pcFree_regIs _ _) (pcFree_regIs _ _)))) hR
  -- Case split on v1 = v2
  by_cases heq : v1 = v2
  · -- Not taken: v1 = v2 → PC = s.pc + 4 = then_entry (exit_t)
    have hexec' : execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1, hrs2, heq, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
    refine ⟨1, s.setPC (s.pc + 4), ?_, Or.inl ⟨by simp [MachineState.setPC], ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · -- Preserve assertions through setPC and add ⌜v1 = v2⌝
      have hPR' := holdsFor_pcFree_setPC hpcfree s (s.pc + 4) hPR
      -- Strengthen the aAnd part: add ⌜v1 = v2⌝ to inner sepConj
      obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨ha, hb, hda, hua, hinstr, haand⟩, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨ha, hb, hda, hua, hinstr, aAnd_mono_right (aAnd_mono_right (aAnd_pure_right_of_true heq)) hb haand⟩, hR2⟩
  · -- Taken: v1 ≠ v2 → PC = s.pc + signExtend13(else_off) = else_entry (exit_f)
    have hexec' : execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) =
        s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) := by
      simp only [execInstrBr, hrs1, hrs2, bne_iff_ne, ne_eq, heq, not_false_eq_true, ite_true]
    -- Show that signExtend13(else_off) = 4*(t+1)+4
    have hse : signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)) =
        BitVec.ofNat 32 (4 * (then_body.length + 1) + 4) :=
      signExtend13_ofNat_small _ ht_small
    -- Show that s.pc + 4*(t+1)+4 = s.pc + 4 + 4*t + 4
    have haddr : s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)) =
        s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length) + 4 := by
      rw [hse]; bv_omega
    refine ⟨1, s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))), ?_,
      Or.inr ⟨by simp [MachineState.setPC]; exact haddr, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · -- Preserve assertions through setPC and add ⌜v1 ≠ v2⌝
      have hPR' := holdsFor_pcFree_setPC hpcfree s
        (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨ha, hb, hda, hua, hinstr, haand⟩, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        ⟨ha, hb, hda, hua, hinstr, aAnd_mono_right (aAnd_mono_right (aAnd_pure_right_of_true heq)) hb haand⟩, hR2⟩

/-- Full CPS specification for if_eq: given that the then-body is correct
    under equality and the else-body is correct under inequality,
    the whole if_eq is a cpsTriple from entry to exit.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register.

    Requires instrAt for both the BNE at base and the JAL at then_exit. -/
theorem if_eq_spec (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Addr) (P Q : Assertion)
    (hP : P.pcFree) (hQ : Q.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12)
    (he_small : 4 * (else_body.length) + 4 < 2^20) :
    let prog := if_eq rs1 rs2 then_body else_body
    let exit_ := base + BitVec.ofNat 32 (4 * prog.length)
    let then_entry := base + 4
    let then_exit  := base + 4 + BitVec.ofNat 32 (4 * then_body.length)
    let else_entry := then_exit + 4
    let else_exit  := exit_
    let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)
    let end_off  : BitVec 21 := BitVec.ofNat 21 (4 * else_body.length + 4)
    let bne_instr := Instr.BNE rs1 rs2 else_off
    let jal_instr := Instr.JAL .x0 end_off
    let pre := (base ↦ᵢ bne_instr) ** (then_exit ↦ᵢ jal_instr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))
    (cpsTriple then_entry then_exit
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) Q) →
    (cpsTriple else_entry else_exit
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) Q) →
    cpsTriple base exit_ pre Q := by
  simp only
  intro hthen helse R hR s hPR hpc; subst hpc
  -- hPR : ((bne ** (jal ** aAnd)) ** R).holdsFor s
  -- Extract instrAt facts
  have hfetch_bne : s.code s.pc = some (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  -- Extract register values from the aAnd part
  have haAnd := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hrs1 : s.getReg rs1 = v1 :=
    (holdsFor_regIs _ _ s).mp (aAnd_holdsFor_elim (aAnd_holdsFor_elim haAnd).2).1
  have hrs2 : s.getReg rs2 = v2 :=
    (holdsFor_regIs _ _ s).mp (aAnd_holdsFor_elim (aAnd_holdsFor_elim haAnd).2).2
  -- Execute BNE
  have hstep' : step s = some (execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)))) :=
    step_non_ecall_non_mem s _ hfetch_bne (by nofun) (by nofun) (by rfl)
  -- pcFree for the full precondition with frame
  have hpcfree_all : (((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
      ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))) ** R).pcFree :=
    pcFree_sepConj (pcFree_sepConj (pcFree_instrAt _ _)
      (pcFree_sepConj (pcFree_instrAt _ _)
        (pcFree_aAnd hP (pcFree_aAnd (pcFree_regIs _ _) (pcFree_regIs _ _))))) hR
  -- Body-triple frame: bne ** jal ** R (pcFree)
  have hframe_pcfree : ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
      ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R).pcFree :=
    pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _) hR)
  -- Helper: rearranging ** chains
  -- (bne ** (jal ** aand)) ** R = (aand ** (bne ** (jal ** R))) as assertions
  have hassert_perm : (((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
      ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))) ** R) =
    ((P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)) **
      ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
       ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)) := by
    funext h; exact propext ⟨fun hp => by sep_perm hp, fun hp => by sep_perm hp⟩
  -- Case split on v1 = v2
  by_cases heq : v1 = v2
  · -- BNE not taken: v1 = v2, PC -> s.pc + 4 = then_entry
    have hexec' : execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1, hrs2, heq, bne_iff_ne, ne_eq, not_true_eq_false, ite_false]
    -- After BNE: all pcFree assertions preserved
    have hPR1 := holdsFor_pcFree_setPC hpcfree_all s (s.pc + 4) hPR
    -- Rearrange to (aand ** (bne ** jal ** R)), then strengthen aand with ⌜v1 = v2⌝
    have hPR1' : ((P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
         ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)).holdsFor
          (s.setPC (s.pc + 4)) := by
      obtain ⟨hp, hcompat, hpq⟩ := hPR1
      rw [hassert_perm] at hpq
      obtain ⟨h1', h2', hd', hu', haand_h, hframe_h⟩ := hpq
      exact ⟨hp, hcompat, h1', h2', hd', hu',
        aAnd_mono_right (aAnd_mono_right (aAnd_pure_right_of_true heq)) h1' haand_h, hframe_h⟩
    -- Apply then-body triple
    obtain ⟨k2, s2, hstep2, hpc2, hQR2⟩ := hthen _ hframe_pcfree
      (s.setPC (s.pc + 4)) hPR1' rfl
    -- hQR2 : (Q ** (bne ** jal ** R)).holdsFor s2 at s2.pc = then_exit
    -- Rearrange for JAL: (Q ** (bne ** (jal ** R))) -> (jal ** (bne ** Q ** R))
    have hassert_perm2 :
      (Q ** ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
           ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)) =
      (((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) ** Q ** R)) := by
      funext h; exact propext ⟨fun hp => by sep_perm hp, fun hp => by sep_perm hp⟩
    have hQR2' : (((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) ** Q ** R)).holdsFor s2 := by
      obtain ⟨hp, hcompat, hpq⟩ := hQR2
      exact ⟨hp, hcompat, hassert_perm2 ▸ hpq⟩
    -- Apply JAL spec
    have hjal_pcfree : ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) ** Q ** R).pcFree :=
      pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj hQ hR)
    obtain ⟨k3, s3, hstep3, hpc3, hQR3⟩ := jal_x0_spec_gen
      (BitVec.ofNat 21 (4 * else_body.length + 4))
      (s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length))
      _ hjal_pcfree s2 hQR2' hpc2
    -- hQR3 : (jal ** (bne ** Q ** R)).holdsFor s3
    -- Extract (Q ** R) by dropping the two instrAt's
    have hQR3' : (Q ** R).holdsFor s3 :=
      holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hQR3)
    -- The exit address: then_exit + signExtend21(end_off) = exit_
    have hexit : (s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) + signExtend21 (BitVec.ofNat 21 (4 * else_body.length + 4)) =
        s.pc + BitVec.ofNat 32 (4 * (if_eq rs1 rs2 then_body else_body).length) := by
      rw [signExtend21_ofNat_small _ he_small]
      simp only [if_eq_length]; bv_omega
    rw [hexit] at hpc3
    have hstep1 : stepN 1 s = some (s.setPC (s.pc + 4)) := by
      show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    exact ⟨1 + (k2 + k3), s3,
      stepN_add_eq 1 (k2 + k3) s _ s3 hstep1
        (stepN_add_eq k2 k3 _ s2 s3 hstep2 hstep3),
      hpc3, hQR3'⟩
  · -- BNE taken: v1 /= v2, PC -> else_entry
    have hexec' : execInstrBr s (Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) =
        s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) := by
      simp only [execInstrBr, hrs1, hrs2, bne_iff_ne, ne_eq, heq, not_false_eq_true, ite_true]
    have hse : signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)) =
        BitVec.ofNat 32 (4 * (then_body.length + 1) + 4) :=
      signExtend13_ofNat_small _ ht_small
    have haddr : s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)) =
        s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length) + 4 := by
      rw [hse]; bv_omega
    -- After BNE
    have hPR1 := holdsFor_pcFree_setPC hpcfree_all s
      (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) hPR
    -- Rearrange to (aand_ne ** (bne ** jal ** R))
    have hPR1' : ((P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) **
        ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
         ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)).holdsFor
          (s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)))) := by
      obtain ⟨hp, hcompat, hpq⟩ := hPR1
      rw [hassert_perm] at hpq
      obtain ⟨h1', h2', hd', hu', haand_h, hframe_h⟩ := hpq
      exact ⟨hp, hcompat, h1', h2', hd', hu',
        aAnd_mono_right (aAnd_mono_right (aAnd_pure_right_of_true heq)) h1' haand_h, hframe_h⟩
    -- Apply else-body triple with frame = (bne ** jal ** R)
    obtain ⟨k2, s2, hstep2, hpc2, hQR2⟩ := helse _ hframe_pcfree
      (s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))))
      hPR1' (by simp [MachineState.setPC]; exact haddr)
    -- hQR2 : (Q ** (bne ** jal ** R)).holdsFor s2
    -- Extract (Q ** R) from (Q ** (bne ** (jal ** R)))
    have hassert_else :
      (Q ** ((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
           ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4))) ** R)) =
      (((s.pc ↦ᵢ Instr.BNE rs1 rs2 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4))) **
           ((s.pc + 4 + BitVec.ofNat 32 (4 * then_body.length)) ↦ᵢ Instr.JAL Reg.x0 (BitVec.ofNat 21 (4 * else_body.length + 4)))) ** (Q ** R)) := by
      funext h; exact propext ⟨fun hp => by sep_perm hp, fun hp => by sep_perm hp⟩
    have hQR2' : (Q ** R).holdsFor s2 := by
      obtain ⟨hp, hcompat, hpq⟩ := hQR2
      exact holdsFor_sepConj_elim_right ⟨hp, hcompat, hassert_else ▸ hpq⟩
    have hstep1 : stepN 1 s = some (s.setPC (s.pc + signExtend13 (BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)))) := by
      show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    exact ⟨1 + k2, s2,
      stepN_add_eq 1 k2 s _ s2 hstep1 hstep2,
      hpc2, hQR2'⟩

-- ============================================================================
-- N-exit CPS specifications for if_eq
-- ============================================================================

/-- The if_eq macro satisfies a cpsNBranch spec with two exits,
    derived from the existing cpsBranch spec.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register. -/
theorem if_eq_branch_step_n (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Addr) (P : Assertion)
    (hP : P.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12) :
    let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)
    let bne_instr := Instr.BNE rs1 rs2 else_off
    let then_entry := base + 4
    let else_entry := base + 4 + BitVec.ofNat 32 (4 * then_body.length) + 4
    let pre := (base ↦ᵢ bne_instr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))
    cpsNBranch base pre
      [ (then_entry, (base ↦ᵢ bne_instr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝)),
        (else_entry, (base ↦ᵢ bne_instr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝)) ] := by
  simp only
  exact cpsBranch_to_cpsNBranch _ _ _ _ _ _
    (if_eq_branch_step rs1 rs2 v1 v2 then_body else_body base P hP ht_small)

/-- Full N-exit CPS specification for if_eq, using cpsNBranch_merge.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register.

    Requires instrAt for both the BNE at base and the JAL at then_exit.
    Same statement as if_eq_spec; provided for API symmetry with if_eq_branch_step_n. -/
theorem if_eq_spec_n (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Addr) (P Q : Assertion)
    (hP : P.pcFree) (hQ : Q.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12)
    (he_small : 4 * (else_body.length) + 4 < 2^20) :
    let prog := if_eq rs1 rs2 then_body else_body
    let exit_ := base + BitVec.ofNat 32 (4 * prog.length)
    let then_entry := base + 4
    let then_exit  := base + 4 + BitVec.ofNat 32 (4 * then_body.length)
    let else_entry := then_exit + 4
    let else_exit  := exit_
    let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (then_body.length + 1) + 4)
    let end_off  : BitVec 21 := BitVec.ofNat 21 (4 * else_body.length + 4)
    let bne_instr := Instr.BNE rs1 rs2 else_off
    let jal_instr := Instr.JAL .x0 end_off
    let pre := (base ↦ᵢ bne_instr) ** (then_exit ↦ᵢ jal_instr) ** (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2))
    (cpsTriple then_entry then_exit
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) Q) →
    (cpsTriple else_entry else_exit
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) Q) →
    cpsTriple base exit_ pre Q := by
  exact if_eq_spec rs1 rs2 v1 v2 then_body else_body base P Q hP hQ ht_small he_small

-- ============================================================================
-- Summary
-- ============================================================================

/-!
  ## Control Flow Macros

  The `if_eq` macro demonstrates the CPS approach to branching:

  1. **Macro definition**: `if_eq` produces a flat list of instructions
     with computed byte offsets for branches.

  2. **Step-based execution**: Using `loadProgram` + `stepN`, we can
     execute the branching code correctly (verified by `native_decide`).

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

end EvmAsm
