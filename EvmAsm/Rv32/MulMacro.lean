/-
  EvmAsm.Rv32.MulMacro

  A verified "multiply by constant" macro for RISC-V, inspired by
  the add_mulc macro from "Coq: The world's best macro assembler?"
  (Kennedy et al., 2013).

  The idea: to multiply register `rs` by a compile-time constant `m`,
  we use the shift-and-add algorithm. The result accumulates in register `rd`.
  We shift `rs` left through the bits of `m`, adding to `rd` whenever
  we encounter a 1 bit.

  In RISC-V (unlike x86), we need a temporary register for shifts since
  instructions are 3-operand. We use `rs` as the shifting operand (it gets
  destroyed) and `rd` as the accumulator.

  The macro:
    add_mulc nbits rd rs m :=
      if nbits = 0 then skip
      else if m is odd then
        ADD rd, rd, rs;;   -- accumulate
        SLLI rs, rs, 1;;   -- shift multiplier left
        add_mulc (nbits-1) rd rs (m/2)
      else
        SLLI rs, rs, 1;;   -- shift multiplier left
        add_mulc (nbits-1) rd rs (m/2)

  Precondition:  rd ↦ᵣ v, rs ↦ᵣ w
  Postcondition: rd ↦ᵣ v + w * m, rs ↦ᵣ (something)
-/

import EvmAsm.Rv32.Basic
import EvmAsm.Rv32.Instructions
import EvmAsm.Rv32.Program
import EvmAsm.Rv32.SepLogic

namespace EvmAsm

-- ============================================================================
-- The multiply-by-constant macro
-- ============================================================================

/-- Generate a program that computes rd := rd + rs * m, destroying rs.
    `nbits` bounds the number of bits to process (recursion fuel).

    **Acknowledgment**: This macro is adapted from the `add_mulc` implementation in:
    Andrew Kennedy, Nick Benton, Jonas B. Jensen, Pierre-Evariste Dagand.
    "Coq: The world's best macro assembler?" PPDP 2013, ACM.
    https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/

    The original implementation uses x86 instructions in Coq. This version
    adapts the shift-and-add algorithm to RISC-V instructions in Lean 4. -/
def add_mulc (nbits : Nat) (rd rs : Reg) (m : Nat) : Program :=
  match nbits with
  | 0 => prog_skip
  | nbits' + 1 =>
    if m % 2 == 1 then
      ADD rd rd rs ;;
      SLLI rs rs 1 ;;
      add_mulc nbits' rd rs (m / 2)
    else
      SLLI rs rs 1 ;;
      add_mulc nbits' rd rs (m / 2)

-- Some examples of what the macro produces:

-- Multiply by 0: produces no instructions.
#eval add_mulc 8 .x10 .x11 0

-- Multiply by 1: ADD then SLLI (plus trailing shifts).
#eval add_mulc 8 .x10 .x11 1

-- Multiply by 6 (= 110₂).
#eval add_mulc 8 .x10 .x11 6

-- Multiply by 10 (= 1010₂).
#eval add_mulc 8 .x10 .x11 10

-- ============================================================================
-- Concrete examples with full proofs (by computation)
-- ============================================================================

/-- A concrete initial state for testing. -/
def testState (v w : Word) : MachineState where
  regs := fun r =>
    match r with
    | .x10 => v
    | .x11 => w
    | _    => 0#32
  mem  := fun _ => 0#32
  pc   := 0#32

/-- Executing add_mulc 4 x10 x11 3 on the test state:
    x10 should become v + w * 3.
    Verified by direct computation. -/
example : (execProgram (testState 10 7) (add_mulc 4 .x10 .x11 3)).getReg .x10
    = 10 + 7 * 3 := by native_decide

example : (execProgram (testState 0 5) (add_mulc 4 .x10 .x11 6)).getReg .x10
    = 0 + 5 * 6 := by native_decide

example : (execProgram (testState 100 13) (add_mulc 8 .x10 .x11 10)).getReg .x10
    = 100 + 13 * 10 := by native_decide

/-- Multiply by 1 (on concrete values). -/
example : (execProgram (testState 0 42) (add_mulc 8 .x10 .x11 1)).getReg .x10
    = 42 := by native_decide

/-- Multiply by 255 (on concrete values). -/
example : (execProgram (testState 0 2) (add_mulc 8 .x10 .x11 255)).getReg .x10
    = 510 := by native_decide

-- ============================================================================
-- Specification: functional correctness (general theorem)
-- ============================================================================

/-- General correctness theorem for add_mulc.

    After executing `add_mulc nbits rd rs m`, the destination register `rd`
    holds the value `(old rd) + (old rs) * m` (in bitvector arithmetic),
    assuming rd ≠ rs, rd ≠ x0, rs ≠ x0, and m < 2^nbits.

    The proof requires detailed reasoning about register file updates
    through the shift-and-add chain. The key invariant is:
      rd = v + w * (m % 2^k)  and  rs = w * 2^k
    where k is the number of bits processed so far.

    TODO: Complete this proof using the getReg_setReg_eq/ne lemmas
    and bitvector arithmetic. -/
theorem add_mulc_correct (nbits : Nat) (rd rs : Reg)
    (hne : rd ≠ rs) (hrd : rd ≠ .x0) (hrs : rs ≠ .x0)
    (m : Nat) (hm : m < 2 ^ nbits) :
    ∀ s : MachineState,
      (execProgram s (add_mulc nbits rd rs m)).getReg rd =
        s.getReg rd + s.getReg rs * BitVec.ofNat 32 m := by
  induction nbits generalizing m with
  | zero =>
    intro s
    simp only [add_mulc, prog_skip]
    have : m = 0 := by omega
    subst this
    simp
  | succ n ih =>
    intro s
    simp only [add_mulc]
    split
    · -- m % 2 == 1 (odd case)
      next hodd =>
      simp only [execProgram_seq, ADD, SLLI, single, execProgram_cons, execProgram_nil, execInstr]
      rw [ih (m / 2) (by omega)]
      simp only [MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hne),
            MachineState.getReg_setReg_ne _ _ _ _ hne,
            MachineState.getReg_setReg_eq _ _ _ hrd,
            MachineState.getReg_setReg_eq _ _ _ hrs]
      have hodd' : m % 2 = 1 := by simp only [beq_iff_eq] at hodd; omega
      rw [BitVec.shiftLeft_eq_mul_twoPow]
      have hm_eq : BitVec.ofNat 32 m = BitVec.ofNat 32 (2 * (m / 2) + 1) := by congr 1; omega
      rw [hm_eq, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.twoPow_eq]
      show s.getReg rd + s.getReg rs + s.getReg rs * (1#32 <<< 1) * BitVec.ofNat 32 (m / 2) =
           s.getReg rd + s.getReg rs * (2#32 * BitVec.ofNat 32 (m / 2) + 1#32)
      have h2 : (1#32 <<< 1 : BitVec 32) = 2#32 := by decide
      rw [h2, BitVec.mul_add, BitVec.mul_one, BitVec.mul_assoc, BitVec.add_assoc, BitVec.add_comm (s.getReg rs)]
    · -- m % 2 != 1 (even case)
      next hmod =>
      simp only [execProgram_seq, SLLI, single, execProgram_cons, execProgram_nil, execInstr]
      rw [ih (m / 2) (by omega)]
      simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hne),
            MachineState.getReg_setReg_eq _ _ _ hrs]
      have heven : m % 2 = 0 := by
        simp only [beq_iff_eq] at hmod; omega
      rw [BitVec.shiftLeft_eq_mul_twoPow]
      have : BitVec.ofNat 32 m = BitVec.ofNat 32 2 * BitVec.ofNat 32 (m / 2) := by
        rw [BitVec.ofNat_mul_ofNat]; congr 1; omega
      rw [this, BitVec.twoPow_eq, BitVec.mul_assoc]
      simp

-- ============================================================================
-- Hoare-triple specification (with separating conjunction)
-- ============================================================================

/-- Hoare-triple specification for add_mulc, in the style of Kennedy et al.

    Precondition: rd holds v, rs holds w (as separated resources).
    Postcondition: rd holds v + w * m, rs holds an unspecified value.

    This is the key theorem connecting the macro to separation logic.
    The full proof requires the general `add_mulc_correct` theorem above.
    Note: the rd ≠ rs case is vacuously true since the separating conjunction
    (rd ↦ᵣ v) ** (rs ↦ᵣ w) is unsatisfiable when rd = rs. -/
theorem add_mulc_spec (m nbits : Nat) (hm : m < 2 ^ nbits)
    (rd rs : Reg) (hrd : rd ≠ .x0) (hrs : rs ≠ .x0)
    (v w : Word) :
    ∀ s : MachineState, ((rd ↦ᵣ v) ** (rs ↦ᵣ w)).holdsFor s →
      (execProgram s (add_mulc nbits rd rs m)).getReg rd = v + w * BitVec.ofNat 32 m := by
  intro s hpre
  by_cases hne : rd = rs
  · -- rd = rs: contradiction from separation logic (can't own same register twice)
    subst hne
    obtain ⟨_, _, h1, h2, hd, _, hp1, hp2⟩ := hpre
    rw [regIs] at hp1 hp2; subst hp1; subst hp2
    exact absurd rfl (singletonReg_disjoint_imp_ne hd)
  · rw [holdsFor_sepConj_regIs_regIs hne] at hpre
    obtain ⟨hrd_eq, hrs_eq⟩ := hpre
    rw [add_mulc_correct nbits rd rs hne hrd hrs m hm]
    rw [hrd_eq, hrs_eq]

/-- For fully concrete inputs, we can verify the Hoare triple by computation. -/
theorem add_mulc_concrete_example :
    let s := testState 10 7
    let s' := execProgram s (add_mulc 4 .x10 .x11 3)
    s'.getReg .x10 = 10 + 7 * 3 := by native_decide

-- ============================================================================
-- Multiply-by-constant as a complete operation
-- ============================================================================

/-- Full multiply macro: zero rd, then add_mulc.
    Computes rd := rs * m. -/
def mulc (nbits : Nat) (rd rs : Reg) (m : Nat) : Program :=
  SUB rd rd rd ;;
  add_mulc nbits rd rs m

/-- mulc concrete correctness: 6 * 7 = 42 -/
example :
    let s : MachineState := {
      regs := fun r => match r with | .x11 => 6 | _ => 0
      mem := fun _ => 0
      pc := 0 }
    (execProgram s (mulc 8 .x10 .x11 7)).getReg .x10 = 42 := by
  native_decide

/-- mulc concrete correctness: 13 * 10 = 130 -/
example :
    let s : MachineState := {
      regs := fun r => match r with | .x11 => 13 | _ => 0
      mem := fun _ => 0
      pc := 0 }
    (execProgram s (mulc 8 .x10 .x11 10)).getReg .x10 = 130 := by
  native_decide

end EvmAsm
