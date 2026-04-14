/-
  EvmAsm.Evm64.Stack

  Separation logic assertions for 256-bit EVM values stored as
  4 little-endian 64-bit limbs in consecutive doubleword-aligned memory.
-/

import EvmAsm.Evm64.Basic
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

open EvmWord

/-- Assert that 4 consecutive memory doublewords hold the limbs of an EvmWord.
    The limbs are stored little-endian: addr+0 is the LSB limb, addr+24 is the MSB limb. -/
def evmWordIs (addr : Word) (v : EvmWord) : Assertion :=
  (addr ↦ₘ v.getLimbN 0) **
  ((addr + 8) ↦ₘ v.getLimbN 1) **
  ((addr + 16) ↦ₘ v.getLimbN 2) **
  ((addr + 24) ↦ₘ v.getLimbN 3)

/-- Assert an EVM stack starting at sp. Each element is 32 bytes (4 × 8-byte limbs). -/
def evmStackIs (sp : Word) (values : List EvmWord) : Assertion :=
  match values with
  | [] => empAssertion
  | v :: vs => evmWordIs sp v ** evmStackIs (sp + 32) vs

theorem pcFree_evmWordIs (addr : Word) (v : EvmWord) :
    (evmWordIs addr v).pcFree := by
  unfold evmWordIs; pcFree

theorem pcFree_evmStackIs (sp : Word) (values : List EvmWord) :
    (evmStackIs sp values).pcFree := by
  induction values generalizing sp with
  | nil => exact pcFree_emp
  | cons v vs ih => exact pcFree_sepConj (pcFree_evmWordIs sp v) (ih (sp + 32))

instance (addr : Word) (v : EvmWord) : Assertion.PCFree (evmWordIs addr v) :=
  ⟨pcFree_evmWordIs addr v⟩

instance (sp : Word) (values : List EvmWord) : Assertion.PCFree (evmStackIs sp values) :=
  ⟨pcFree_evmStackIs sp values⟩

theorem evmStackIs_cons (sp : Word) (v : EvmWord) (vs : List EvmWord) :
    evmStackIs sp (v :: vs) = (evmWordIs sp v ** evmStackIs (sp + 32) vs) := rfl

theorem evmStackIs_nil (sp : Word) :
    evmStackIs sp [] = empAssertion := rfl

-- ============================================================================
-- Shared infrastructure for stack operation specs
-- ============================================================================

@[simp] theorem EvmWord.getLimb_zero (i : Fin 4) : (0 : EvmWord).getLimb i = 0 := by
  have h : ∀ j : Fin 4, (0 : EvmWord).getLimb j = 0 := by decide
  exact h i

@[simp] theorem signExtend12_neg32 : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by
  decide

/-- Sign-extend a small non-negative 12-bit value to 64 bits.
    The MSB is clear when m < 2^11 = 2048, so signExtend = zeroExtend = identity. -/
theorem signExtend12_ofNat_small (m : Nat) (hm : m < 2048) :
    signExtend12 (BitVec.ofNat 12 m) = BitVec.ofNat 64 m := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

/-- Split evmStackIs at position k: extract the kth element (0-indexed). -/
theorem evmStackIs_split_at (sp : Word) (stack : List EvmWord) (k : Nat)
    (hk : k < stack.length) :
    evmStackIs sp stack =
      (evmStackIs sp (stack.take k) **
       evmWordIs (sp + BitVec.ofNat 64 (k * 32)) (stack[k]'hk) **
       evmStackIs (sp + BitVec.ofNat 64 ((k + 1) * 32)) (stack.drop (k + 1))) := by
  induction k generalizing sp stack with
  | zero =>
    cases stack with
    | nil => simp at hk
    | cons v vs =>
      simp only [Nat.zero_mul, List.take_zero,
                 List.drop_succ_cons, List.drop_zero, List.getElem_cons_zero,
                 evmStackIs_cons, evmStackIs_nil, sepConj_emp_left', BitVec.add_zero]
      congr 1
  | succ k ih =>
    cases stack with
    | nil => simp at hk
    | cons v vs =>
      have hk' : k < vs.length := by simp at hk; omega
      have a1 : sp + (32 : Word) + BitVec.ofNat 64 (k * 32) =
                sp + BitVec.ofNat 64 ((k + 1) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have a2 : sp + (32 : Word) + BitVec.ofNat 64 ((k + 1) * 32) =
                sp + BitVec.ofNat 64 ((k + 2) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [evmStackIs_cons, ih (sp + 32) vs hk', a1, a2]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ]
      simp only [evmStackIs_cons, sepConj_assoc']

end EvmAsm.Evm64
