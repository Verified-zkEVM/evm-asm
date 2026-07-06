/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIter

  CodeReq decomposition for the fixed x19 two-MUL saved-bit EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulIter
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall
import EvmAsm.Evm64.Exp.CondMulPairThenMulCall

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

private theorem word_add_even_and_one_eq_zero
    (base k : Word) (hbase : base &&& 1 = 0) (hk0 : k.getLsbD 0 = false) :
    (base + k : Word) &&& 1 = 0 := by
  have hbase0 : base.getLsbD 0 = false := by
    have h := congr_arg (·.getLsbD 0) hbase
    simp only [BitVec.getLsbD_and,
      show (BitVec.getLsbD (1 : Word) 0) = true from by simp,
      Bool.and_true] at h
    exact h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [show (BitVec.getLsbD (1 : Word) 0) = true from by simp, Bool.and_true]
    rw [BitVec.getLsbD_add (by omega : 0 < 64)]
    have h_carry : BitVec.carry 0 base k false = false := by
      simp [BitVec.carry, Nat.mod_one]
    rw [hk0, h_carry, Bool.false_xor, Bool.xor_false, hbase0]
    simp
  · have h1i : (BitVec.getLsbD (1 : Word) i) = false := by
      simp only [show (1 : Word) = BitVec.ofNat 64 1 from rfl]
      rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and,
        Nat.testBit_lt_two_pow]
      exact (Nat.pow_lt_pow_right (by norm_num) hi0).trans_le le_rfl
    rw [h1i, Bool.and_false]
    simp [BitVec.getLsbD_zero]

/-- CodeReq decomposition for the fixed saved-bit iteration with separate
    MUL-call offsets at the squaring and conditional-multiply JAL sites. -/
abbrev expIterBodyFullMsbSavedBitTwoMulFixedCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block_fixed,
    CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_save_bit_block,
    exp_squaring_call_block_code (base + 32) squaringMulOff,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 136) condMulOff skipOff,
    CodeReq.ofProg (base + 244) (EvmAsm.Evm64.exp_loop_back backOff)
  ]

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
          squaringMulOff condMulOff skipOff backOff) := by
  unfold expIterBodyFullMsbSavedBitTwoMulFixedCode
  unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h28 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_msb_bit_test_block_fixed).length) = base + 28 := by
    rw [EvmAsm.Evm64.exp_msb_bit_test_block_fixed_length]
    rfl
  rw [h28]
  rw [CodeReq.ofProg_append]
  have h32 :
      (base + 28 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_save_bit_block).length) = base + 32 := by
    rw [EvmAsm.Evm64.exp_save_bit_block_length]
    bv_addr
  rw [h32]
  rw [CodeReq.ofProg_append]
  have h136 :
      (base + 32 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_squaring_call_block squaringMulOff).length) =
        base + 136 := by
    rw [EvmAsm.Evm64.exp_squaring_call_block_length]
    bv_addr
  rw [h136]
  rw [CodeReq.ofProg_append]
  have h244 :
      (base + 136 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
          condMulOff skipOff).length) = base + 244 := by
    rw [EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length]
    bv_addr
  rw [h244]
  rw [← exp_squaring_call_block_code_eq_ofProg (base + 32) squaringMulOff]
  rw [← EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg
    (base + 136) condMulOff skipOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_bit_test_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block_fixed)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_msb_bit_test_block_fixed 0
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_msb_bit_test_block_fixed_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_save_bit_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 28)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_save_bit_block 7
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_save_bit_block_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_squaring_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 32) squaringMulOff)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg,
    exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 32)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_squaring_call_block squaringMulOff) 8
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_squaring_call_block_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_cond_mul_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 136) condMulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 136)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
      condMulOff skipOff) 34
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_loop_back_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 244)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 244)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_loop_back backOff) 61
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_loop_back_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_block_subs {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block_fixed)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (exp_squaring_call_block_code (base + 32) squaringMulOff)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 136) condMulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 244)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) := by
  exact ⟨expIterBodyFullMsbSavedBitTwoMulFixedCode_bit_test_sub,
    expIterBodyFullMsbSavedBitTwoMulFixedCode_save_bit_sub,
    expIterBodyFullMsbSavedBitTwoMulFixedCode_squaring_sub,
    expIterBodyFullMsbSavedBitTwoMulFixedCode_cond_mul_sub,
    expIterBodyFullMsbSavedBitTwoMulFixedCode_loop_back_sub⟩

/-- Fixed x19 bit-test skip path lifted to the decomposed fixed iteration body. -/
theorem exp_msb_bit_test_block_fixed_skip_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 c10 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    cpsTripleWithin 4 base (base + 28)
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ c10) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ c6 + signExtend12 (-1 : BitVec 12)) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜c6 + signExtend12 (-1 : BitVec 12) ≠ 0⌝ **
       (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x10 ↦ᵣ (e >>> (63 : BitVec 6).toNat))) := by
  exact cpsTripleWithin_extend_code
    (h := EvmAsm.Evm64.exp_msb_bit_test_block_fixed_skip_spec_within
      e c6 c10 base hc6)
    (hmono := expIterBodyFullMsbSavedBitTwoMulFixedCode_bit_test_sub)

/-- Fixed x19 bit-test reload path lifted to the decomposed fixed iteration body. -/
theorem exp_msb_bit_test_block_fixed_reload_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 c10 ptr nextLimb : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    cpsTripleWithin 7 base (base + 28)
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ c10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
      ((.x19 ↦ᵣ nextLimb) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x10 ↦ᵣ (e >>> (63 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
       (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) := by
  exact cpsTripleWithin_extend_code
    (h := EvmAsm.Evm64.exp_msb_bit_test_block_fixed_reload_spec_within
      e c6 c10 ptr nextLimb base hc6)
    (hmono := expIterBodyFullMsbSavedBitTwoMulFixedCode_bit_test_sub)

/-- Saved-bit block lifted to the decomposed fixed iteration body. -/
theorem exp_save_bit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (bit v18 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 28) (base + 32)
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_save_bit_block_spec_within bit v18 (base + 28)
  have haddr : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  rw [haddr] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := expIterBodyFullMsbSavedBitTwoMulFixedCode_save_bit_sub)

/-- Fixed x19 no-reload bit-test path followed by the saved-bit store. -/
theorem exp_msb_bit_test_fixed_skip_then_save_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v10 v18 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    cpsTripleWithin (4 + 1) base (base + 32)
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
       (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ c6New) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜c6New ≠ 0⌝ ** (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  intro bit c6New
  have hBit :=
    exp_msb_bit_test_block_fixed_skip_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v10 squaringMulOff condMulOff skipOff backOff base hc6
  have hBitFramed :=
    cpsTripleWithin_frameR (.x18 ↦ᵣ v18) (by pcFree) hBit
  have hSave :=
    exp_save_bit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      bit v18 squaringMulOff condMulOff skipOff backOff base
  have hSaveFramed := cpsTripleWithin_frameL
    ((.x20 ↦ᵣ c6New) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c6New ≠ 0⌝ **
     (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)))
    (by pcFree) hSave
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hBitFramed hSaveFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Fixed x19 no-reload bit-test path followed by saved-bit store, lifted to
    the decomposed fixed iteration body plus external `mul_callable` code. -/
theorem exp_msb_bit_test_fixed_skip_then_save_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
    (e c6 v10 v18 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    cpsTripleWithin (4 + 1) base (base + 32)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
       (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ c6New) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜c6New ≠ 0⌝ ** (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  exact cpsTripleWithin_extend_code
    (h := exp_msb_bit_test_fixed_skip_then_save_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v10 v18 squaringMulOff condMulOff skipOff backOff base hc6)
    (hmono := fun a i hi => by
      simp only [CodeReq.union, hi])

/-- Fixed x19 reload bit-test path followed by the saved-bit store. -/
theorem exp_msb_bit_test_fixed_reload_then_save_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v10 v18 ptr nextLimb : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    cpsTripleWithin (7 + 1) base (base + 32)
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
       (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
      ((.x19 ↦ᵣ nextLimb) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x10 ↦ᵣ bit) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
       (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  intro bit
  have hBit :=
    exp_msb_bit_test_block_fixed_reload_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v10 ptr nextLimb squaringMulOff condMulOff skipOff backOff base hc6
  have hBitFramed :=
    cpsTripleWithin_frameR (.x18 ↦ᵣ v18) (by pcFree) hBit
  have hSave :=
    exp_save_bit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      bit v18 squaringMulOff condMulOff skipOff backOff base
  have hSaveFramed := cpsTripleWithin_frameL
    ((.x19 ↦ᵣ nextLimb) **
     (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
     (.x0 ↦ᵣ (0 : Word)) **
     ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
     (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
     ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
    (by pcFree) hSave
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hBitFramed hSaveFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Fixed x19 reload bit-test path followed by saved-bit store, lifted to the
    decomposed fixed iteration body plus external `mul_callable` code. -/
theorem exp_msb_bit_test_fixed_reload_then_save_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
    (e c6 v10 v18 ptr nextLimb mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    cpsTripleWithin (7 + 1) base (base + 32)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
       (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
      ((.x19 ↦ᵣ nextLimb) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x10 ↦ᵣ bit) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
       (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  exact cpsTripleWithin_extend_code
    (h := exp_msb_bit_test_fixed_reload_then_save_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v10 v18 ptr nextLimb squaringMulOff condMulOff skipOff backOff base hc6)
    (hmono := fun a i hi => by
      simp only [CodeReq.union, hi])

/-- Squaring-side call block lifted to the decomposed fixed iteration body
    plus the external `mul_callable` code. -/
theorem exp_squaring_call_block_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    cpsTripleWithin (17 + 64 + 9) (base + 32) (base + 136)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ squareW.getLimbN 3) **
       evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 32) + 68))) := by
  intro squareW
  have hbase' : (base + 32 : Word) &&& 1 = 0 :=
    word_add_even_and_one_eq_zero base (32 : Word) hbase (by simp)
  have h_square_sub : ∀ a i,
      exp_squaring_call_block_code (base + 32) squaringMulOff a = some i →
      expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff a = some i :=
    expIterBodyFullMsbSavedBitTwoMulFixedCode_squaring_sub
  have hd_inner : CodeReq.Disjoint
      (exp_squaring_call_block_code (base + 32) squaringMulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with h_exp | h_mul
    · left
      cases hsub : exp_squaring_call_block_code (base + 32) squaringMulOff a with
      | none => rfl
      | some i =>
        have h_ev := h_square_sub a i hsub
        exact absurd (h_ev.symm.trans h_exp) (by simp)
    · right
      exact h_mul
  have h := EvmAsm.Evm64.exp_squaring_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget squaringMulOff (base + 32) hbase' hmt hd_inner
  have haddr : (base + 32 : Word) + 104 = base + 136 := by bv_addr
  rw [haddr] at h
  have h_square_sub_union : ∀ a i,
      exp_squaring_call_block_code (base + 32) squaringMulOff a = some i →
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget)) a = some i := by
    intro a i hi
    simp only [CodeReq.union, h_square_sub a i hi]
  have h_mul_sub_union : ∀ a i, mul_callable_code mulTarget a = some i →
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget)) a = some i := by
    intro a i hi
    rcases hd a with h_iter | h_mul
    · simp only [CodeReq.union, h_iter, hi]
    · rw [hi] at h_mul
      contradiction
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := CodeReq.union_sub h_square_sub_union h_mul_sub_union)

/-- Fixed x19 no-reload prefix followed by the squaring-side MUL call. -/
theorem exp_msb_bit_test_fixed_skip_save_then_squaring_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    cpsTripleWithin ((4 + 1) + (17 + 64 + 9)) base (base + 136)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)))
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        (.x5 ↦ᵣ squareW.getLimbN 3) **
        evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
        regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        memOwn evmSp ** memOwn (evmSp + 8) **
        memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
        (.x1 ↦ᵣ ((base + 32) + 68)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
        (.x20 ↦ᵣ c6New) **
        (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
        ⌜c6New ≠ 0⌝)) := by
  intro bit c6New squareW
  have hPrefix :=
    exp_msb_bit_test_fixed_skip_then_save_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
      e c6 v10 v18 mulTarget squaringMulOff condMulOff skipOff backOff base hc6
  have hPrefixFramed := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
     ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
     ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
     ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
     ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
     ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
     ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
     ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
     ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
     ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
     ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
     (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld))
    (by pcFree) hPrefix
  have hSquare :=
    exp_squaring_call_block_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 bit v11 mulTarget squaringMulOff condMulOff skipOff backOff
      base hbase hmt hd
  have hSquareFramed := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ c6New) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
     (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
     ⌜c6New ≠ 0⌝)
    (by pcFree) hSquare
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hPrefixFramed hSquareFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Fixed x19 reload prefix followed by the squaring-side MUL call. -/
theorem exp_msb_bit_test_fixed_reload_save_then_squaring_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    cpsTripleWithin ((7 + 1) + (17 + 64 + 9)) base (base + 136)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)))
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        (.x5 ↦ᵣ squareW.getLimbN 3) **
        evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
        regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        memOwn evmSp ** memOwn (evmSp + 8) **
        memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
        (.x1 ↦ᵣ ((base + 32) + 68)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ nextLimb) **
        (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
        (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
        ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
        ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))) := by
  intro bit squareW
  have hPrefix :=
    exp_msb_bit_test_fixed_reload_then_save_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
      e c6 v10 v18 ptr nextLimb mulTarget
      squaringMulOff condMulOff skipOff backOff base hc6
  have hPrefixFramed := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
     ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
     ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
     ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
     ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
     ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
     ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
     ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
     ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
     ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
     ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
     (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld))
    (by pcFree) hPrefix
  have hSquare :=
    exp_squaring_call_block_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 bit v11
      mulTarget squaringMulOff condMulOff skipOff backOff base hbase hmt hd
  have hSquareFramed := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x19 ↦ᵣ nextLimb) **
     (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
     ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
     (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
     ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
    (by pcFree) hSquare
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hPrefixFramed hSquareFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Conditional-multiply taken call block lifted to the decomposed fixed
    iteration body plus the external `mul_callable` code. The leading saved-bit
    BEQ remains part of the surrounding conditional path proof. -/
theorem exp_cond_mul_call_block_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    cpsTripleWithin (17 + 64 + 9) (base + 140) (base + 244)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (r * aw).getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp (r * aw) ** evmWordIs (evmSp + 32) (r * aw) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 140) + 68))) := by
  intro r aw
  have hbase' : (base + 140 : Word) &&& 1 = 0 :=
    word_add_even_and_one_eq_zero base (140 : Word) hbase (by simp)
  have h_cond_sub : ∀ a i,
      exp_cond_mul_call_block_code (base + 140) condMulOff a = some i →
      expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff a = some i := by
    intro a i h
    have haddr : (base + 136 : Word) + 4 = base + 140 := by bv_addr
    rw [← haddr] at h
    exact expIterBodyFullMsbSavedBitTwoMulFixedCode_cond_mul_sub
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
      a i (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_call_sub
        (base + 136) condMulOff skipOff a i h)
  have hd_inner : CodeReq.Disjoint
      (exp_cond_mul_call_block_code (base + 140) condMulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with h_exp | h_mul
    · left
      cases hsub : exp_cond_mul_call_block_code (base + 140) condMulOff a with
      | none => rfl
      | some i =>
        have h_ev := h_cond_sub a i hsub
        exact absurd (h_ev.symm.trans h_exp) (by simp)
    · right
      exact h_mul
  have h := EvmAsm.Evm64.exp_cond_mul_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget condMulOff (base + 140) hbase' hmt hd_inner
  have haddr : (base + 140 : Word) + 104 = base + 244 := by bv_addr
  rw [haddr] at h
  have h_cond_sub_union : ∀ a i,
      exp_cond_mul_call_block_code (base + 140) condMulOff a = some i →
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget)) a = some i := by
    intro a i hi
    simp only [CodeReq.union, h_cond_sub a i hi]
  have h_mul_sub_union : ∀ a i, mul_callable_code mulTarget a = some i →
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget)) a = some i := by
    intro a i hi
    rcases hd a with h_iter | h_mul
    · simp only [CodeReq.union, h_iter, hi]
    · rw [hi] at h_mul
      contradiction
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := CodeReq.union_sub h_cond_sub_union h_mul_sub_union)

/-- Saved-bit conditional-multiply BEQ skip-gate lifted to the decomposed
    fixed iteration body. The nonzero branch falls through to the taken
    conditional-multiply call block at `base + 140`. -/
theorem exp_cond_mul_saved_bit_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 : Word) (base target : Word)
    (htarget : (base + 136 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 136)
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 140) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) := by
  have h := EvmAsm.Rv64.beq_spec_within .x18 .x0 skipOff v18 (0 : Word)
    (base + 136)
  rw [htarget] at h
  have hnext : (base + 136 : Word) + 4 = base + 140 := by bv_addr
  rw [hnext] at h
  exact cpsBranchWithin_extend_code
    (h := h)
    (hmono := fun a i hi =>
      expIterBodyFullMsbSavedBitTwoMulFixedCode_cond_mul_sub
        (base := base) (squaringMulOff := squaringMulOff)
        (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
        a i (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_beq_sub
          (base + 136) condMulOff skipOff a i hi))

/-- Saved-bit conditional-multiply BEQ skip-gate lifted to the decomposed
    fixed iteration body plus the external `mul_callable` code. -/
theorem exp_cond_mul_saved_bit_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 base target mulTarget : Word)
    (htarget : (base + 136 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 136)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 140) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) := by
  exact cpsBranchWithin_extend_code
    (h := exp_cond_mul_saved_bit_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      squaringMulOff condMulOff skipOff backOff v18 base target htarget)
    (hmono := fun a i hi => by
      simp only [CodeReq.union, hi])

/-- Fixed x19 no-reload prefix and squaring-side MUL call followed by the
    saved-bit conditional-multiply BEQ. -/
theorem exp_msb_bit_test_fixed_skip_save_squaring_then_cond_mul_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget target : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (htarget : (base + 136 : Word) + signExtend13 skipOff = target)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    cpsBranchWithin (((4 + 1) + (17 + 64 + 9)) + 1) base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)))
      target
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        (.x5 ↦ᵣ squareW.getLimbN 3) **
        evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
        regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        memOwn evmSp ** memOwn (evmSp + 8) **
        memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
        (.x1 ↦ᵣ ((base + 32) + 68)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
        (.x20 ↦ᵣ c6New) **
        (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
        ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝))
      (base + 140)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        (.x5 ↦ᵣ squareW.getLimbN 3) **
        evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
        regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        memOwn evmSp ** memOwn (evmSp + 8) **
        memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
        (.x1 ↦ᵣ ((base + 32) + 68)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
        (.x20 ↦ᵣ c6New) **
        (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
        ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝)) := by
  intro bit c6New squareW
  let rest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ ((base + 32) + 68))
  have hPrefixSquare :=
    exp_msb_bit_test_fixed_skip_save_then_squaring_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget squaringMulOff condMulOff skipOff backOff
      base hc6 hbase hmt hd
  have hBeq :=
    exp_cond_mul_saved_bit_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
      squaringMulOff condMulOff skipOff backOff
      (bit + signExtend12 (0 : BitVec 12)) base target mulTarget htarget
  have hBeqFramed := cpsBranchWithin_frameR
    (rest **
     (.x20 ↦ᵣ c6New) **
     (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
     ⌜c6New ≠ 0⌝)
    (by
      dsimp [rest]
      pcFree)
    hBeq
  have hSeq :
      cpsBranchWithin (((4 + 1) + (17 + 64 + 9)) + 1) base
        ((expIterBodyFullMsbSavedBitTwoMulFixedCode
          base squaringMulOff condMulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        _ target _ (base + 140) _ :=
    cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by
        dsimp [rest, bit, c6New] at hp ⊢
        xperm_hyp hp)
      hPrefixSquare hBeqFramed
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    hSeq

/-- Fixed x19 reload prefix and squaring-side MUL call followed by the
    saved-bit conditional-multiply BEQ. -/
theorem exp_msb_bit_test_fixed_reload_save_squaring_then_cond_mul_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget target : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (htarget : (base + 136 : Word) + signExtend13 skipOff = target)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    cpsBranchWithin (((7 + 1) + (17 + 64 + 9)) + 1) base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)))
      target
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        (.x5 ↦ᵣ squareW.getLimbN 3) **
        evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
        regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        memOwn evmSp ** memOwn (evmSp + 8) **
        memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
        (.x1 ↦ᵣ ((base + 32) + 68)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ nextLimb) **
        (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
        (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
        ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
        ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝))
      (base + 140)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        (.x5 ↦ᵣ squareW.getLimbN 3) **
        evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
        regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        memOwn evmSp ** memOwn (evmSp + 8) **
        memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
        (.x1 ↦ᵣ ((base + 32) + 68)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ nextLimb) **
        (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
        (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
        ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
        ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝)) := by
  intro bit squareW
  let rest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ ((base + 32) + 68))
  have hPrefixSquare :=
    exp_msb_bit_test_fixed_reload_save_then_squaring_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget squaringMulOff condMulOff skipOff backOff
      base hc6 hbase hmt hd
  have hBeq :=
    exp_cond_mul_saved_bit_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
      squaringMulOff condMulOff skipOff backOff
      (bit + signExtend12 (0 : BitVec 12)) base target mulTarget htarget
  have hBeqFramed := cpsBranchWithin_frameR
    (rest **
     (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
     (.x19 ↦ᵣ nextLimb) **
     ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
     (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
     ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
    (by
      dsimp [rest]
      pcFree)
    hBeq
  have hSeq :
      cpsBranchWithin (((7 + 1) + (17 + 64 + 9)) + 1) base
        ((expIterBodyFullMsbSavedBitTwoMulFixedCode
          base squaringMulOff condMulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        _ target _ (base + 140) _ :=
    cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by
        dsimp [rest, bit] at hp ⊢
        xperm_hyp hp)
      hPrefixSquare hBeqFramed
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    hSeq

/-- Loop-back block lifted to the decomposed fixed iteration body. -/
theorem exp_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (c : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base target : Word)
    (htarget : ((base + 244) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 244)
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c ≠ 0⌝)
      (base + 252)
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 244)
    target htarget
  have h_lifted := cpsBranchWithin_extend_code (h := h)
    (hmono := fun a i hi =>
      expIterBodyFullMsbSavedBitTwoMulFixedCode_loop_back_sub
        (base := base) (squaringMulOff := squaringMulOff)
        (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
        a i hi)
  have haddr : (base + 244 : Word) + 8 = base + 252 := by bv_addr
  rw [haddr] at h_lifted
  simpa [expTwoMulIterCountNew] using
    h_lifted

/-- Loop-back block lifted to the decomposed fixed iteration body plus the
    external `mul_callable` code. -/
theorem exp_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
    (c : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base target mulTarget : Word)
    (htarget : ((base + 244) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 244)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c ≠ 0⌝)
      (base + 252)
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c = 0⌝) := by
  exact cpsBranchWithin_extend_code
    (h := exp_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      c squaringMulOff condMulOff skipOff backOff base target htarget)
    (hmono := fun a i hi => by
      simp only [CodeReq.union, hi])

end EvmAsm.Evm64.Exp.Compose
