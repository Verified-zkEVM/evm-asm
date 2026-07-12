/- Shared declaration home for the EXP loop-control and saved-bit-with-mul helpers. -/

import EvmAsm.Evm64.Exp.SquaringWithMulShared
import EvmAsm.Evm64.Exp.Compose.SquaringMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.CondMulMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.CondMulSkipBlock
import EvmAsm.Evm64.Exp.CondMulWithMulShared
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall
import EvmAsm.Evm64.Exp.CondMulPairThenMulCall
import EvmAsm.Evm64.Multiply.Callable

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Bit-test block lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_bit_test_evm_exp_with_mul_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e >>> (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e &&& signExtend12 (1 : BitVec 12)))) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_bit_test_evm_exp_spec_within e c v10 mulOff skipOff backOff base)

/-- Loop-back block lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_loop_back_evm_exp_with_mul_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget target : Word)
    (htarget : ((base + 252) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 252)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c ≠ 0⌝)
      (base + 260)
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c = 0⌝) :=
  cpsBranchWithin_extend_evmExpWithMulCode
    (exp_loop_back_evm_exp_spec_within c mulOff skipOff backOff base target htarget)

/-- Squaring-call JAL lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_squaring_square_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 104) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 104) mulTarget
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 108)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_squaring_square_evm_exp_spec_within
      mulOff skipOff backOff vOld base mulTarget hmul)

/-- Conditional-multiply JAL lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_cond_mul_square_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 212) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 212) mulTarget
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 216)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_square_evm_exp_spec_within
      mulOff skipOff backOff vOld base mulTarget hmul)


open EvmAsm.Rv64 (Assertion CodeReq cpsBranchWithin
  cpsBranchWithin_extend_code cpsTripleWithin cpsTripleWithin_extend_code
  memOwn regOwn signExtend12 signExtend13 signExtend21)


open EvmAsm.Rv64

/-- Code required by the corrected saved-bit EXP program plus the external
    `mul_callable` body reached by the squaring and conditional-multiply JALs. -/
abbrev evmExpMsbSavedBitWithMulCode (base mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpMsbSavedBitCode base mulOff skipOff backOff).union
    (mul_callable_code mulTarget)

/-- Corrected saved-bit EXP program with independent JAL offsets for the
    squaring and conditional-multiply call sites, plus the external
    `mul_callable` body both sites target. -/
abbrev evmExpMsbSavedBitTwoMulWithMulCode (base mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpMsbSavedBitTwoMulCode
    base squaringMulOff condMulOff skipOff backOff).union
    (mul_callable_code mulTarget)

/-- Canonical-branch-offset two-MUL saved-bit EXP program plus the external
    `mul_callable` body targeted by both MUL call sites. -/
abbrev evmExpMsbSavedBitTwoMulCanonicalWithMulCode
    (base mulTarget : Word) (squaringMulOff condMulOff : BitVec 21) : CodeReq :=
  (evmExpMsbSavedBitTwoMulCanonicalCode
    base squaringMulOff condMulOff).union
    (mul_callable_code mulTarget)

/-- Canonical two-MUL saved-bit EXP program plus an appended `mul_callable`
    body placed immediately after the 304-byte EXP wrapper. -/
abbrev evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode
    (base : Word) : CodeReq :=
  evmExpMsbSavedBitTwoMulCanonicalWithMulCode
    base (base + 304)
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff

theorem evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_eq
    (base : Word) :
    evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base =
      evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base (base + 304)
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff := rfl

theorem evmExpMsbSavedBitWithMulCode_exp_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        a = some i := by
  unfold evmExpMsbSavedBitWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulWithMulCode_exp_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i,
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub
    {base mulTarget : Word} {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i,
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulCanonicalWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_exp_sub
    {base : Word} :
    ∀ a i,
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) a = some i := by
  unfold evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode
  exact evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub

theorem evmExpMsbSavedBitWithMulCode_mul_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        a = some i := by
  unfold evmExpMsbSavedBitWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

theorem evmExpMsbSavedBitTwoMulWithMulCode_mul_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

theorem evmExpMsbSavedBitTwoMulCanonicalWithMulCode_mul_sub
    {base mulTarget : Word} {squaringMulOff condMulOff : BitVec 21}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulCanonicalWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

/-- The canonical two-MUL saved-bit EXP wrapper is disjoint from a
    `mul_callable` body appended immediately after the 304-byte wrapper. -/
theorem evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul
    (base : Word) :
    CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff)
      (mul_callable_code (base + 304)) := by
  rw [evmExpMsbSavedBitTwoMulCanonicalCode_eq_ofProg,
    mul_callable_code_eq_ofProg]
  exact CodeReq.ofProg_disjoint_range_len
    base
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_canonical
      EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff)
    76
    (base + 304)
    EvmAsm.Evm64.mul_callable
    64
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_canonical_length
      EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff)
    EvmAsm.Evm64.mul_callable_length
    (fun k1 k2 hk1 hk2 =>
      EvmAsm.Evm64.Exp.AddrNorm.evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_disjoint_addr
        base hk1 hk2)

theorem evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_mul_sub
    {base : Word} :
    ∀ a i, (mul_callable_code (base + 304)) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) a = some i := by
  unfold evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode
  exact evmExpMsbSavedBitTwoMulCanonicalWithMulCode_mul_sub
    (evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul base)

/-- Lift a corrected saved-bit top-level EXP spec into the combined EXP+MUL
    code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitWithMulCode_exp_sub) h

/-- Lift a two-offset corrected saved-bit EXP spec into the combined EXP+MUL
    code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulWithMulCode_exp_sub) h

/-- Lift a canonical two-offset saved-bit EXP spec into the combined EXP+MUL
    code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulCanonicalWithMulCode
    {nSteps : Nat} {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub) h

/-- Lift a canonical two-MUL saved-bit EXP spec into the named appended-MUL
    code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode
    {nSteps : Nat} {entry exit_ base : Word} {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_exp_sub) h

/-- Lift a corrected saved-bit top-level EXP branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitWithMulCode {nSteps : Nat}
    {entry base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word}
    {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitWithMulCode_exp_sub) h

/-- Lift a two-offset corrected saved-bit EXP branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode {nSteps : Nat}
    {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word}
    {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulWithMulCode_exp_sub) h

/-- Lift a canonical two-offset saved-bit EXP branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitTwoMulCanonicalWithMulCode
    {nSteps : Nat} {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word}
    {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub) h

/-- Lift a canonical two-MUL saved-bit EXP branch spec into the named
    appended-MUL code bundle. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode
    {nSteps : Nat} {entry base : Word}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word}
    {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_exp_sub) h

/-- Lift a corrected saved-bit top-level EXP N-branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsNBranchWithin_extend_evmExpMsbSavedBitWithMulCode
    {nSteps : Nat} {entry base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      P exits :=
  cpsNBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitWithMulCode_exp_sub) h

/-- Lift a two-offset corrected saved-bit EXP N-branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsNBranchWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    {nSteps : Nat} {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P exits :=
  cpsNBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulWithMulCode_exp_sub) h

/-- Lift a canonical two-offset saved-bit EXP N-branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsNBranchWithin_extend_evmExpMsbSavedBitTwoMulCanonicalWithMulCode
    {nSteps : Nat} {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff)
      P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) P exits :=
  cpsNBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub) h

/-- Lift a canonical two-MUL saved-bit EXP N-branch spec into the named
    appended-MUL code bundle. -/
theorem cpsNBranchWithin_extend_evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode
    {nSteps : Nat} {entry base : Word}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff)
      P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) P exits :=
  cpsNBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_exp_sub) h

/-- Lift a multiply-callable spec into the two-MUL saved-bit EXP+MUL code
    bundle. -/
theorem cpsTripleWithin_extend_mulCallable_evmExpMsbSavedBitTwoMulWithMulCode
    {nSteps : Nat} {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget))
    (h : cpsTripleWithin nSteps entry exit_
      (mul_callable_code mulTarget) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulWithMulCode_mul_sub
      (base := base) (mulTarget := mulTarget)
      (squaringMulOff := squaringMulOff) (condMulOff := condMulOff)
      (skipOff := skipOff) (backOff := backOff) hd)
    h

/-- Lift a multiply-callable spec into the canonical two-MUL saved-bit EXP+MUL
    code bundle. -/
theorem cpsTripleWithin_extend_mulCallable_evmExpMsbSavedBitTwoMulCanonicalWithMulCode
    {nSteps : Nat} {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {P Q : Assertion}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff)
      (mul_callable_code mulTarget))
    (h : cpsTripleWithin nSteps entry exit_
      (mul_callable_code mulTarget) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulCanonicalWithMulCode_mul_sub
      (base := base) (mulTarget := mulTarget)
      (squaringMulOff := squaringMulOff) (condMulOff := condMulOff) hd)
    h

/-- Lift an appended `mul_callable` spec into the named appended-MUL code
    bundle. -/
theorem cpsTripleWithin_extend_mulCallable_evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode
    {nSteps : Nat} {entry exit_ base : Word} {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (mul_callable_code (base + 304)) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_mul_sub)
    h

theorem evmExpMsbSavedBitTwoMulWithMulCode_block_subs {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) := by
  rcases evmExpMsbSavedBitTwoMulCode_block_subs
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff) with
    ⟨h_prologue, h_pointer_advance, h_iter, h_pointer_restore, h_epilogue⟩
  exact
    ⟨fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i (h_prologue a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
          (h_pointer_advance a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i (h_iter a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
          (h_pointer_restore a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i (h_epilogue a i h),
     evmExpMsbSavedBitTwoMulWithMulCode_mul_sub hd⟩

theorem evmExpMsbSavedBitTwoMulCanonicalWithMulCode_block_subs
    {base mulTarget : Word} {squaringMulOff condMulOff : BitVec 21}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff)
      (mul_callable_code mulTarget)) :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) := by
  rcases evmExpMsbSavedBitTwoMulCanonicalCode_block_subs
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) with
    ⟨h_prologue, h_pointer_advance, h_iter, h_pointer_restore, h_epilogue⟩
  exact
    ⟨fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_prologue a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_pointer_advance a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_iter a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_pointer_restore a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_epilogue a i h),
     evmExpMsbSavedBitTwoMulCanonicalWithMulCode_mul_sub hd⟩

/-- Bundled block subsumptions for the canonical two-MUL saved-bit EXP wrapper
    with `mul_callable` appended immediately after the 304-byte wrapper. -/
theorem evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_block_subs
    {base : Word} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) a = some i) ∧
    (∀ a i, (mul_callable_code (base + 304)) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base) a = some i) :=
  evmExpMsbSavedBitTwoMulCanonicalWithMulCode_block_subs
    (base := base) (mulTarget := base + 304)
    (squaringMulOff := EvmAsm.Evm64.canonicalExpSquaringMulOff)
    (condMulOff := EvmAsm.Evm64.canonicalExpCondMulOff)
    (evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul base)

/-- Pointer advance lifted to the two-MUL saved-bit EXP+MUL code bundle. -/
theorem exp_loop_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (vOld : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 24) (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    (exp_loop_pointer_advance_evm_exp_msb_saved_bit_two_mul_spec_within
      vOld squaringMulOff condMulOff skipOff backOff base)

/-- Pointer restore lifted to the two-MUL saved-bit EXP+MUL code bundle. -/
theorem exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (vOld : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 264) (base + 268)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    (exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_spec_within
      vOld squaringMulOff condMulOff skipOff backOff base)

/-- EXP prologue lifted to the two-MUL saved-bit EXP+MUL code bundle. -/
theorem exp_prologue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp cOld tOld m0 m1 m2 m3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 6 base (base + 24)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord)) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    (exp_prologue_evm_exp_msb_saved_bit_two_mul_spec_within
      sp cOld tOld m0 m1 m2 m3
      squaringMulOff condMulOff skipOff backOff base)

/-- EXP epilogue lifted to the two-MUL saved-bit EXP+MUL code bundle. -/
theorem exp_epilogue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 9 (base + 268) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    (exp_epilogue_evm_exp_msb_saved_bit_two_mul_spec_within
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3
      squaringMulOff condMulOff skipOff backOff base)

end EvmAsm.Evm64.Exp.Compose
