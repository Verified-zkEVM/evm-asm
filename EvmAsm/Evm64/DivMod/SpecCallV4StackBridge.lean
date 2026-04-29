/-
  EvmAsm.Evm64.DivMod.SpecCallV4StackBridge

  Bridges between v4 closure proofs (in `SpecCallV4.lean`) and the
  EVM-stack-level specs (in `SpecCallAddbackBeq.lean`). Provides v4
  mirrors of bridges originally written for v1 (`div128Quot`).

  Companion to `SpecCallV4.lean` (the v4 closure proofs) and
  `SpecCallAddbackBeq.lean` (the v1 stack specs).
-/

import EvmAsm.Evm64.DivMod.SpecCallV4

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **v4 mirror of `n4_call_addback_beq_div_mod_getLimbN`**: under
    `n4CallAddbackBeqSemanticHolds_v4` (the v4 semantic-holds, which uses
    `div128Quot_v4` for the trial quotient), the post-addback corrected
    quotient `q_out` equals `(EvmWord.div a b).getLimbN 0`, and the
    upper three limbs of `EvmWord.div a b` are all zero.

    Same proof shape as the v1 version — only uses `div128Quot_v4`
    instead of `div128Quot`. The final equality `q_target = EvmWord.div a b`
    is established via `BitVec.eq_of_toNat_eq` on the toNat values. -/
theorem n4_call_addback_beq_div_mod_getLimbN_v4 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHolds_v4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_out : Word :=
      if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
      else qHat + signExtend12 4095
    (EvmWord.div a b).getLimbN 0 = q_out ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_out
  rw [n4CallAddbackBeqSemanticHolds_v4_def] at hsem
  change q_out.toNat = val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) at hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val] at hsem
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hbnz]
    exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => q_out | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = q_out.toNat := by
    simp [q_target, EvmWord.fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
