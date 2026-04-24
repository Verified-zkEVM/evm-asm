/-
  EvmAsm.Evm64.EvmWordArith.AddbackBorrowExtract

  Extracts the Nat-level strict inequality `u_top.toNat < c3_n.toNat` from the
  runtime addback-borrow predicate `isAddbackBorrowN4Max`. Parallel to
  `SkipBorrowExtract.lean` — that file extracts `c3_n ≤ u_top` from the
  skip-borrow; this one extracts the complementary inequality from the
  addback-borrow (the addback path fires exactly when u_top < c3_n).

  Feeds into the normalized-vs-un-normalized carry bridge (Lemma A of the
  Phase F plan) for the max+addback stack spec, Issue #61.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4Beq
import EvmAsm.Evm64.EvmWordArith.Common

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

/-- From the Word-level addback-borrow predicate (`1` if `u_top < c3_n` else `0`,
    equal to `1`, i.e., `≠ 0`), extract the Nat-level strict inequality
    `u_top.toNat < c3_n.toNat`. Complement of `c3_le_u_top_of_skip_borrow`
    which extracts the opposite inequality from `isSkipBorrowN4Max`. -/
theorem u_top_lt_c3_of_addback_borrow (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (h : isAddbackBorrowN4Max a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    u4.toNat <
    (mulsubN4 (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0
  unfold isAddbackBorrowN4Max at h
  simp only [] at h
  by_cases hlt : BitVec.ult u4 (mulsubN4_c3 (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3)
  · -- If u4 < c3_n, the ite returns 1 ≠ 0, matching h. Extract the inequality.
    rw [ult_iff] at hlt
    unfold mulsubN4_c3 at hlt
    exact hlt
  · -- Otherwise, ite returns 0, contradicting h : ite ≠ 0.
    rw [if_neg hlt] at h
    exact absurd rfl h

/-- Call-trial variant of `u_top_lt_c3_of_addback_borrow`. From the Word-level
    addback-borrow predicate with `qHat = div128Quot u4 u3 b3'` (call trial),
    extract the Nat-level strict inequality `u_top.toNat < c3_n.toNat`.
    Mirror of the max-trial version for the call-addback BEQ stack spec. -/
theorem u_top_lt_c3_of_addback_borrow_call (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (h : isAddbackBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    let qHat := div128Quot u4 u3 b3'
    u4.toNat <
    (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  unfold isAddbackBorrowN4Call at h
  simp only [] at h
  by_cases hlt : BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
  · rw [ult_iff] at hlt
    unfold mulsubN4_c3 at hlt
    exact hlt
  · rw [if_neg hlt] at h
    exact absurd rfl h

end EvmWord

end EvmAsm.Evm64
