/-
  EvmAsm.Evm64.EvmWordArith.SkipBorrowExtract

  Extracts the Nat-level inequality `c3_n.toNat ≤ uTop.toNat` from the
  runtime skip-borrow predicate `isSkipBorrowN4Max`. This fact feeds
  directly into the MOD stack spec's post reshape via
  `output_slot_to_evmWordIs_mod_n4_max_skip_denorm`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4
import EvmAsm.Evm64.EvmWordArith.Common

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

/-- From the Word-level skip-borrow predicate (`1` if `uTop < c3_n` else `0`,
    equal to `0`), extract the Nat-level inequality `c3_n.toNat ≤ uTop.toNat`. -/
theorem c3_le_u_top_of_skip_borrow (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (h : isSkipBorrowN4Max a0 a1 a2 a3 b0 b1 b2 b3) :
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
    (mulsubN4 (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat ≤
    u4.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0
  unfold isSkipBorrowN4Max at h
  simp only [] at h
  by_cases hlt : BitVec.ult u4 (mulsubN4_c3 (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3)
  · -- If u4 < c3_n, the ite returns 1, contradicting h : ite = 0.
    rw [if_pos hlt] at h
    exact absurd h (by decide)
  · -- Otherwise, ¬ (u4 < c3_n), i.e., c3_n ≤ u4.
    rw [ult_iff] at hlt
    unfold mulsubN4_c3 at hlt
    omega

end EvmWord

end EvmAsm.Evm64
