/-
  EvmAsm.Evm64.DivMod.Spec.N4Carry2OfNamed

  Reverse of `n4CallAddbackBeqCarry2Nz_of_runtimeV5`: from the raw double-addback
  progress predicate over the normalized marker limbs (in the `n4CallAddbackBeq*`
  names) back to the packaged runtime predicate `isAddbackCarry2NzN4CallV5Evm a b`.

  This is the direction the n=4 `h_carry2` DISCHARGE needs: given the generic
  `isAddbackCarry2Nz (n4CallAddbackBeqQHatV5 a b) (B0Prime b) … (U4 a b)` — which
  `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` produces from the `+2`
  over the normalized window (#7574, under `U4 = 0`), the divisor `≠ 0`, and the
  `c3 = 1`-of-carry-zero invariant — conclude the packaged `isAddbackCarry2NzN4CallV5Evm`
  hypothesis of the n=4 v5 semantic.  Mirrors the forward proof (`unfold` of the
  predicate / named defs + the `divKTrialCallV5QHat = div128Quot_v5` bridge).
  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The packaged runtime carry-2 predicate from its raw normalized-limb form. -/
theorem isAddbackCarry2NzN4CallV5Evm_of_named {a b : EvmWord}
    (h : isAddbackCarry2Nz
      (n4CallAddbackBeqQHatV5 a b)
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)) :
    isAddbackCarry2NzN4CallV5Evm a b := by
  rw [n4CallAddbackBeqQHatV5_eq_normalized] at h
  unfold isAddbackCarry2Nz at h
  unfold n4CallAddbackBeqB0Prime n4CallAddbackBeqB1Prime
    n4CallAddbackBeqB2Prime n4CallAddbackBeqB3Prime
    n4CallAddbackBeqU0 n4CallAddbackBeqU1 n4CallAddbackBeqU2
    n4CallAddbackBeqU3 n4CallAddbackBeqU4 n4CallAddbackBeqShift
    n4CallAddbackBeqAntiShift at h
  rw [isAddbackCarry2NzN4CallV5Evm_def]
  unfold isAddbackCarry2NzN4CallV5Ab loopBodyN4CallAddbackCarry2NzV5
  simp_rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  simpa using h

end EvmAsm.Evm64
