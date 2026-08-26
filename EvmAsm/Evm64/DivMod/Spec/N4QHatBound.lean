/-
  EvmAsm.Evm64.DivMod.Spec.N4QHatBound

  The n=4 call-path trial-quotient `+2` overestimate in the `n4CallAddbackBeq*`
  names: `(n4CallAddbackBeqQHatV5 a b).toNat ≤ n4CallAddbackBeqQTrue a b + 2`
  (`qTrue = val256 a / val256 b`).  Just the generic
  `divKTrialCallV5QHat_le_val256_div_plus_two_of_call` (#7219) transported through
  `n4CallAddbackBeqQHatV5 = div128Quot_v5 (…) = divKTrialCallV5QHat (…)` (the
  normalized window of `n4CallAddbackBeqQHatV5` is, definitionally, exactly the
  trial window of #7219).

  Feeds the n=4 unconditional-semantic routing (bead `.8.2.2`): with the window
  bridge `n4CallAddbackBeq_window_div_eq_qTrue_of_u4_zero` (#7572), under `U4 = 0`
  this `+2` over `qTrue` becomes a `+2` over the normalized window
  `val256(U0..U3)/BNormVal`, which `mulsubN4_c3_le_two` /
  `isAddbackCarry2Nz_of_overestimate_…` consume.  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5
public import EvmAsm.Evm64.EvmWordArith.DivV5TrialOverestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The n=4 call-path trial quotient overestimates `qTrue` by at most 2. -/
theorem n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (n4CallAddbackBeqQHatV5 a b).toNat ≤ n4CallAddbackBeqQTrue a b + 2 := by
  have h := divKTrialCallV5QHat_le_val256_div_plus_two_of_call
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz hcall
  rw [divKTrialCallV5QHat_eq_div128Quot_v5] at h
  exact h

end EvmAsm.Evm64
