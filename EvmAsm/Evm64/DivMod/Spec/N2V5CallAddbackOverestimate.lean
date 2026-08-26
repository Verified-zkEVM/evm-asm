/-
  EvmAsm.Evm64.DivMod.Spec.N2V5CallAddbackOverestimate

  v5 n=2 call-digit carry: `callAddbackCarry2NzV5` from the +2 Knuth overestimate
  + the BLT c3 invariant.  v5 counterpart of
  `loopBodyN2CallAddbackCarry2NzV4_of_overestimate_c3`
  (DivBltBridgeSpecializations) — `callAddbackCarry2NzV5` is definitionally
  `isAddbackCarry2Nz (divKTrialCallV5QHat u2 u1 v1) …`, so the qHat-abstract
  generic lemma `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` applies
  directly with the v5 trial.  (The v4 abbrev `MulsubBltC3OneOfCarryZero` is
  hardcoded to `divKTrialCallV4QHat`, so the c3 invariant is stated here in raw
  form over `divKTrialCallV5QHat` to avoid a v4-vs-v5 trial reconciliation.)
  This is the call-digit half of the n=2 carry-from-shape discharge (the
  max-digit half is `isAddbackCarry2NzN2Max_of_not_ult_c3_one_of_carry_zero`).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopFinalPostCCC
public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- v5 call-digit carry-2-nonzero from the +2 overestimate and the BLT c3
    invariant (raw form over the v5 trial `divKTrialCallV5QHat u2 u1 v1`). -/
theorem callAddbackCarry2NzV5_of_overestimate_c3
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV5QHat u2 u1 v1).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hc3 :
      addbackN4_carry
          (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          v0 v1 v2 v3 = 0 →
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1) :
    callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  rw [callAddbackCarry2NzV5_unfold]
  exact isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
    (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hq_over hc3

end EvmAsm.Evm64
