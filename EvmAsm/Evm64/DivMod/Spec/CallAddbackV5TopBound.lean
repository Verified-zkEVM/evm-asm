/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackV5TopBound

  Top-limb (128÷64) upper bound for the v5 n=4 call+addback trial quotient:
  `qHatV5 ≤ (u4·2^64 + u3) / b3' + 1`.

  This is the v5 analog of `n4CallAddbackBeqQHatV4_le_floor_plus_one_of_call_*`
  (CallAddbackRuntime.lean), but it is UNCONDITIONAL — V5.4.5
  (`div128Quot_v5_le_q_true_plus_one`) holds with only `vTop ≥ 2^63` and
  `uHi < vTop`, so the v4 `rhatdd_hi_zero` / extra side conditions are gone.

  It is the first half of the bridge toward the val256-level `hq_over` bound
  used by the legacy `n4CallAddbackBeqSemanticHoldsV5_of_runtime_conditions_legacy`
  helper before the U4-general wrapper (bead `evm-asm-wbc4i.8.2.2`). The remaining (harder) half is
  the top-limb → val256 quotient bridge.

  Bead `evm-asm-wbc4i.8.2.2.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Top-limb (128÷64) `+1` upper bound for the v5 marker trial quotient on the
    call path: `qHatV5 ≤ (u4·2^64 + u3) / b3' + 1`. Unconditional version of the
    v4 `n4CallAddbackBeqQHatV4_le_floor_plus_one_of_call_rhatdd_hi_zero`
    (no `rhatdd_hi_zero` premise — V5.4.5 is unconditional). -/
theorem n4CallAddbackBeqQHatV5_le_128_div_plus_one_of_call {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (n4CallAddbackBeqQHatV5 a b).toNat ≤
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat + 1 := by
  rw [n4CallAddbackBeqQHatV5_eq_normalized]
  have hu4_lt_b3prime :
      (n4CallAddbackBeqU4 a b).toNat < (n4CallAddbackBeqB3Prime b).toNat := by
    have h_decomp := n4CallAddbackBeqU4_lt_vTop_of_call hcall
    rw [div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
    simpa [divKTrialCallV4DHi, divKTrialCallV4DLo] using h_decomp
  exact div128Quot_v5_le_q_true_plus_one
    (n4CallAddbackBeqU4 a b) (n4CallAddbackBeqU3 a b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqB3Prime_ge_pow63 hb3nz) hu4_lt_b3prime

/-- Top-limb (128÷64) lower bound for the v5 marker trial quotient on the call
    path: `(u4·2^64 + u3) / b3' ≤ qHatV5`. Companion to the `+1` upper bound;
    uses V5.5.3 (`div128Quot_v5_ge_q_true`). Together they pin `qHatV5` to
    `{(u4·2^64+u3)/b3', that + 1}` — the input to the val256 `hq_over` bridge
    (bead `evm-asm-wbc4i.8.2.2`). -/
theorem n4CallAddbackBeqQHatV5_ge_128_div_of_call {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
        (n4CallAddbackBeqU3 a b).toNat) /
      (n4CallAddbackBeqB3Prime b).toNat ≤
      (n4CallAddbackBeqQHatV5 a b).toNat := by
  rw [n4CallAddbackBeqQHatV5_eq_normalized]
  have hu4_lt_b3prime :
      (n4CallAddbackBeqU4 a b).toNat < (n4CallAddbackBeqB3Prime b).toNat := by
    have h_decomp := n4CallAddbackBeqU4_lt_vTop_of_call hcall
    rw [div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
    simpa [divKTrialCallV4DHi, divKTrialCallV4DLo] using h_decomp
  exact div128Quot_v5_ge_q_true
    (n4CallAddbackBeqU4 a b) (n4CallAddbackBeqU3 a b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqB3Prime_ge_pow63 hb3nz) hu4_lt_b3prime

end EvmAsm.Evm64
