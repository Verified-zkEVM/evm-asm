/-
  EvmAsm.Evm64.DivMod.Spec.N4QHatOvershoot

  The n=4 v5 call trial quotient overshoots the TRUE quotient by at most 2, and
  never underestimates — UNCONDITIONALLY on the call path (no `U4 = 0`):

    `qTrue ≤ qHatV5  ∧  qHatV5 - qTrue ≤ 2`   (equivalently `qTrue ≤ qHatV5 ≤ qTrue + 2`).

  The lower half `qTrue ≤ qHatV5` composes the val256→top-window Knuth bridge
  `q_true_triple_bridge_to_val256_norm` (`qTrue ≤ (U4·2^64+U3)/B3'`) with the
  top-window trial lower bound `n4CallAddbackBeqQHatV5_ge_128_div_of_call`
  (`(U4·2^64+U3)/B3' ≤ qHatV5`).  The upper half is the existing unconditional
  `+2` overestimate `n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call` (#7573).

  Consequence: the corrective addback count `qHatV5 - qTrue ≤ 2` for ANY `U4`, so
  the double-addback (carry2) path is always sufficient — the algorithmic
  foundation for a `U4`-general n=4 addback semantic (replacing the `U4 = 0`
  single-addback chain).  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5TopBound
public import EvmAsm.Evm64.DivMod.Spec.N4QHatBound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The n=4 v5 call trial quotient never underestimates the true quotient:
    `qTrue ≤ qHatV5`, unconditionally on the call path. -/
theorem n4CallAddbackBeqQHatV5_ge_qTrue {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqQTrue a b ≤ (n4CallAddbackBeqQHatV5 a b).toNat := by
  have h_top := n4CallAddbackBeqQHatV5_ge_128_div_of_call hb3nz hcall
  have h_bridge := q_true_triple_bridge_to_val256_norm
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hshift_nz hb3nz
  simp only [] at h_bridge
  rw [n4CallAddbackBeqQTrue_unfold]
  exact le_trans h_bridge h_top

/-- The n=4 v5 call trial quotient overshoots the true quotient by at most 2:
    `qHatV5 - qTrue ≤ 2`, unconditionally on the call path.  Hence the double
    addback always suffices to correct it. -/
theorem n4CallAddbackBeqQHatV5_sub_qTrue_le_two {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (n4CallAddbackBeqQHatV5 a b).toNat - n4CallAddbackBeqQTrue a b ≤ 2 := by
  have hle := n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call hb3nz hshift_nz hcall
  omega

end EvmAsm.Evm64
