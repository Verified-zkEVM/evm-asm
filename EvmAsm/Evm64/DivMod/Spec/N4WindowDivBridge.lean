/-
  EvmAsm.Evm64.DivMod.Spec.N4WindowDivBridge

  The n=4 window-vs-original quotient bridge under `U4 = 0`: when the normalized
  five-limb dividend has zero overflow limb (`n4CallAddbackBeqU4 a b = 0`), the
  normalized-window Euclidean quotient `val256(U0..U3) / val256(B0..B3Prime)`
  collapses to the original unnormalized quotient `n4CallAddbackBeqQTrue a b`
  (`= val256 a / val256 b`).

  This is the clean math link the n=4 unconditional-semantic routing (bead
  `.8.2.2`) needs: the `hq_over` hypothesis of
  `n4CallAddbackBeqSemanticHoldsV5_of_runtime_conditions_legacy` is stated over the
  normalized WINDOW `val256(U0..U3)/val256(B0..B3Prime)`, while the proven trial
  bounds (`#7201` top-limb `+1`, `#7219` val256 `+2`) are over the ORIGINAL
  `val256 a / val256 b = qTrue`.  Under `U4 = 0` (which the dispatcher routing
  establishes on the call/addback path) the two domains coincide, so this lemma
  lets those original-domain bounds be transported to the window `hq_over`.

  Follows immediately from the proven `n4CallAddbackBeqNormalized_div_eq_qTrueV5`
  (`UNormVal / BNormVal = qTrue`) by collapsing the `U4·2^256` overflow term of
  `UNormVal`.  Bead `evm-asm-wbc4i.8.2.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Abstract collapse: a five-limb dividend value `W + u4·2^256` with zero overflow
    limb (`u4 = 0`) has the same Euclidean quotient as its low four limbs `W`.  Kept
    fully abstract (the window value `W` is an opaque `Nat` variable) so the kernel
    never evaluates the huge `val256`-of-normalized-limbs term it is instantiated to. -/
private theorem div_collapse_of_zero_overflow {W u4 BN q : Nat}
    (h : (W + u4 * 2 ^ 256) / BN = q) (hu4 : u4 = 0) : W / BN = q := by
  subst hu4; simpa using h

/-- Under `U4 = 0`, the normalized-window quotient equals the original `qTrue`.
    Phrased with the opaque `n4CallAddbackBeqBNormVal b` denominator (which is by
    definition `val256 (B0Prime b) .. (B3Prime b)`, the `hq_over` denominator).
    The abstract `div_collapse_of_zero_overflow` keeps the huge `val256(U0..U3)`
    window value opaque, sidestepping the kernel deep-recursion the n=4 normalized
    limb terms otherwise trigger. -/
theorem n4CallAddbackBeq_window_div_eq_qTrue_of_u4_zero {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hu4 : (n4CallAddbackBeqU4 a b).toNat = 0) :
    EvmWord.val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) /
      n4CallAddbackBeqBNormVal b
      = n4CallAddbackBeqQTrue a b :=
  div_collapse_of_zero_overflow
    (n4CallAddbackBeqNormalized_div_eq_qTrueV5 (a := a) (b := b) hshift_nz) hu4

end EvmAsm.Evm64
