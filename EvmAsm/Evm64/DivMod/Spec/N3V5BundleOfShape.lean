/-
  EvmAsm.Evm64.DivMod.Spec.N3V5BundleOfShape

  `loopN3SelectedBorrowCarryV5_of_shape`: the borrow-conditional carry bundle for
  the n=3 v5 loop, discharged from shape (lane level), over the
  `fullDivN3NormV/U` accessors.  n3 mirror of `loopN2SelectedBorrowCarryV5_of_shape`
  (#7461).  Each obligation (`borrow → carry`) is discharged by the per-regime
  carry-from-shape lemmas (#7522 max / #7523 call), with the shared normalized
  divisor facts from `fullDivN3NormV_shape_facts` (#7525).  Unlike n2, the n=3
  discharge takes the full four-limb window + a general `uTop`, so no
  window-collapse is needed — only the divisor's `v3 = 0`.  The j=0 obligation's
  loop result is `fullDivN3R1V5 bltu_1` (defeq to the bundle's `iterN3V5 bltu_1`
  over `NormV`/`NormU`).  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopLoopDefsBorrowCarry
public import EvmAsm.Evm64.DivMod.Spec.N3V5MaxCarryOfMaxShape
public import EvmAsm.Evm64.DivMod.Spec.N3V5CallCarryOfCallShape
public import EvmAsm.Evm64.DivMod.Spec.N3V5NormVShapeFacts

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The borrow-conditional carry bundle, discharged from shape (lane level). -/
theorem loopN3SelectedBorrowCarryV5_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) (hshift_nz : (clzResult b2).1 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    loopN3SelectedBorrowCarryV5 bltu_1 bltu_0
      (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.1 (fullDivN3NormV b0 b1 b2 b3).2.2.2
      (fullDivN3NormU a0 a1 a2 a3 b2).2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
      0 (fullDivN3NormU a0 a1 a2 a3 b2).1 := by
  obtain ⟨hv2n, hv3z⟩ := fullDivN3NormV_shape_facts b0 b1 b2 b3 hb3z hb2nz hshift_nz
  unfold loopN3SelectedBorrowCarryV5
  -- the bundle's `r1` is definitionally `fullDivN3R1V5 bltu_1`
  rw [show (iterN3V5 bltu_1 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 0) =
      fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 from (fullDivN3R1V5_eq bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).symm]
  refine ⟨?_, ?_⟩
  · -- j=1 obligation, first window
    cases hb : bltu_1 with
    | true =>
      simp only [reduceIte]
      intro hborrow
      rw [hv3z] at hborrow ⊢
      exact n3_call_addback_carry2_nz_of_borrow_of_call_shape _ _ _ _ _ _ _ _ hv2n (hc1 hb) hborrow
    | false =>
      rw [if_neg (by decide)]
      intro hborrow
      rw [hv3z] at hborrow ⊢
      exact isAddbackCarry2NzN3Max_of_borrow_of_max_shape _ _ _ _ _ _ _ _ hv2n (hm1 hb) hborrow
  · -- j=0 obligation, second window (over fullDivN3R1V5 bltu_1)
    cases hb : bltu_0 with
    | true =>
      simp only [reduceIte]
      intro hborrow
      rw [hv3z] at hborrow ⊢
      exact n3_call_addback_carry2_nz_of_borrow_of_call_shape _ _ _ _ _ _ _ _ hv2n (hc0 hb) hborrow
    | false =>
      rw [if_neg (by decide)]
      intro hborrow
      rw [hv3z] at hborrow ⊢
      exact isAddbackCarry2NzN3Max_of_borrow_of_max_shape _ _ _ _ _ _ _ _ hv2n (hm0 hb) hborrow

end EvmAsm.Evm64
