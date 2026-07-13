/- Shared declaration home for the n=2 V5 shape bundle and iteration bridges. -/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopDispatchShared
import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared
import EvmAsm.Evm64.DivMod.Spec.N2V5NormVShapeFacts
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDefsBorrowCarry

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The unified loop iteration equals the families iteration. -/
theorem loopN2IterSelectedV5_eq_iterN2V5 (bltu : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopN2IterSelectedV5 bltu v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterN2V5 bltu v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp only [loopN2IterSelectedV5, iterN2V5]


open EvmAsm.Rv64

/-- The bundle's j=2 iteration (over NormV/U) equals the families' `fullDivN2R2V5`. -/
theorem loopN2IterSelectedV5_normUV_eq_R2V5
    (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    loopN2IterSelectedV5 bltu_2
      (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0
      = fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 := by
  simp only [loopN2IterSelectedV5_eq_iterN2V5, fullDivN2R2V5]

/-- The bundle's j=1 iteration (over NormV/U and the R2 outputs) equals the
    families' `fullDivN2R1V5`. -/
theorem loopN2IterSelectedV5_normUV_eq_R1V5
    (bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    loopN2IterSelectedV5 bltu_1
      (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
      (fullDivN2NormU a0 a1 a2 a3 b1).2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      = fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 := by
  simp only [loopN2IterSelectedV5_eq_iterN2V5, fullDivN2R1V5]


open EvmWord EvmAsm.Rv64

/-- The borrow-conditional carry bundle, discharged from shape (lane level). -/
theorem loopN2SelectedBorrowCarryV5_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    loopN2SelectedBorrowCarryV5 bltu_2 bltu_1 bltu_0
      (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0
      (fullDivN2NormU a0 a1 a2 a3 b1).2.1 (fullDivN2NormU a0 a1 a2 a3 b1).1 := by
  unfold loopN2SelectedBorrowCarryV5
  simp only [loopN2IterSelectedV5_normUV_eq_R2V5, loopN2IterSelectedV5_normUV_eq_R1V5]
  obtain ⟨hv1n, hv2z', hv3z'⟩ := fullDivN2NormV_shape_facts b0 b1 b2 b3 hb2z hb3z hb1nz hshift_nz
  have hfwv := fullDivN2_first_window_valid a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z hshift_nz hb1nz
  obtain ⟨hR2c1, hR2c2⟩ := fullDivN2R2V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2
    hb2z hb3z hshift_nz hb1nz hfwv hc2 hm2
  have hR2 := fullDivN2R2V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2
    hb2z hb3z hshift_nz hb1nz hfwv hc2 hm2
  have hR1valid := n2_next_window_lt (fullDivN2NormU a0 a1 a2 a3 b1).2.1
    (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 _ hR2.2
  obtain ⟨hR1c1, hR1c2⟩ := fullDivN2R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1
    hb2z hb3z hshift_nz hb1nz hR2c1 hR2c2 hR1valid hc1 hm1
  refine ⟨?_, ?_, ?_⟩
  · rw [hv2z', hv3z']
    cases hb : bltu_2 with
    | true =>
      intro hborrow
      have hcall : (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat <
          (fullDivN2NormV b0 b1 b2 b3).2.1.toNat := by
        have := hc2 hb; rw [BitVec.ult] at this; exact of_decide_eq_true this
      exact callAddbackCarry2NzV5_of_borrow_of_call_shape _ _ _ _ _ 0 hv1n hcall hborrow
    | false =>
      intro hborrow
      exact isAddbackCarry2NzN2Max_of_borrow_of_max_shape _ _ _ _ _ 0 hv1n (hm2 hb) hborrow
  · rw [hv2z', hv3z', hR2c1, hR2c2]
    cases hb : bltu_1 with
    | true =>
      intro hborrow
      have hcall : (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat <
          (fullDivN2NormV b0 b1 b2 b3).2.1.toNat := by
        have := hc1 hb; rw [BitVec.ult] at this; exact of_decide_eq_true this
      exact callAddbackCarry2NzV5_of_borrow_of_call_shape _ _ _ _ _ 0 hv1n hcall hborrow
    | false =>
      intro hborrow
      exact isAddbackCarry2NzN2Max_of_borrow_of_max_shape _ _ _ _ _ 0 hv1n (hm1 hb) hborrow
  · rw [hv2z', hv3z', hR1c1, hR1c2]
    cases hb : bltu_0 with
    | true =>
      intro hborrow
      have hcall : (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat <
          (fullDivN2NormV b0 b1 b2 b3).2.1.toNat := by
        have := hc0 hb; rw [BitVec.ult] at this; exact of_decide_eq_true this
      exact callAddbackCarry2NzV5_of_borrow_of_call_shape _ _ _ _ _ 0 hv1n hcall hborrow
    | false =>
      intro hborrow
      exact isAddbackCarry2NzN2Max_of_borrow_of_max_shape _ _ _ _ _ 0 hv1n (hm0 hb) hborrow

end EvmAsm.Evm64
