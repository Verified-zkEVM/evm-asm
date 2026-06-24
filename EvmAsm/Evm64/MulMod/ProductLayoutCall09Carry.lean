import EvmAsm.Evm64.MulMod.ProductLayoutCall05Carry

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- The ninth call's offset-128 cell is the low word of the column-3 carry. -/
theorem mulModProductLayoutCall09P128_toNat_eq_c4_from_chain (a b : EvmWord) :
    let a0 := a.getLimbN 0
    let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2
    let a3 := a.getLimbN 3
    let b0 := b.getLimbN 0
    let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2
    let b3 := b.getLimbN 3
    let d0 := a0.toNat * b0.toNat
    let d1 := a0.toNat * b1.toNat + a1.toNat * b0.toNat
    let d2 := a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat
    let d3 := a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat + a3.toNat * b0.toNat
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    (mulModProductLayoutCall09P128 a b).toNat = c4 % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall09P128_eq_expanded]
  simp only [BitVec.toNat_add, mulModProductLayoutCarryRight_toNat,
    mulModProductLayoutCall05P120_toNat_eq_limb2CarryLow,
    mulModProductLayoutCall05P128_toNat_eq_limb2CarryHigh,
    mulModProductLayoutCall06P120_eq_add,
    mulModProductLayoutCall07P120_eq_add,
    mulModProductLayoutCall08P120_eq_add,
    mulModAddPartialLoProduct]
  rw [mulModProductLayoutCarryChainHigh4ModEq]
  all_goals
    have h00 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 0)
    have h10 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)
    have h20 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 0)
    have h30 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 0)
    have h01 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)
    have h11 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 1)
    have h21 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 1)
    have h02 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 2)
    have h12 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 2)
    have h03 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 3)
    norm_num at h00 h10 h20 h30 h01 h11 h21 h02 h12 h03 ⊢
    omega


/-- Public spelling of the call09 offset-128 limb-3 carry theorem. -/
theorem mulModProductLayoutCall09P128_toNat_eq_limb3Carry (a b : EvmWord) :
    let a0 := a.getLimbN 0
    let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2
    let a3 := a.getLimbN 3
    let b0 := b.getLimbN 0
    let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2
    let b3 := b.getLimbN 3
    let d0 := a0.toNat * b0.toNat
    let d1 := a0.toNat * b1.toNat + a1.toNat * b0.toNat
    let d2 := a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat
    let d3 := a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat + a3.toNat * b0.toNat
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    (mulModProductLayoutCall09P128 a b).toNat = c4 % 2 ^ 64 := by
  exact mulModProductLayoutCall09P128_toNat_eq_c4_from_chain a b

end EvmAsm.Evm64
