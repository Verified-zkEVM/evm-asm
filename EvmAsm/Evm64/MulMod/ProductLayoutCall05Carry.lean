import EvmAsm.Evm64.MulMod.ProductLayoutPublicAlgebra

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra



/-- Carry out of a two-word addition, with operands in source order. -/
theorem mulModProductLayoutCarry_toNat (x y : Word) :
    (if BitVec.ult (x + y) x then (1 : Word) else 0).toNat =
      (x.toNat + y.toNat) / 2 ^ 64 := by
  rw [show x + y = y + x by rw [BitVec.add_comm]]
  rw [EvmWord.carry_toNat (x := y) (y := x)]
  omega

/-- Carry out of a two-word addition, compared against the right operand. -/
theorem mulModProductLayoutCarryRight_toNat (x y : Word) :
    (if BitVec.ult (x + y) y then (1 : Word) else 0).toNat =
      (x.toNat + y.toNat) / 2 ^ 64 := by
  rw [EvmWord.carry_toNat (x := x) (y := y)]

/-- Carry out of a two-word addition, with operands in source order. -/
theorem mulModProductLayoutCarryEqTrue_toNat (x y : Word) :
    (if (x + y).ult x = true then (1 : Word) else 0).toNat =
      (x.toNat + y.toNat) / 2 ^ 64 := by
  rw [show x + y = y + x by rw [BitVec.add_comm]]
  rw [EvmWord.carry_toNat (x := y) (y := x)]
  omega

/-- Carry out of a two-word addition, compared against the right operand. -/
theorem mulModProductLayoutCarryRightEqTrue_toNat (x y : Word) :
    (if (x + y).ult y = true then (1 : Word) else 0).toNat =
      (x.toNat + y.toNat) / 2 ^ 64 := by
  simpa [BitVec.ult] using EvmWord.carry_toNat (x := x) (y := y)

/-- The second call's offset-120 carry bit as a Nat quotient. -/
theorem mulModProductLayoutCall02P120_toNat_eq_column1CarryLow (a b : EvmWord) :
    let a0 := a.getLimbN 0; let a1 := a.getLimbN 1;
    let b0 := b.getLimbN 0; let b1 := b.getLimbN 1;
    let p00 := a0.toNat * b0.toNat;
    let p10 := a1.toNat * b0.toNat;
    let p01 := a0.toNat * b1.toNat;
    (mulModProductLayoutCall02P120 a b).toNat =
      (((p01 / 2 ^ 64 +
            (((p00 / 2 ^ 64 + p10 % 2 ^ 64) % 2 ^ 64 + p01 % 2 ^ 64) /
              2 ^ 64)) %
          2 ^ 64 +
        (p10 / 2 ^ 64 + (p00 / 2 ^ 64 + p10 % 2 ^ 64) / 2 ^ 64) % 2 ^ 64) /
        2 ^ 64) := by
  dsimp only
  rw [mulModProductLayoutCall02P120_eq_expanded]
  simp only [mulModProductLayoutCarryRightEqTrue_toNat,
    mulModProductLayoutCarryEqTrue_toNat, BitVec.toNat_add, EvmWord.rv64_mulhu_toNat,
    EvmWord.mul_toNat]


/-- The second call's offset-120 carry bit in high/low product-word form. -/
theorem mulModProductLayoutCall02P120_toNat_eq_column1CarryLowWords (a b : EvmWord) :
    (mulModProductLayoutCall02P120 a b).toNat =
      (((rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat +
          (((rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat +
              (a.getLimbN 1 * b.getLimbN 0).toNat) % 2 ^ 64 +
            (a.getLimbN 0 * b.getLimbN 1).toNat) / 2 ^ 64) % 2 ^ 64 +
        ((rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat +
          ((rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat +
            (a.getLimbN 1 * b.getLimbN 0).toNat) / 2 ^ 64) % 2 ^ 64) /
        2 ^ 64 := by
  rw [mulModProductLayoutCall02P120_eq_expanded]
  simp only [mulModProductLayoutCarryEqTrue_toNat,
    mulModProductLayoutCarryRightEqTrue_toNat, BitVec.toNat_add]



end EvmAsm.Evm64
