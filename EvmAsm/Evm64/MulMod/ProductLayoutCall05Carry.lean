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

/-- Carry out of a two-word addition in `BitVec.ult` spelling. -/
theorem mulModProductLayoutCarryRightBitVecUltEqTrue_toNat (x y : Word) :
    (if BitVec.ult (x + y) y = true then (1 : Word) else 0).toNat =
      (x.toNat + y.toNat) / 2 ^ 64 := by
  simpa only [BitVec.ult] using mulModProductLayoutCarryRightEqTrue_toNat x y

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



/-- The second call's offset-112 cell is the low word of the column-1 quotient. -/
theorem mulModProductLayoutCall02P112_toNat_eq_column1CarryLowWord (a b : EvmWord) :
    let mu00 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat
    let lo10 := (a.getLimbN 1 * b.getLimbN 0).toNat
    let lo01 := (a.getLimbN 0 * b.getLimbN 1).toNat
    let mu10 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat
    let mu01 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat
    (mulModProductLayoutCall02P112 a b).toNat =
      ((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) / 2 ^ 64) %
        2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall02P112_eq_expanded]
  simp only [mulModProductLayoutCarryRightEqTrue_toNat, BitVec.toNat_add]
  have h01 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)
  have h10 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)
  omega

/-- The second call's offset-120 cell is the high word of the column-1 quotient. -/
theorem mulModProductLayoutCall02P120_toNat_eq_column1CarryHighWord (a b : EvmWord) :
    let mu00 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat
    let lo10 := (a.getLimbN 1 * b.getLimbN 0).toNat
    let lo01 := (a.getLimbN 0 * b.getLimbN 1).toNat
    let mu10 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat
    let mu01 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat
    (mulModProductLayoutCall02P120 a b).toNat =
      ((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) / 2 ^ 64) /
        2 ^ 64 % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall02P120_toNat_eq_column1CarryLowWords]
  have h_mu00 : (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat < 2 ^ 64 :=
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).isLt
  have h_lo10 : (a.getLimbN 1 * b.getLimbN 0).toNat < 2 ^ 64 :=
    (a.getLimbN 1 * b.getLimbN 0).isLt
  have h_lo01 : (a.getLimbN 0 * b.getLimbN 1).toNat < 2 ^ 64 :=
    (a.getLimbN 0 * b.getLimbN 1).isLt
  have h10 : (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat * 2 ^ 64 +
      (a.getLimbN 1 * b.getLimbN 0).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)]
    exact Nat.mul_le_mul (by have := (a.getLimbN 1).isLt; omega)
      (by have := (b.getLimbN 0).isLt; omega)
  have h01 : (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat * 2 ^ 64 +
      (a.getLimbN 0 * b.getLimbN 1).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)]
    exact Nat.mul_le_mul (by have := (a.getLimbN 0).isLt; omega)
      (by have := (b.getLimbN 1).isLt; omega)
  omega


/-- The third call's offset-112 cell after adding the `a2*b0` low word. -/
theorem mulModProductLayoutCall03P112_toNat_eq_column2Add20LowWord (a b : EvmWord) :
    let mu00 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat
    let lo10 := (a.getLimbN 1 * b.getLimbN 0).toNat
    let lo20 := (a.getLimbN 2 * b.getLimbN 0).toNat
    let mu10 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat
    let lo01 := (a.getLimbN 0 * b.getLimbN 1).toNat
    let mu01 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat
    (mulModProductLayoutCall03P112 a b).toNat =
      (((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) /
          2 ^ 64) % 2 ^ 64 + lo20) % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall03P112_eq_add]
  unfold mulModAddPartialLoProduct
  rw [BitVec.toNat_add]
  rw [mulModProductLayoutCall02P112_toNat_eq_column1CarryLowWord]

/-- The fourth call's offset-112 cell after adding the `a1*b1` low word. -/
theorem mulModProductLayoutCall04P112_toNat_eq_column2Add11LowWord (a b : EvmWord) :
    let mu00 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat
    let lo10 := (a.getLimbN 1 * b.getLimbN 0).toNat
    let lo20 := (a.getLimbN 2 * b.getLimbN 0).toNat
    let mu10 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat
    let lo01 := (a.getLimbN 0 * b.getLimbN 1).toNat
    let mu01 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat
    let lo11 := (a.getLimbN 1 * b.getLimbN 1).toNat
    (mulModProductLayoutCall04P112 a b).toNat =
      ((((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) /
          2 ^ 64) % 2 ^ 64 + lo20) % 2 ^ 64 + lo11) % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall04P112_eq_add]
  unfold mulModAddPartialLoProduct
  rw [BitVec.toNat_add]
  rw [mulModProductLayoutCall03P112_toNat_eq_column2Add20LowWord]


/-- The fifth call's offset-120 cell is the low word of the column-2 carry. -/
theorem mulModProductLayoutCall05P120_toNat_eq_limb2CarryLow (a b : EvmWord) :
    let mu00 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat
    let lo00 := (a.getLimbN 0 * b.getLimbN 0).toNat
    let lo10 := (a.getLimbN 1 * b.getLimbN 0).toNat
    let mu10 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat
    let lo20 := (a.getLimbN 2 * b.getLimbN 0).toNat
    let mu20 := (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)).toNat
    let lo01 := (a.getLimbN 0 * b.getLimbN 1).toNat
    let mu01 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat
    let lo11 := (a.getLimbN 1 * b.getLimbN 1).toNat
    let mu11 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)).toNat
    let lo02 := (a.getLimbN 0 * b.getLimbN 2).toNat
    let mu02 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)).toNat
    (mulModProductLayoutCall05P120 a b).toNat =
      (mu02 * 2 ^ 64 + lo02 + (mu11 * 2 ^ 64 + lo11) +
        (mu20 * 2 ^ 64 + lo20) +
        (mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) +
          (mu00 * 2 ^ 64 + lo00) / 2 ^ 64) / 2 ^ 64) /
        2 ^ 64 % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall05P120_eq_add]
  rw [mulModProductLayoutCall04P120_eq_add]
  rw [mulModProductLayoutCall03P120_eq_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry
    mulModAddPartialLoValue mulModAddPartialLoProduct
  simp only [BitVec.toNat_add, mulModProductLayoutCarryRight_toNat,
    mulModProductLayoutCall02P112_toNat_eq_column1CarryLowWord,
    mulModProductLayoutCall02P120_toNat_eq_column1CarryHighWord,
    mulModProductLayoutCall03P112_toNat_eq_column2Add20LowWord,
    mulModProductLayoutCall04P112_toNat_eq_column2Add11LowWord]
  have h00 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 0)
  have h10 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)
  have h20 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 0)
  have h01 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)
  have h11 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 1)
  have h02 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 2)
  omega


/-- The third call's offset-120 cell after adding the `a2*b0` high word. -/
theorem mulModProductLayoutCall03P120_toNat_eq_column2Add20HighWord (a b : EvmWord) :
    let mu00 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat
    let lo10 := (a.getLimbN 1 * b.getLimbN 0).toNat
    let mu10 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat
    let lo20 := (a.getLimbN 2 * b.getLimbN 0).toNat
    let mu20 := (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)).toNat
    let lo01 := (a.getLimbN 0 * b.getLimbN 1).toNat
    let mu01 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat
    (mulModProductLayoutCall03P120 a b).toNat =
      (((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) /
            2 ^ 64) / 2 ^ 64 % 2 ^ 64 +
        (mu20 +
          (((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) /
                2 ^ 64) % 2 ^ 64 + lo20) /
            2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall03P120_eq_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry
    mulModAddPartialLoValue mulModAddPartialLoProduct
  simp only [BitVec.toNat_add, mulModProductLayoutCarryRight_toNat,
    mulModProductLayoutCall02P112_toNat_eq_column1CarryLowWord,
    mulModProductLayoutCall02P120_toNat_eq_column1CarryHighWord]

/-- The fourth call's offset-120 cell after adding the `a1*b1` high word. -/
theorem mulModProductLayoutCall04P120_toNat_eq_column2Add11HighWord (a b : EvmWord) :
    let mu00 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0)).toNat
    let lo10 := (a.getLimbN 1 * b.getLimbN 0).toNat
    let mu10 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)).toNat
    let lo20 := (a.getLimbN 2 * b.getLimbN 0).toNat
    let mu20 := (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)).toNat
    let lo01 := (a.getLimbN 0 * b.getLimbN 1).toNat
    let mu01 := (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)).toNat
    let lo11 := (a.getLimbN 1 * b.getLimbN 1).toNat
    let mu11 := (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)).toNat
    (mulModProductLayoutCall04P120 a b).toNat =
      (((((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) /
              2 ^ 64) / 2 ^ 64 % 2 ^ 64 +
          (mu20 +
            (((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) /
                  2 ^ 64) % 2 ^ 64 + lo20) /
              2 ^ 64) % 2 ^ 64) % 2 ^ 64) +
        (mu11 +
          ((((mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) + mu00) /
                2 ^ 64) % 2 ^ 64 + lo20) % 2 ^ 64 + lo11) /
            2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall04P120_eq_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry
    mulModAddPartialLoValue mulModAddPartialLoProduct
  simp only [BitVec.toNat_add, mulModProductLayoutCarryRight_toNat,
    mulModProductLayoutCall03P112_toNat_eq_column2Add20LowWord,
    mulModProductLayoutCall03P120_toNat_eq_column2Add20HighWord]








/-- The fifth call's offset-128 cell is the high word of the column-2 carry. -/
theorem mulModProductLayoutCall05P128_toNat_eq_limb2CarryHigh (a b : EvmWord) :
    let a0 := a.getLimbN 0
    let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2
    let b0 := b.getLimbN 0
    let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2
    let d0 := a0.toNat * b0.toNat
    let d1 := a0.toNat * b1.toNat + a1.toNat * b0.toNat
    let d2 := a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    (mulModProductLayoutCall05P128 a b).toNat = (c3 / 2 ^ 64) % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall05P128_eq_highCarry]
  simp only [BitVec.toNat_add, mulModProductLayoutCarryRight_toNat,
    mulModProductLayoutCall02P112_toNat_eq_column1CarryLowWord,
    mulModProductLayoutCall02P120_toNat_eq_column1CarryHighWord,
    mulModProductLayoutCall03P112_toNat_eq_column2Add20LowWord,
    mulModProductLayoutCall03P120_toNat_eq_column2Add20HighWord,
    mulModProductLayoutCall04P112_toNat_eq_column2Add11LowWord,
    mulModProductLayoutCall04P120_toNat_eq_column2Add11HighWord]
  have h00 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 0)
  have h10 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)
  have h20 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 0)
  have h01 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)
  have h11 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 1)
  have h02 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 2)
  have ha0 := (a.getLimbN 0).isLt
  have ha1 := (a.getLimbN 1).isLt
  have ha2 := (a.getLimbN 2).isLt
  have hb0 := (b.getLimbN 0).isLt
  have hb1 := (b.getLimbN 1).isLt
  have hb2 := (b.getLimbN 2).isLt
  have hp20 : (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)).toNat * 2 ^ 64 +
      (a.getLimbN 2 * b.getLimbN 0).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [h20]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hp11 : (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)).toNat * 2 ^ 64 +
      (a.getLimbN 1 * b.getLimbN 1).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [h11]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hp02 : (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)).toNat * 2 ^ 64 +
      (a.getLimbN 0 * b.getLimbN 2).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [h02]
    exact Nat.mul_le_mul (by omega) (by omega)
  rw [mulModProductLayoutCarryHighFromTwoWordAccumulatorProducts
    (hlo := Nat.mod_lt _ (by norm_num))
    (hhi := Nat.mod_lt _ (by norm_num))
    (hp20 := hp20) (hp11 := hp11) (hp02 := hp02)]
  norm_num at h00 h10 h20 h01 h11 h02 ⊢
  omega

end EvmAsm.Evm64
