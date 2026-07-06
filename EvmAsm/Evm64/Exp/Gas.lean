/-
  EvmAsm.Evm64.Exp.Gas

  Dynamic gas helpers for the EXP opcode (GH #92). The static/base EXP cost
  remains the table entry in `EvmAsm.Evm64.Gas`; this file adds the
  exponent-byte add-on used by Shanghai-era executable semantics.
-/

import EvmAsm.Evm64.Basic
import EvmAsm.Evm64.Gas

namespace EvmAsm.Evm64.ExpGas

/-- Dynamic EXP byte cost charged for each byte of a nonzero exponent. -/
def expGasPerByte : Nat := 50

/-- Number of big-endian bytes needed to encode a natural exponent, with zero
    encoded as length zero for EXP gas accounting. -/
def exponentByteLengthNat : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + exponentByteLengthNat ((n + 1) / 256)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

theorem exponentByteLengthNat_zero : exponentByteLengthNat 0 = 0 := by
  simp [exponentByteLengthNat]

theorem exponentByteLengthNat_succ (n : Nat) :
    exponentByteLengthNat (n + 1) = 1 + exponentByteLengthNat ((n + 1) / 256) := by
  rw [exponentByteLengthNat]

theorem exponentByteLengthNat_of_pos_lt_256 {n : Nat} (h_pos : 0 < n) (h_lt : n < 256) :
    exponentByteLengthNat n = 1 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [exponentByteLengthNat_succ]
      have h_div : (k + 1) / 256 = 0 := Nat.div_eq_of_lt h_lt
      simp [h_div, exponentByteLengthNat_zero]

theorem exponentByteLengthNat_one : exponentByteLengthNat 1 = 1 := by
  exact exponentByteLengthNat_of_pos_lt_256 (by decide) (by decide)

theorem exponentByteLengthNat_255 : exponentByteLengthNat 255 = 1 := by
  exact exponentByteLengthNat_of_pos_lt_256 (by decide) (by decide)

theorem exponentByteLengthNat_256 : exponentByteLengthNat 256 = 2 := by
  rw [show (256 : Nat) = 255 + 1 from rfl, exponentByteLengthNat_succ,
    show (255 + 1) / 256 = 1 from rfl, exponentByteLengthNat_one]

theorem exponentByteLengthNat_65535 : exponentByteLengthNat 65535 = 2 := by
  rw [show (65535 : Nat) = 65534 + 1 from rfl, exponentByteLengthNat_succ,
    show (65534 + 1) / 256 = 255 from rfl, exponentByteLengthNat_255]

theorem exponentByteLengthNat_65536 : exponentByteLengthNat 65536 = 3 := by
  rw [show (65536 : Nat) = 65535 + 1 from rfl, exponentByteLengthNat_succ,
    show (65535 + 1) / 256 = 256 from rfl, exponentByteLengthNat_256]

theorem exponentByteLengthNat_16777215 : exponentByteLengthNat 16777215 = 3 := by
  rw [show (16777215 : Nat) = 16777214 + 1 from rfl, exponentByteLengthNat_succ,
    show (16777214 + 1) / 256 = 65535 from rfl, exponentByteLengthNat_65535]

theorem exponentByteLengthNat_16777216 : exponentByteLengthNat 16777216 = 4 := by
  rw [show (16777216 : Nat) = 16777215 + 1 from rfl, exponentByteLengthNat_succ,
    show (16777215 + 1) / 256 = 65536 from rfl, exponentByteLengthNat_65536]

/-- `exponentByteLengthNat (2^(8*j) - 1) = j`: each division-by-256 step strips
    exactly one byte (eight bits) off an all-ones prefix. -/
theorem exponentByteLengthNat_pow8_sub_one (j : Nat) :
    exponentByteLengthNat (2 ^ (8 * j) - 1) = j := by
  induction j with
  | zero => simp [exponentByteLengthNat]
  | succ k ih =>
      have hpos : 0 < 2 ^ (8 * (k + 1)) - 1 := by
        have h2 : 2 ^ 1 ≤ 2 ^ (8 * (k + 1)) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have h1 : (2 : Nat) ^ 1 = 2 := by decide
        omega
      cases h : (2 ^ (8 * (k + 1)) - 1) with
      | zero => omega
      | succ m =>
          rw [exponentByteLengthNat_succ, ← h]
          have hdiv : (2 ^ (8 * (k + 1)) - 1) / 256 = 2 ^ (8 * k) - 1 := by
            rw [show (256 : Nat) = 2 ^ 8 from by decide,
              show 8 * (k + 1) = 8 * k + 8 from by omega, Nat.pow_add]
            have hp : 0 < 2 ^ 8 := by decide
            omega
          rw [hdiv, ih]
          omega

theorem exponentByteLengthNat_max : exponentByteLengthNat (2^256 - 1) = 32 := by
  have h := exponentByteLengthNat_pow8_sub_one 32
  simpa using h

/-- Number of exponent bytes seen by EXP dynamic gas accounting. -/
def exponentByteLength (exponent : EvmWord) : Nat :=
  exponentByteLengthNat exponent.toNat

/-- Dynamic EXP gas add-on from the exponent operand alone. -/
def expDynamicCostFromExponent (exponent : EvmWord) : Nat :=
  expGasPerByte * exponentByteLength exponent

/-- Full EXP gas before memory-independent execution effects: static EXP base
    cost plus the exponent-byte dynamic add-on. -/
def expTotalGasFromExponent (exponent : EvmWord) : Nat :=
  EvmOpcode.staticGasCost .EXP + expDynamicCostFromExponent exponent

theorem exponentByteLength_zero : exponentByteLength (0 : EvmWord) = 0 := by
  unfold exponentByteLength
  simp [exponentByteLengthNat_zero]

theorem exponentByteLength_of_pos_lt_256 {exponent : EvmWord}
    (h_pos : 0 < exponent.toNat) (h_lt : exponent.toNat < 256) :
    exponentByteLength exponent = 1 := by
  unfold exponentByteLength
  exact exponentByteLengthNat_of_pos_lt_256 h_pos h_lt

theorem exponentByteLength_one : exponentByteLength (1 : EvmWord) = 1 := by
  exact exponentByteLength_of_pos_lt_256 (by decide) (by decide)

theorem exponentByteLength_255 : exponentByteLength (255 : EvmWord) = 1 := by
  exact exponentByteLength_of_pos_lt_256 (by decide) (by decide)

theorem exponentByteLength_256 : exponentByteLength (256 : EvmWord) = 2 := by
  unfold exponentByteLength
  rw [show (256 : EvmWord).toNat = 256 from by decide]
  exact exponentByteLengthNat_256

theorem exponentByteLength_65535 : exponentByteLength (65535 : EvmWord) = 2 := by
  unfold exponentByteLength
  rw [show (65535 : EvmWord).toNat = 65535 from by decide]
  exact exponentByteLengthNat_65535

theorem exponentByteLength_65536 : exponentByteLength (65536 : EvmWord) = 3 := by
  unfold exponentByteLength
  rw [show (65536 : EvmWord).toNat = 65536 from by decide]
  exact exponentByteLengthNat_65536

theorem exponentByteLength_16777215 : exponentByteLength (16777215 : EvmWord) = 3 := by
  unfold exponentByteLength
  rw [show (16777215 : EvmWord).toNat = 16777215 from by decide]
  exact exponentByteLengthNat_16777215

theorem exponentByteLength_16777216 : exponentByteLength (16777216 : EvmWord) = 4 := by
  unfold exponentByteLength
  rw [show (16777216 : EvmWord).toNat = 16777216 from by decide]
  exact exponentByteLengthNat_16777216

theorem exponentByteLength_max : exponentByteLength (-1 : EvmWord) = 32 := by
  unfold exponentByteLength
  rw [show (-1 : EvmWord).toNat = 2 ^ 256 - 1 from by decide]
  exact exponentByteLengthNat_max

theorem expDynamicCostFromExponent_zero :
    expDynamicCostFromExponent (0 : EvmWord) = 0 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_zero]

theorem expDynamicCostFromExponent_of_pos_lt_256 {exponent : EvmWord}
    (h_pos : 0 < exponent.toNat) (h_lt : exponent.toNat < 256) :
    expDynamicCostFromExponent exponent = 50 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_of_pos_lt_256 h_pos h_lt]

theorem expDynamicCostFromExponent_one :
    expDynamicCostFromExponent (1 : EvmWord) = 50 := by
  exact expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)

theorem expTotalGasFromExponent_zero :
    expTotalGasFromExponent (0 : EvmWord) = 10 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_zero]
  rfl

theorem expTotalGasFromExponent_of_pos_lt_256 {exponent : EvmWord}
    (h_pos : 0 < exponent.toNat) (h_lt : exponent.toNat < 256) :
    expTotalGasFromExponent exponent = 60 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_of_pos_lt_256 h_pos h_lt]
  rfl

theorem expTotalGasFromExponent_one :
    expTotalGasFromExponent (1 : EvmWord) = 60 := by
  exact expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)

theorem expTotalGasFromExponent_255 :
    expTotalGasFromExponent (255 : EvmWord) = 60 := by
  exact expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)

theorem expDynamicCostFromExponent_255 :
    expDynamicCostFromExponent (255 : EvmWord) = 50 := by
  exact expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)

theorem expDynamicCostFromExponent_256 :
    expDynamicCostFromExponent (256 : EvmWord) = 100 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_256]

theorem expTotalGasFromExponent_256 :
    expTotalGasFromExponent (256 : EvmWord) = 110 := by
  unfold expTotalGasFromExponent expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_256]
  rfl

theorem expDynamicCostFromExponent_65535 :
    expDynamicCostFromExponent (65535 : EvmWord) = 100 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_65535]

theorem expTotalGasFromExponent_65535 :
    expTotalGasFromExponent (65535 : EvmWord) = 110 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_65535]
  rfl

theorem expDynamicCostFromExponent_65536 :
    expDynamicCostFromExponent (65536 : EvmWord) = 150 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_65536]

theorem expTotalGasFromExponent_65536 :
    expTotalGasFromExponent (65536 : EvmWord) = 160 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_65536]
  rfl

theorem expDynamicCostFromExponent_16777215 :
    expDynamicCostFromExponent (16777215 : EvmWord) = 150 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_16777215]

theorem expTotalGasFromExponent_16777215 :
    expTotalGasFromExponent (16777215 : EvmWord) = 160 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_16777215]
  rfl

theorem expDynamicCostFromExponent_16777216 :
    expDynamicCostFromExponent (16777216 : EvmWord) = 200 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_16777216]

theorem expTotalGasFromExponent_16777216 :
    expTotalGasFromExponent (16777216 : EvmWord) = 210 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_16777216]
  rfl

theorem expDynamicCostFromExponent_max :
    expDynamicCostFromExponent (-1 : EvmWord) = 1600 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_max]

theorem expTotalGasFromExponent_max :
    expTotalGasFromExponent (-1 : EvmWord) = 1610 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_max]
  rfl

end EvmAsm.Evm64.ExpGas
