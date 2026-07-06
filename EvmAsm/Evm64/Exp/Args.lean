/-
  EvmAsm.Evm64.Exp.Args

  Pure stack-argument bridge for EXP (GH #92).
-/

import EvmAsm.Evm64.EvmWordArith.Exp
import EvmAsm.Evm64.Exp.Gas

namespace EvmAsm.Evm64
namespace ExpArgs

/-- EXP stack arguments: base and exponent. -/
structure Args where
  base : EvmWord
  exponent : EvmWord
  deriving Repr

/-- EXP pops two stack words: base and exponent. -/
def stackArgumentCount : Nat := 2

/-- EXP pushes one result word. -/
def resultCount : Nat := 1

/-- Convenience builder for EXP stack arguments. -/
def expArgs (base exponent : EvmWord) : Args :=
  { base := base, exponent := exponent }

/-- EXP result computed from decoded stack arguments.
    Distinctive token: ExpArgs.expResultFromArgs. -/
def expResultFromArgs (args : Args) : EvmWord :=
  EvmWord.exp args.base args.exponent

/-- Dynamic gas for EXP computed from decoded stack arguments. -/
def expDynamicCostFromArgs (args : Args) : Nat :=
  ExpGas.expDynamicCostFromExponent args.exponent

/-- Total EXP gas computed from decoded stack arguments. -/
def expTotalGasFromArgs (args : Args) : Nat :=
  ExpGas.expTotalGasFromExponent args.exponent

/-- Stack after the EXP result replaces the two operands. -/
def stackAfterExp (args : Args) (rest : List EvmWord) : List EvmWord :=
  expResultFromArgs args :: rest

theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl

theorem resultCount_eq_one : resultCount = 1 := rfl

theorem expArgs_base (base exponent : EvmWord) :
    (expArgs base exponent).base = base := rfl

theorem expArgs_exponent (base exponent : EvmWord) :
    (expArgs base exponent).exponent = exponent := rfl

theorem expResultFromArgs_eq (args : Args) :
    expResultFromArgs args = EvmWord.exp args.base args.exponent := rfl

theorem expDynamicCostFromArgs_eq (args : Args) :
    expDynamicCostFromArgs args =
      ExpGas.expDynamicCostFromExponent args.exponent := rfl

theorem expTotalGasFromArgs_eq (args : Args) :
    expTotalGasFromArgs args =
      ExpGas.expTotalGasFromExponent args.exponent := rfl

theorem expTotalGasFromArgs_eq_static_add_dynamic (args : Args) :
    expTotalGasFromArgs args =
      EvmOpcode.staticGasCost .EXP + expDynamicCostFromArgs args := rfl

theorem expTotalGasFromArgs_eq_dynamic_add_static (args : Args) :
    expTotalGasFromArgs args =
      expDynamicCostFromArgs args + EvmOpcode.staticGasCost .EXP := by
  rw [expTotalGasFromArgs_eq_static_add_dynamic, Nat.add_comm]

theorem stackAfterExp_eq (args : Args) (rest : List EvmWord) :
    stackAfterExp args rest = expResultFromArgs args :: rest := rfl

theorem stackAfterExp_head (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).head? = some (expResultFromArgs args) := rfl

theorem stackAfterExp_tail (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).tail = rest := rfl

@[simp] theorem stackAfterExp_length (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).length = rest.length + 1 := by
  simp [stackAfterExp]

theorem stackAfterExp_length_pos (args : Args) (rest : List EvmWord) :
    0 < (stackAfterExp args rest).length := by
  simp [stackAfterExp]

theorem stackAfterExp_length_eq_counts (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).length + stackArgumentCount =
      (args.base :: args.exponent :: rest).length + resultCount := by
  simp [stackAfterExp, stackArgumentCount, resultCount]

theorem stackAfterExp_length_succ_eq_input_length
    (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).length + 1 =
      (args.base :: args.exponent :: rest).length := by
  simp [stackAfterExp, Nat.add_comm]

theorem stackAfterExp_ne_nil (args : Args) (rest : List EvmWord) :
    stackAfterExp args rest ≠ [] := by
  simp [stackAfterExp]

theorem expResultFromArgs_zero_zero :
    expResultFromArgs (expArgs 0 0) = 1 := by
  exact EvmWord.exp_zero_zero

theorem expResultFromArgs_zero_right (base : EvmWord) :
    expResultFromArgs (expArgs base 0) = 1 := by
  exact EvmWord.exp_zero_right base

theorem expResultFromArgs_max_zero_right :
    expResultFromArgs (expArgs (-1 : EvmWord) 0) = 1 := by
  exact expResultFromArgs_zero_right (-1 : EvmWord)

theorem expResultFromArgs_one_left (exponent : EvmWord) :
    expResultFromArgs (expArgs 1 exponent) = 1 := by
  exact EvmWord.exp_one_left exponent

theorem expResultFromArgs_zero_left_of_ne_zero (exponent : EvmWord)
    (h : exponent ≠ 0) :
    expResultFromArgs (expArgs 0 exponent) = 0 := by
  exact EvmWord.exp_zero_left_of_ne_zero exponent h

theorem expResultFromArgs_zero_left_of_toNat_pos (exponent : EvmWord)
    (h_pos : 0 < exponent.toNat) :
    expResultFromArgs (expArgs 0 exponent) = 0 := by
  exact expResultFromArgs_zero_left_of_ne_zero exponent (by
    intro h_zero
    rw [h_zero] at h_pos
    simp at h_pos)

theorem expResultFromArgs_one_right (base : EvmWord) :
    expResultFromArgs (expArgs base 1) = base := by
  exact EvmWord.exp_one_right base

theorem expResultFromArgs_zero_one :
    expResultFromArgs (expArgs 0 1) = 0 := by
  exact expResultFromArgs_one_right 0

theorem expResultFromArgs_two_one :
    expResultFromArgs (expArgs 2 1) = 2 := by
  exact EvmWord.exp_two_one

theorem expResultFromArgs_max_one_right :
    expResultFromArgs (expArgs (-1 : EvmWord) 1) = (-1 : EvmWord) := by
  exact expResultFromArgs_one_right (-1 : EvmWord)

theorem expResultFromArgs_two_64 :
    expResultFromArgs (expArgs 2 64) = BitVec.ofNat 256 (2^64) := by
  exact EvmWord.exp_two_64

theorem expResultFromArgs_two_128 :
    expResultFromArgs (expArgs 2 128) = BitVec.ofNat 256 (2^128) := by
  exact EvmWord.exp_two_128

theorem expResultFromArgs_two_255 :
    expResultFromArgs (expArgs 2 255) = BitVec.ofNat 256 (2^255) := by
  exact EvmWord.exp_two_255

theorem expResultFromArgs_two_256 :
    expResultFromArgs (expArgs 2 256) = 0 := by
  exact EvmWord.exp_two_256

theorem expResultFromArgs_zero_left_max :
    expResultFromArgs (expArgs 0 (-1 : EvmWord)) = 0 := by
  exact expResultFromArgs_zero_left_of_ne_zero (-1 : EvmWord) (by decide)

theorem stackAfterExp_zero_exponent (base : EvmWord) (rest : List EvmWord) :
    stackAfterExp (expArgs base 0) rest = 1 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_right]

theorem stackAfterExp_max_zero_exponent (rest : List EvmWord) :
    stackAfterExp (expArgs (-1 : EvmWord) 0) rest = 1 :: rest := by
  rw [stackAfterExp, expResultFromArgs_max_zero_right]

theorem stackAfterExp_zero_zero (rest : List EvmWord) :
    stackAfterExp (expArgs 0 0) rest = 1 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_zero]

theorem stackAfterExp_zero_left_of_ne_zero
    (exponent : EvmWord) (rest : List EvmWord) (h : exponent ≠ 0) :
    stackAfterExp (expArgs 0 exponent) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_left_of_ne_zero exponent h]

theorem stackAfterExp_zero_left_of_toNat_pos
    (exponent : EvmWord) (rest : List EvmWord) (h_pos : 0 < exponent.toNat) :
    stackAfterExp (expArgs 0 exponent) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_left_of_toNat_pos exponent h_pos]

theorem stackAfterExp_one_left (exponent : EvmWord) (rest : List EvmWord) :
    stackAfterExp (expArgs 1 exponent) rest = 1 :: rest := by
  rw [stackAfterExp, expResultFromArgs_one_left]

theorem stackAfterExp_one_exponent (base : EvmWord) (rest : List EvmWord) :
    stackAfterExp (expArgs base 1) rest = base :: rest := by
  rw [stackAfterExp, expResultFromArgs_one_right]

theorem stackAfterExp_zero_one (rest : List EvmWord) :
    stackAfterExp (expArgs 0 1) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_one]

theorem stackAfterExp_two_one (rest : List EvmWord) :
    stackAfterExp (expArgs 2 1) rest = 2 :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_one]

theorem stackAfterExp_max_one_exponent (rest : List EvmWord) :
    stackAfterExp (expArgs (-1 : EvmWord) 1) rest = (-1 : EvmWord) :: rest := by
  rw [stackAfterExp, expResultFromArgs_max_one_right]

theorem stackAfterExp_two_64 (rest : List EvmWord) :
    stackAfterExp (expArgs 2 64) rest =
      BitVec.ofNat 256 (2^64) :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_64]

theorem stackAfterExp_two_128 (rest : List EvmWord) :
    stackAfterExp (expArgs 2 128) rest =
      BitVec.ofNat 256 (2^128) :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_128]

theorem stackAfterExp_two_255 (rest : List EvmWord) :
    stackAfterExp (expArgs 2 255) rest =
      BitVec.ofNat 256 (2^255) :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_255]

theorem stackAfterExp_two_256 (rest : List EvmWord) :
    stackAfterExp (expArgs 2 256) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_256]

theorem stackAfterExp_zero_left_max (rest : List EvmWord) :
    stackAfterExp (expArgs 0 (-1 : EvmWord)) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_left_max]

theorem expDynamicCostFromArgs_one_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 1) = 50 := by
  unfold expDynamicCostFromArgs expArgs
  change ExpGas.expDynamicCostFromExponent (1 : EvmWord) = 50
  exact ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)

theorem expTotalGasFromArgs_one_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 1) = 60 := by
  unfold expTotalGasFromArgs expArgs
  change ExpGas.expTotalGasFromExponent (1 : EvmWord) = 60
  exact ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)

theorem expTotalGasFromArgs_255_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 255) = 60 := by
  unfold expTotalGasFromArgs expArgs
  change ExpGas.expTotalGasFromExponent (255 : EvmWord) = 60
  exact ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)

theorem expDynamicCostFromArgs_255_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 255) = 50 := by
  unfold expDynamicCostFromArgs expArgs
  change ExpGas.expDynamicCostFromExponent (255 : EvmWord) = 50
  exact ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)

@[simp] theorem expDynamicCostFromArgs_zero_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 0) = 0 := by
  exact ExpGas.expDynamicCostFromExponent_zero

theorem expTotalGasFromArgs_zero_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 0) = 10 := by
  exact ExpGas.expTotalGasFromExponent_zero

theorem expDynamicCostFromArgs_256_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 256) = 100 := by
  unfold expDynamicCostFromArgs expArgs
  change ExpGas.expDynamicCostFromExponent (256 : EvmWord) = 100
  exact ExpGas.expDynamicCostFromExponent_256

theorem expTotalGasFromArgs_256_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 256) = 110 := by
  exact ExpGas.expTotalGasFromExponent_256

theorem expDynamicCostFromArgs_65535_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 65535) = 100 := by
  exact ExpGas.expDynamicCostFromExponent_65535

theorem expTotalGasFromArgs_65535_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 65535) = 110 := by
  exact ExpGas.expTotalGasFromExponent_65535

theorem expDynamicCostFromArgs_65536_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 65536) = 150 := by
  exact ExpGas.expDynamicCostFromExponent_65536

theorem expTotalGasFromArgs_65536_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 65536) = 160 := by
  exact ExpGas.expTotalGasFromExponent_65536

theorem expDynamicCostFromArgs_max_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base (-1)) = 1600 := by
  exact ExpGas.expDynamicCostFromExponent_max

theorem expTotalGasFromArgs_max_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base (-1)) = 1610 := by
  exact ExpGas.expTotalGasFromExponent_max

end ExpArgs
end EvmAsm.Evm64
