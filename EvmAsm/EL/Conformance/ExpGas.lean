/-
  EvmAsm.EL.Conformance.ExpGas

  Lean-side conformance vectors for EXP exponent-byte gas accounting
  (GH #125, exercising the GH #92 executable helper).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.Exp.Gas

@[expose] public section

namespace EvmAsm.EL
namespace Conformance
namespace ExpGas

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Input shape for an EXP gas executable-helper conformance vector. -/
structure ExpGasInput where
  exponent : EvmWord
  deriving Repr

def runExpGas (input : ExpGasInput) : Nat :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent input.exponent

/-- EXP with zero exponent charges only the static/base EXP gas.
    Distinctive token: expGasZeroExponentVector. -/
def expGasZeroExponentVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-zero-exponent"
    input := { exponent := 0 }
    expected := .value 10 }

/-- A one-byte nonzero exponent adds one 50-gas exponent-byte charge. -/
def expGasOneByteExponentVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-one-byte-exponent"
    input := { exponent := 1 }
    expected := .value 60 }

/-- Exponent 255 is the upper end of the one-byte exponent gas range.
    Distinctive token: exp-gas-one-byte-upper. -/
def expGasOneByteUpperVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-one-byte-upper"
    input := { exponent := 255 }
    expected := .value 60 }

/-- Exponent 256 is the first two-byte threshold and charges 10 + 2 * 50. -/
def expGasTwoByteThresholdVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-two-byte-threshold"
    input := { exponent := 256 }
    expected := .value 110 }

/-- The maximum 256-bit exponent occupies all 32 bytes. -/
def expGasMaxExponentVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-max-exponent"
    input := { exponent := -1 }
    expected := .value 1610 }

theorem runExpGas_zero :
    runExpGas { exponent := (0 : EvmWord) } = 10 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_zero

theorem runExpGas_one :
    runExpGas { exponent := (1 : EvmWord) } = 60 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_of_pos_lt_256
    (by decide) (by decide)

theorem runExpGas_255 :
    runExpGas { exponent := (255 : EvmWord) } = 60 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_of_pos_lt_256
    (by decide) (by decide)

theorem runExpGas_256 :
    runExpGas { exponent := (256 : EvmWord) } = 110 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_256

theorem runExpGas_max :
    runExpGas { exponent := (-1 : EvmWord) } = 1610 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_max

theorem expGasZeroExponentVector_passed :
    checkVector runExpGas expGasZeroExponentVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-zero-exponent"
    { exponent := (0 : EvmWord) }
    10
    runExpGas_zero

theorem expGasOneByteExponentVector_passed :
    checkVector runExpGas expGasOneByteExponentVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-one-byte-exponent"
    { exponent := (1 : EvmWord) }
    60
    runExpGas_one

theorem expGasOneByteUpperVector_passed :
    checkVector runExpGas expGasOneByteUpperVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-one-byte-upper"
    { exponent := (255 : EvmWord) }
    60
    runExpGas_255

theorem expGasTwoByteThresholdVector_passed :
    checkVector runExpGas expGasTwoByteThresholdVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-two-byte-threshold"
    { exponent := (256 : EvmWord) }
    110
    runExpGas_256

theorem expGasMaxExponentVector_passed :
    checkVector runExpGas expGasMaxExponentVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-max-exponent"
    { exponent := (-1 : EvmWord) }
    1610
    runExpGas_max

/-- Vector IDs for EXP gas executable-helper conformance coverage.
    Distinctive token: expGasConformanceVectorIds #125 #92. -/
def expGasConformanceVectorIds : List String :=
  [ expGasZeroExponentVector.id
  , expGasOneByteExponentVector.id
  , expGasOneByteUpperVector.id
  , expGasTwoByteThresholdVector.id
  , expGasMaxExponentVector.id
  ]

theorem expGasConformanceVectorIds_eq :
    expGasConformanceVectorIds =
      [ "exp-gas-zero-exponent"
      , "exp-gas-one-byte-exponent"
      , "exp-gas-one-byte-upper"
      , "exp-gas-two-byte-threshold"
      , "exp-gas-max-exponent"
      ] := rfl

theorem expGasConformanceVectorIds_length :
    expGasConformanceVectorIds.length = 5 := rfl

theorem expGasConformanceVectorIds_nodup :
    expGasConformanceVectorIds.Nodup := by
  decide

/-- Compact checked-vector batch for EXP gas executable helpers.
    Distinctive token: expGasConformanceVectors. -/
def expGasConformanceVectors : List CheckResult :=
  [ checkVector runExpGas expGasZeroExponentVector
  , checkVector runExpGas expGasOneByteExponentVector
  , checkVector runExpGas expGasOneByteUpperVector
  , checkVector runExpGas expGasTwoByteThresholdVector
  , checkVector runExpGas expGasMaxExponentVector
  ]

theorem expGasConformanceVectors_passed :
    expGasConformanceVectors = [.passed, .passed, .passed, .passed, .passed] := by
  simp [expGasConformanceVectors, expGasZeroExponentVector_passed,
    expGasOneByteExponentVector_passed, expGasOneByteUpperVector_passed,
    expGasTwoByteThresholdVector_passed, expGasMaxExponentVector_passed]

end ExpGas
end Conformance
end EvmAsm.EL
