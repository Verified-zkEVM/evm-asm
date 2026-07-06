/-
  EvmAsm.EL.Conformance.ExpStackExecution

  Lean-side conformance vectors for the EXP stack execution bridge
  (GH #92 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.Evm64.Exp.StackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace ExpStackExecution

abbrev EvmWord := EvmAsm.Evm64.EvmWord

abbrev ExpStackState := EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackState

abbrev ExpStackResult := EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackResult

abbrev ExpVisibleEffects :=
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpVisibleEffects

deriving instance DecidableEq for
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpVisibleEffects

deriving instance DecidableEq for
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackResult

def runExpStack? (input : ExpStackState) : Option ExpStackResult :=
  EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack? input

/-- EXP with stack [2, 8, 99] returns 256 on top of [99]. -/
def expStackValueVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-value"
    input := { stack := [2, 8, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [256]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }

/-- EXP with zero base and zero exponent returns 1. -/
def expStackZeroZeroVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-zero-zero"
    input := { stack := [0, 0, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [1]
              dynamicGas := 0
              totalGas := 10 }
          stack := [99] } }

/-- EXP with max base and zero exponent returns one with no dynamic gas.
    Distinctive token: exp-stack-max-zero-exponent #92 #125. -/
def expStackMaxZeroExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-max-zero-exponent"
    input := { stack := [(-1 : EvmWord), 0, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [1]
              dynamicGas := 0
              totalGas := 10 }
          stack := [99] } }

/-- EXP with exponent one returns the base word.
    Distinctive token: expStackOneExponentVector #92 #125. -/
def expStackOneExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-one-exponent"
    input := { stack := [7, 1, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [7]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }

/-- EXP edge vector required by GH #92: `2^256 = 0 mod 2^256`.
    Distinctive token: expStackTwo256Vector #92 #125. -/
def expStackTwo256Vector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-two-256"
    input := { stack := [2, 256, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [0]
              dynamicGas := 100
              totalGas := 110 }
          stack := [99] } }

/-- EXP with base one and max exponent returns one while charging max
    exponent-byte gas.
    Distinctive token: exp-stack-one-max-exponent #92 #125. -/
def expStackOneMaxExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-one-max-exponent"
    input := { stack := [1, (-1 : EvmWord), 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [1]
              dynamicGas := 1600
              totalGas := 1610 }
          stack := [99] } }

def expStackZeroOneVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-zero-one"
    input := { stack := [0, 1, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [0]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }

def expStackZeroMaxExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-zero-max-exponent"
    input := { stack := [0, (-1 : EvmWord), 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [0]
              dynamicGas := 1600
              totalGas := 1610 }
          stack := [99] } }

def expStackTwo128Vector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-two-128"
    input := { stack := [2, 128, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^128)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }

/-- EXP with max base and exponent one returns the max word.
    Distinctive token: exp-stack-max-one-exponent #92 #125. -/
def expStackMaxOneExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-max-one-exponent"
    input := { stack := [(-1 : EvmWord), 1, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [(-1 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }

def expStackTwo64Vector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-two-64"
    input := { stack := [2, 64, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^64)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }

def expStackTwo255Vector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-two-255"
    input := { stack := [2, 255, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^255)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }

def expStackUnderflowVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-underflow"
    input := { stack := [2] }
    expected := .error "stack-underflow" }

/-- EXP stack conformance inputs as reusable test vectors.
    Distinctive token:
    ExpStackExecutionConformance.expStackConformanceTestVectors #92 #125. -/
def expStackConformanceTestVectors : List (TestVector ExpStackState ExpStackResult) :=
  [ expStackValueVector
  , expStackZeroZeroVector
  , expStackMaxZeroExponentVector
  , expStackOneExponentVector
  , expStackTwo256Vector
  , expStackOneMaxExponentVector
  , expStackZeroOneVector
  , expStackZeroMaxExponentVector
  , expStackTwo128Vector
  , expStackMaxOneExponentVector
  , expStackTwo64Vector
  , expStackTwo255Vector
  , expStackUnderflowVector
  ]

def expStackConformanceVectorIds : List String :=
  expStackConformanceTestVectors.map TestVector.id

theorem expStackConformanceTestVectors_length :
    expStackConformanceTestVectors.length = 13 := rfl

theorem expStackConformanceVectorIds_eq :
    expStackConformanceVectorIds =
      [ "exp-stack-value"
      , "exp-stack-zero-zero"
      , "exp-stack-max-zero-exponent"
      , "exp-stack-one-exponent"
      , "exp-stack-two-256"
      , "exp-stack-one-max-exponent"
      , "exp-stack-zero-one"
      , "exp-stack-zero-max-exponent"
      , "exp-stack-two-128"
      , "exp-stack-max-one-exponent"
      , "exp-stack-two-64"
      , "exp-stack-two-255"
      , "exp-stack-underflow"
      ] := rfl

theorem expStackConformanceVectorIds_length :
    expStackConformanceVectorIds.length = 13 := rfl

theorem expStackConformanceVectorIds_nodup :
    expStackConformanceVectorIds.Nodup := by
  decide

def expStackValueVectorIds : List String :=
  [ "exp-stack-value"
  , "exp-stack-zero-zero"
  , "exp-stack-max-zero-exponent"
  , "exp-stack-one-exponent"
  , "exp-stack-two-256"
  , "exp-stack-one-max-exponent"
  , "exp-stack-zero-one"
  , "exp-stack-zero-max-exponent"
  , "exp-stack-two-128"
  , "exp-stack-max-one-exponent"
  , "exp-stack-two-64"
  , "exp-stack-two-255"
  ]

def expStackErrorVectorIds : List String :=
  ["exp-stack-underflow"]

theorem expStackValueVectorIds_subset_all :
    ∀ id ∈ expStackValueVectorIds, id ∈ expStackConformanceVectorIds := by
  decide

theorem expStackErrorVectorIds_subset_all :
    ∀ id ∈ expStackErrorVectorIds, id ∈ expStackConformanceVectorIds := by
  decide

theorem expStackValueVectorIds_no_error :
    ∀ id ∈ expStackValueVectorIds, id ∉ expStackErrorVectorIds := by
  decide

theorem runExpStack?_value :
    runExpStack? { stack := [(2 : EvmWord), (8 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(256 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  change EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?
      { stack := [(2 : EvmWord), (8 : EvmWord), (99 : EvmWord)] } =
    some
      { effects :=
          { stackWords := [(256 : EvmWord)]
            dynamicGas := 50
            totalGas := 60 }
        stack := [(99 : EvmWord)] }
  rw [EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_cons]
  simp only [EvmAsm.Evm64.ExpArgs.expResultFromArgs, EvmAsm.Evm64.ExpArgs.expArgs,
    EvmAsm.Evm64.ExpArgs.expDynamicCostFromArgs, EvmAsm.Evm64.ExpArgs.expTotalGasFromArgs]
  rw [show EvmAsm.Evm64.EvmWord.exp (2 : EvmWord) (8 : EvmWord) = (256 : EvmWord) from by
    apply BitVec.eq_of_toNat_eq; rw [EvmAsm.Evm64.EvmWord.exp_correct]; decide]
  rw [EvmAsm.Evm64.ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)]
  rw [EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)]

theorem runExpStack?_zero_zero :
    runExpStack? { stack := [(0 : EvmWord), (0 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(1 : EvmWord)]
              dynamicGas := 0
              totalGas := 10 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_zero_zero
    [(99 : EvmWord)]

theorem runExpStack?_max_zero_exponent :
    runExpStack?
        { stack := [(-1 : EvmWord), (0 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(1 : EvmWord)]
              dynamicGas := 0
              totalGas := 10 }
          stack := [(99 : EvmWord)] } := by
  change EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?
      { stack := [(-1 : EvmWord), (0 : EvmWord), (99 : EvmWord)] } =
    some
      { effects :=
          { stackWords := [(1 : EvmWord)]
            dynamicGas := 0
            totalGas := 10 }
        stack := [(99 : EvmWord)] }
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_max_zero_exponent
    [(99 : EvmWord)]

theorem runExpStack?_one_exponent :
    runExpStack? { stack := [(7 : EvmWord), (1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(7 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_one_exponent 7
    [(99 : EvmWord)]

theorem runExpStack?_two_256 :
    runExpStack? { stack := [(2 : EvmWord), (256 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(0 : EvmWord)]
              dynamicGas := 100
              totalGas := 110 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_two_256 [(99 : EvmWord)]

theorem runExpStack?_one_max_exponent :
    runExpStack?
        { stack := [(1 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(1 : EvmWord)]
              dynamicGas := 1600
              totalGas := 1610 }
          stack := [(99 : EvmWord)] } := by
  change EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?
      { stack := [(1 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] } =
    some
      { effects :=
          { stackWords := [(1 : EvmWord)]
            dynamicGas := 1600
            totalGas := 1610 }
        stack := [(99 : EvmWord)] }
  rw [EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_one_left]
  rw [EvmAsm.Evm64.ExpArgs.expDynamicCostFromArgs_max_exponent]
  rw [EvmAsm.Evm64.ExpArgs.expTotalGasFromArgs_max_exponent]

theorem runExpStack?_zero_one :
    runExpStack? { stack := [(0 : EvmWord), (1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(0 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_zero_one
    [(99 : EvmWord)]

theorem runExpStack?_zero_max_exponent :
    runExpStack?
        { stack := [(0 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(0 : EvmWord)]
              dynamicGas := 1600
              totalGas := 1610 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_zero_max_exponent
    [(99 : EvmWord)]

theorem runExpStack?_two_128 :
    runExpStack? { stack := [(2 : EvmWord), (128 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^128)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_two_128 [(99 : EvmWord)]

theorem runExpStack?_max_one_exponent :
    runExpStack?
        { stack := [(-1 : EvmWord), (1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(-1 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  change EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?
      { stack := [(-1 : EvmWord), (1 : EvmWord), (99 : EvmWord)] } =
    some
      { effects :=
          { stackWords := [(-1 : EvmWord)]
            dynamicGas := 50
            totalGas := 60 }
        stack := [(99 : EvmWord)] }
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_max_one_exponent
    [(99 : EvmWord)]

theorem runExpStack?_two_64 :
    runExpStack? { stack := [(2 : EvmWord), (64 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^64)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_two_64 [(99 : EvmWord)]

theorem runExpStack?_two_255 :
    runExpStack? { stack := [(2 : EvmWord), (255 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^255)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_two_255 [(99 : EvmWord)]

theorem runExpStack?_underflow :
    runExpStack? { stack := [(2 : EvmWord)] } = none := rfl

theorem expStackValueVector_passed :
    checkVector? runExpStack? expStackValueVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-value"
    { stack := [(2 : EvmWord), (8 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(256 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_value

theorem expStackZeroZeroVector_passed :
    checkVector? runExpStack? expStackZeroZeroVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-zero-zero"
    { stack := [(0 : EvmWord), (0 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(1 : EvmWord)]
          dynamicGas := 0
          totalGas := 10 }
      stack := [(99 : EvmWord)] }
    runExpStack?_zero_zero

theorem expStackMaxZeroExponentVector_passed :
    checkVector? runExpStack? expStackMaxZeroExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-max-zero-exponent"
    { stack := [(-1 : EvmWord), (0 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(1 : EvmWord)]
          dynamicGas := 0
          totalGas := 10 }
      stack := [(99 : EvmWord)] }
    runExpStack?_max_zero_exponent

theorem expStackOneExponentVector_passed :
    checkVector? runExpStack? expStackOneExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-one-exponent"
    { stack := [(7 : EvmWord), (1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(7 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_one_exponent

theorem expStackTwo256Vector_passed :
    checkVector? runExpStack? expStackTwo256Vector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-two-256"
    { stack := [(2 : EvmWord), (256 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(0 : EvmWord)]
          dynamicGas := 100
          totalGas := 110 }
      stack := [(99 : EvmWord)] }
    runExpStack?_two_256

theorem expStackOneMaxExponentVector_passed :
    checkVector? runExpStack? expStackOneMaxExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-one-max-exponent"
    { stack := [(1 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(1 : EvmWord)]
          dynamicGas := 1600
          totalGas := 1610 }
      stack := [(99 : EvmWord)] }
    runExpStack?_one_max_exponent

theorem expStackZeroOneVector_passed :
    checkVector? runExpStack? expStackZeroOneVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-zero-one"
    { stack := [(0 : EvmWord), (1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(0 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_zero_one

theorem expStackZeroMaxExponentVector_passed :
    checkVector? runExpStack? expStackZeroMaxExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-zero-max-exponent"
    { stack := [(0 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(0 : EvmWord)]
          dynamicGas := 1600
          totalGas := 1610 }
      stack := [(99 : EvmWord)] }
    runExpStack?_zero_max_exponent

theorem expStackTwo128Vector_passed :
    checkVector? runExpStack? expStackTwo128Vector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-two-128"
    { stack := [(2 : EvmWord), (128 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [BitVec.ofNat 256 (2^128)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_two_128

theorem expStackMaxOneExponentVector_passed :
    checkVector? runExpStack? expStackMaxOneExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-max-one-exponent"
    { stack := [(-1 : EvmWord), (1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(-1 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_max_one_exponent

theorem expStackTwo64Vector_passed :
    checkVector? runExpStack? expStackTwo64Vector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-two-64"
    { stack := [(2 : EvmWord), (64 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [BitVec.ofNat 256 (2^64)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_two_64

theorem expStackTwo255Vector_passed :
    checkVector? runExpStack? expStackTwo255Vector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-two-255"
    { stack := [(2 : EvmWord), (255 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [BitVec.ofNat 256 (2^255)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_two_255

theorem expStackUnderflowVector_passed :
    checkVector? runExpStack? expStackUnderflowVector =
      .errored "exp-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runExpStack?
    "exp-stack-underflow"
    "stack-underflow"
    { stack := [(2 : EvmWord)] }
    runExpStack?_underflow

/-- Compact checked-vector batch for EXP stack execution.
    Distinctive token: ExpStackExecutionConformance.expStackConformanceVectors #92 #125. -/
def expStackConformanceVectors : List CheckResult :=
  checkBatch? runExpStack? expStackConformanceTestVectors

theorem expStackConformanceVectors_passed :
    expStackConformanceVectors =
      [ .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .errored "exp-stack-underflow" "stack-underflow"
      ] := by
  simp [expStackConformanceVectors, expStackConformanceTestVectors,
    expStackValueVector_passed, expStackZeroZeroVector_passed,
    expStackMaxZeroExponentVector_passed,
    expStackOneExponentVector_passed,
    expStackTwo256Vector_passed,
    expStackOneMaxExponentVector_passed,
    expStackZeroOneVector_passed,
    expStackZeroMaxExponentVector_passed,
    expStackMaxOneExponentVector_passed,
    expStackTwo128Vector_passed, expStackTwo64Vector_passed,
    expStackTwo255Vector_passed,
    expStackUnderflowVector_passed]

end ExpStackExecution
end Conformance
end EvmAsm.EL
