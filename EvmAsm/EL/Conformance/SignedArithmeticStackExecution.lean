/-
  EvmAsm.EL.Conformance.SignedArithmeticStackExecution

  Lean-side conformance vectors for the SDIV/SMOD stack execution bridges
  (GH #90 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.Evm64.SDiv.StackExecutionBridge
import EvmAsm.Evm64.SMod.StackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace SignedArithmeticStackExecution

abbrev EvmWord := EvmAsm.Evm64.EvmWord

abbrev SDivStackState := EvmAsm.Evm64.SDivStackExecutionBridge.SDivStackState

abbrev SDivStackResult := EvmAsm.Evm64.SDivStackExecutionBridge.SDivStackResult

abbrev SModStackState := EvmAsm.Evm64.SModStackExecutionBridge.SModStackState

abbrev SModStackResult := EvmAsm.Evm64.SModStackExecutionBridge.SModStackResult

deriving instance DecidableEq for
  EvmAsm.Evm64.SDivStackExecutionBridge.SDivVisibleEffects

deriving instance DecidableEq for
  EvmAsm.Evm64.SDivStackExecutionBridge.SDivStackResult

deriving instance DecidableEq for
  EvmAsm.Evm64.SModStackExecutionBridge.SModVisibleEffects

deriving instance DecidableEq for
  EvmAsm.Evm64.SModStackExecutionBridge.SModStackResult

def runSDivStack? (input : SDivStackState) : Option SDivStackResult :=
  EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack? input

def runSModStack? (input : SModStackState) : Option SModStackResult :=
  EvmAsm.Evm64.SModStackExecutionBridge.runSModStack? input

def sdivZeroDivisorVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-zero-divisor"
    input := { stack := [9, 0, 42] }
    expected :=
      .value
        { effects := { stackWords := [0] }
          stack := [42] } }

def sdivIntMinNegOneVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-int-min-neg-one"
    input := { stack := [BitVec.intMin 256, (-1 : EvmWord), 42] }
    expected :=
      .value
        { effects := { stackWords := [BitVec.intMin 256] }
          stack := [42] } }

def sdivPosPosVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-pos-pos"
    input := { stack := [9, 2, 42] }
    expected :=
      .value
        { effects := { stackWords := [4] }
          stack := [42] } }

def sdivNegNegVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-neg-neg"
    input := { stack := [(-9 : EvmWord), (-2 : EvmWord), 42] }
    expected :=
      .value
        { effects := { stackWords := [4] }
          stack := [42] } }

def sdivPosNegTruncVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-pos-neg-trunc"
    input := { stack := [7, (-2 : EvmWord), 42] }
    expected :=
      .value
        { effects := { stackWords := [(-3 : EvmWord)] }
          stack := [42] } }

def sdivUnderflowVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-underflow"
    input := { stack := [7] }
    expected := .error "stack-underflow" }

def smodZeroDivisorVector : TestVector SModStackState SModStackResult :=
  { id := "smod-stack-zero-divisor"
    input := { stack := [9, 0, 42] }
    expected :=
      .value
        { effects := { stackWords := [0] }
          stack := [42] } }

def smodNegPosSignVector : TestVector SModStackState SModStackResult :=
  { id := "smod-stack-neg-pos-sign"
    input := { stack := [(-3 : EvmWord), 2, 42] }
    expected :=
      .value
        { effects := { stackWords := [(-1 : EvmWord)] }
          stack := [42] } }

def smodPosNegSignVector : TestVector SModStackState SModStackResult :=
  { id := "smod-stack-pos-neg-sign"
    input := { stack := [3, (-2 : EvmWord), 42] }
    expected :=
      .value
        { effects := { stackWords := [1] }
          stack := [42] } }

def smodUnderflowVector : TestVector SModStackState SModStackResult :=
  { id := "smod-stack-underflow"
    input := { stack := [] }
    expected := .error "stack-underflow" }

/-- SDIV stack conformance inputs as reusable test vectors.
    Distinctive token:
    SignedArithmeticStackExecutionConformance.sdivStackConformanceTestVectors #90 #125. -/
def sdivStackConformanceTestVectors : List (TestVector SDivStackState SDivStackResult) :=
  [ sdivZeroDivisorVector
  , sdivIntMinNegOneVector
  , sdivPosPosVector
  , sdivNegNegVector
  , sdivPosNegTruncVector
  , sdivUnderflowVector
  ]

/-- SMOD stack conformance inputs as reusable test vectors.
    Distinctive token:
    SignedArithmeticStackExecutionConformance.smodStackConformanceTestVectors #90 #125. -/
def smodStackConformanceTestVectors : List (TestVector SModStackState SModStackResult) :=
  [ smodZeroDivisorVector
  , smodNegPosSignVector
  , smodPosNegSignVector
  , smodUnderflowVector
  ]

theorem sdivStackConformanceTestVectors_length :
    sdivStackConformanceTestVectors.length = 6 := rfl

theorem smodStackConformanceTestVectors_length :
    smodStackConformanceTestVectors.length = 4 := rfl

def signedArithmeticConformanceTestVectorCount : Nat :=
  sdivStackConformanceTestVectors.length + smodStackConformanceTestVectors.length

theorem signedArithmeticConformanceTestVectorCount_eq :
    signedArithmeticConformanceTestVectorCount = 10 := rfl

def sdivStackConformanceVectorIds : List String :=
  sdivStackConformanceTestVectors.map TestVector.id

def smodStackConformanceVectorIds : List String :=
  smodStackConformanceTestVectors.map TestVector.id

def signedArithmeticConformanceVectorIds : List String :=
  sdivStackConformanceVectorIds ++ smodStackConformanceVectorIds

theorem sdivStackConformanceVectorIds_eq :
    sdivStackConformanceVectorIds =
      [ "sdiv-stack-zero-divisor"
      , "sdiv-stack-int-min-neg-one"
      , "sdiv-stack-pos-pos"
      , "sdiv-stack-neg-neg"
      , "sdiv-stack-pos-neg-trunc"
      , "sdiv-stack-underflow"
      ] := rfl

theorem smodStackConformanceVectorIds_eq :
    smodStackConformanceVectorIds =
      [ "smod-stack-zero-divisor"
      , "smod-stack-neg-pos-sign"
      , "smod-stack-pos-neg-sign"
      , "smod-stack-underflow"
      ] := rfl

theorem signedArithmeticConformanceVectorIds_eq :
    signedArithmeticConformanceVectorIds =
      [ "sdiv-stack-zero-divisor"
      , "sdiv-stack-int-min-neg-one"
      , "sdiv-stack-pos-pos"
      , "sdiv-stack-neg-neg"
      , "sdiv-stack-pos-neg-trunc"
      , "sdiv-stack-underflow"
      , "smod-stack-zero-divisor"
      , "smod-stack-neg-pos-sign"
      , "smod-stack-pos-neg-sign"
      , "smod-stack-underflow"
      ] := rfl

theorem sdivStackConformanceVectorIds_length :
    sdivStackConformanceVectorIds.length = 6 := rfl

theorem smodStackConformanceVectorIds_length :
    smodStackConformanceVectorIds.length = 4 := rfl

theorem signedArithmeticConformanceVectorIds_length :
    signedArithmeticConformanceVectorIds.length = 10 := rfl

theorem sdivStackConformanceVectorIds_nodup :
    sdivStackConformanceVectorIds.Nodup := by
  decide

theorem smodStackConformanceVectorIds_nodup :
    smodStackConformanceVectorIds.Nodup := by
  decide

theorem signedArithmeticConformanceVectorIds_nodup :
    signedArithmeticConformanceVectorIds.Nodup := by
  decide

def signedArithmeticValueVectorIds : List String :=
  [ "sdiv-stack-zero-divisor"
  , "sdiv-stack-int-min-neg-one"
  , "sdiv-stack-pos-pos"
  , "sdiv-stack-neg-neg"
  , "sdiv-stack-pos-neg-trunc"
  , "smod-stack-zero-divisor"
  , "smod-stack-neg-pos-sign"
  , "smod-stack-pos-neg-sign"
  ]

def signedArithmeticErrorVectorIds : List String :=
  [ "sdiv-stack-underflow"
  , "smod-stack-underflow"
  ]

theorem signedArithmeticValueVectorIds_length :
    signedArithmeticValueVectorIds.length = 8 := rfl

theorem signedArithmeticErrorVectorIds_length :
    signedArithmeticErrorVectorIds.length = 2 := rfl

theorem signedArithmeticValueVectorIds_nodup :
    signedArithmeticValueVectorIds.Nodup := by
  decide

theorem signedArithmeticErrorVectorIds_nodup :
    signedArithmeticErrorVectorIds.Nodup := by
  decide

theorem signedArithmeticValueVectorIds_subset_all :
    ∀ id ∈ signedArithmeticValueVectorIds,
      id ∈ signedArithmeticConformanceVectorIds := by
  decide

theorem signedArithmeticErrorVectorIds_subset_all :
    ∀ id ∈ signedArithmeticErrorVectorIds,
      id ∈ signedArithmeticConformanceVectorIds := by
  decide

theorem signedArithmeticValueVectorIds_no_error :
    ∀ id ∈ signedArithmeticValueVectorIds,
      id ∉ signedArithmeticErrorVectorIds := by
  decide

theorem runSDivStack?_zero_divisor_vector :
    runSDivStack? { stack := [(9 : EvmWord), 0, 42] } =
      some { effects := { stackWords := [0] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_zero_divisor
      (9 : EvmWord) [(42 : EvmWord)]

theorem runSDivStack?_intMin_neg_one_vector :
    runSDivStack? { stack := [BitVec.intMin 256, (-1 : EvmWord), 42] } =
      some { effects := { stackWords := [BitVec.intMin 256] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_intMin_neg_one
      [(42 : EvmWord)]

theorem runSDivStack?_pos_pos_vector :
    runSDivStack? { stack := [(9 : EvmWord), (2 : EvmWord), 42] } =
      some { effects := { stackWords := [4] }, stack := [42] } := by
  have h : EvmAsm.Evm64.SDivArgs.sdivResultFromArgs
      (EvmAsm.Evm64.SDivArgs.sdivArgs (9 : EvmWord) (2 : EvmWord)) = (4 : EvmWord) := by
    unfold EvmAsm.Evm64.SDivArgs.sdivResultFromArgs EvmAsm.Evm64.SDivArgs.sdivArgs
      EvmAsm.Evm64.EvmWord.sdiv
    decide
  unfold runSDivStack?
  rw [EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_cons, h]

theorem runSDivStack?_neg_neg_vector :
    runSDivStack? { stack := [(-9 : EvmWord), (-2 : EvmWord), 42] } =
      some { effects := { stackWords := [4] }, stack := [42] } := by
  have h : EvmAsm.Evm64.SDivArgs.sdivResultFromArgs
      (EvmAsm.Evm64.SDivArgs.sdivArgs (-9 : EvmWord) (-2 : EvmWord)) = (4 : EvmWord) := by
    unfold EvmAsm.Evm64.SDivArgs.sdivResultFromArgs EvmAsm.Evm64.SDivArgs.sdivArgs
      EvmAsm.Evm64.EvmWord.sdiv
    decide
  unfold runSDivStack?
  rw [EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_cons, h]

theorem runSDivStack?_pos_neg_trunc_vector :
    runSDivStack? { stack := [(7 : EvmWord), (-2 : EvmWord), 42] } =
      some { effects := { stackWords := [(-3 : EvmWord)] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_pos_neg_trunc
      [(42 : EvmWord)]

theorem runSDivStack?_underflow_vector :
    runSDivStack? { stack := [(7 : EvmWord)] } = none := rfl

theorem runSModStack?_zero_divisor_vector :
    runSModStack? { stack := [(9 : EvmWord), 0, 42] } =
      some { effects := { stackWords := [0] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SModStackExecutionBridge.runSModStack?_zero_divisor
      (9 : EvmWord) [(42 : EvmWord)]

theorem runSModStack?_neg_pos_sign_vector :
    runSModStack? { stack := [(-3 : EvmWord), 2, 42] } =
      some { effects := { stackWords := [(-1 : EvmWord)] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SModStackExecutionBridge.runSModStack?_neg_pos_sign
      [(42 : EvmWord)]

theorem runSModStack?_pos_neg_sign_vector :
    runSModStack? { stack := [(3 : EvmWord), (-2 : EvmWord), 42] } =
      some { effects := { stackWords := [1] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SModStackExecutionBridge.runSModStack?_pos_neg_sign
      [(42 : EvmWord)]

theorem runSModStack?_underflow_vector :
    runSModStack? { stack := [] } = none := rfl

theorem sdivZeroDivisorVector_passed :
    checkVector? runSDivStack? sdivZeroDivisorVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-zero-divisor"
    { stack := [(9 : EvmWord), 0, 42] }
    { effects := { stackWords := [0] }, stack := [(42 : EvmWord)] }
    runSDivStack?_zero_divisor_vector

theorem sdivIntMinNegOneVector_passed :
    checkVector? runSDivStack? sdivIntMinNegOneVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-int-min-neg-one"
    { stack := [BitVec.intMin 256, (-1 : EvmWord), 42] }
    { effects := { stackWords := [BitVec.intMin 256] }, stack := [(42 : EvmWord)] }
    runSDivStack?_intMin_neg_one_vector

theorem sdivPosPosVector_passed :
    checkVector? runSDivStack? sdivPosPosVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-pos-pos"
    { stack := [(9 : EvmWord), (2 : EvmWord), 42] }
    { effects := { stackWords := [4] }, stack := [(42 : EvmWord)] }
    runSDivStack?_pos_pos_vector

theorem sdivNegNegVector_passed :
    checkVector? runSDivStack? sdivNegNegVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-neg-neg"
    { stack := [(-9 : EvmWord), (-2 : EvmWord), 42] }
    { effects := { stackWords := [4] }, stack := [(42 : EvmWord)] }
    runSDivStack?_neg_neg_vector

theorem sdivPosNegTruncVector_passed :
    checkVector? runSDivStack? sdivPosNegTruncVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-pos-neg-trunc"
    { stack := [(7 : EvmWord), (-2 : EvmWord), 42] }
    { effects := { stackWords := [(-3 : EvmWord)] }, stack := [(42 : EvmWord)] }
    runSDivStack?_pos_neg_trunc_vector

theorem sdivUnderflowVector_passed :
    checkVector? runSDivStack? sdivUnderflowVector =
      .errored "sdiv-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runSDivStack?
    "sdiv-stack-underflow"
    "stack-underflow"
    { stack := [(7 : EvmWord)] }
    runSDivStack?_underflow_vector

theorem smodZeroDivisorVector_passed :
    checkVector? runSModStack? smodZeroDivisorVector = .passed :=
  checkVector?_some_passed runSModStack?
    "smod-stack-zero-divisor"
    { stack := [(9 : EvmWord), 0, 42] }
    { effects := { stackWords := [0] }, stack := [(42 : EvmWord)] }
    runSModStack?_zero_divisor_vector

theorem smodNegPosSignVector_passed :
    checkVector? runSModStack? smodNegPosSignVector = .passed :=
  checkVector?_some_passed runSModStack?
    "smod-stack-neg-pos-sign"
    { stack := [(-3 : EvmWord), 2, 42] }
    { effects := { stackWords := [(-1 : EvmWord)] }, stack := [(42 : EvmWord)] }
    runSModStack?_neg_pos_sign_vector

theorem smodPosNegSignVector_passed :
    checkVector? runSModStack? smodPosNegSignVector = .passed :=
  checkVector?_some_passed runSModStack?
    "smod-stack-pos-neg-sign"
    { stack := [(3 : EvmWord), (-2 : EvmWord), 42] }
    { effects := { stackWords := [1] }, stack := [(42 : EvmWord)] }
    runSModStack?_pos_neg_sign_vector

theorem smodUnderflowVector_passed :
    checkVector? runSModStack? smodUnderflowVector =
      .errored "smod-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runSModStack?
    "smod-stack-underflow"
    "stack-underflow"
    { stack := [] }
    runSModStack?_underflow_vector

/-- Compact checked-vector batch for signed arithmetic stack execution.
    Distinctive token:
    SignedArithmeticStackExecutionConformance.signedArithmeticConformanceVectors #90 #125. -/
def signedArithmeticConformanceVectors : List CheckResult :=
  checkBatch? runSDivStack? sdivStackConformanceTestVectors ++
    checkBatch? runSModStack? smodStackConformanceTestVectors

theorem signedArithmeticConformanceVectors_passed :
    signedArithmeticConformanceVectors =
      [ .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .errored "sdiv-stack-underflow" "stack-underflow"
      , .passed
      , .passed
      , .passed
      , .errored "smod-stack-underflow" "stack-underflow"
      ] := by
  simp [signedArithmeticConformanceVectors, sdivZeroDivisorVector_passed,
    sdivStackConformanceTestVectors, smodStackConformanceTestVectors,
    sdivIntMinNegOneVector_passed, sdivPosPosVector_passed,
    sdivNegNegVector_passed, sdivPosNegTruncVector_passed,
    sdivUnderflowVector_passed, smodZeroDivisorVector_passed,
    smodNegPosSignVector_passed, smodPosNegSignVector_passed,
    smodUnderflowVector_passed]

end SignedArithmeticStackExecution
end Conformance
end EvmAsm.EL
