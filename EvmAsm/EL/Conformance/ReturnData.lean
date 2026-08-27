/-
  EvmAsm.EL.Conformance.ReturnData

  Initial Lean-side conformance vector for executable returndata helpers
  (GH #125 / GH #114).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.ReturnData.CopyExec
public import EvmAsm.Evm64.ReturnData.CopyArgsStackDecode

@[expose] public section

namespace EvmAsm.EL
namespace Conformance
namespace ReturnData

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Input shape for a RETURNDATACOPY executable-helper conformance vector. -/
structure ReturnDataCopyInput where
  data : List (BitVec 8)
  destOffset : EvmWord
  dataOffset : EvmWord
  size : EvmWord
  deriving Repr

/-- Input shape for a RETURNDATACOPY stack-decoder conformance vector. -/
structure ReturnDataCopyStackInput where
  data : List (BitVec 8)
  stack : List EvmWord
  deriving Repr

def runReturnDataCopy (input : ReturnDataCopyInput) : List (BitVec 8) :=
  EvmAsm.Evm64.ReturnDataCopyExec.copiedBytesFromArgs
    input.data
    (EvmAsm.Evm64.ReturnDataCopyArgs.copyArgs
      input.destOffset input.dataOffset input.size)

def runReturnDataCopyStack? (input : ReturnDataCopyStackInput) :
    Option (List (BitVec 8)) :=
  EvmAsm.Evm64.ReturnDataCopyArgsStackDecode.decodeReturnDataCopyStack? input.stack
    |>.map (EvmAsm.Evm64.ReturnDataCopyExec.copiedBytesFromArgs input.data)

/-- RETURNDATACOPY zero-pads bytes copied past the end of returndata.
    Distinctive token: returnDataCopyZeroPadVector #125 #114. -/
def returnDataCopyZeroPadVector :
    TestVector ReturnDataCopyInput (List (BitVec 8)) :=
  { id := "returndatacopy-zero-pad"
    input :=
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        destOffset := 32
        dataOffset := 1
        size := 4 }
    expected := .value [(0xbb : BitVec 8), 0, 0, 0] }

/-- Stack-decoded RETURNDATACOPY uses stack words as
    `destOffset, dataOffset, size`; the executable helper here returns only
    the copied byte sequence. Distinctive token: runReturnDataCopyStack?
    #107 #114 #125. -/
def returnDataCopyStackVector :
    TestVector ReturnDataCopyStackInput (List (BitVec 8)) :=
  { id := "returndatacopy-stack-decode"
    input :=
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        stack := [(32 : EvmWord), (1 : EvmWord), (4 : EvmWord)] }
    expected := .value [(0xbb : BitVec 8), 0, 0, 0] }

/-- RETURNDATACOPY stack decoding fails unless all three stack operands exist. -/
def returnDataCopyStackUnderflowVector :
    TestVector ReturnDataCopyStackInput (List (BitVec 8)) :=
  { id := "returndatacopy-stack-underflow"
    input :=
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        stack := [(32 : EvmWord), (1 : EvmWord)] }
    expected := .error "stack-underflow" }

theorem runReturnDataCopy_zeroPad :
    runReturnDataCopy
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        destOffset := 32
        dataOffset := 1
        size := 4 } =
      [(0xbb : BitVec 8), 0, 0, 0] := rfl

theorem runReturnDataCopyStack_decoded :
    runReturnDataCopyStack?
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        stack := [(32 : EvmWord), (1 : EvmWord), (4 : EvmWord)] } =
      some [(0xbb : BitVec 8), 0, 0, 0] := rfl

theorem runReturnDataCopyStack_underflow :
    runReturnDataCopyStack?
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        stack := [(32 : EvmWord), (1 : EvmWord)] } = none := rfl

theorem returnDataCopyZeroPadVector_passed :
    checkVector runReturnDataCopy returnDataCopyZeroPadVector = .passed :=
  checkVector_value_passed runReturnDataCopy
    "returndatacopy-zero-pad"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
      destOffset := (32 : EvmWord)
      dataOffset := (1 : EvmWord)
      size := (4 : EvmWord) }
    [(0xbb : BitVec 8), 0, 0, 0]
    runReturnDataCopy_zeroPad

theorem returnDataCopyStackVector_passed :
    checkVector? runReturnDataCopyStack? returnDataCopyStackVector = .passed :=
  checkVector?_some_passed runReturnDataCopyStack?
    "returndatacopy-stack-decode"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
      stack := [(32 : EvmWord), (1 : EvmWord), (4 : EvmWord)] }
    [(0xbb : BitVec 8), 0, 0, 0]
    runReturnDataCopyStack_decoded

theorem returnDataCopyStackUnderflowVector_errored :
    checkVector? runReturnDataCopyStack? returnDataCopyStackUnderflowVector =
      .errored "returndatacopy-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runReturnDataCopyStack?
    "returndatacopy-stack-underflow"
    "stack-underflow"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
      stack := [(32 : EvmWord), (1 : EvmWord)] }
    runReturnDataCopyStack_underflow

/-- Vector IDs for returndata executable-helper conformance coverage.
    Distinctive token: returnDataConformanceVectorIds #125 #114. -/
def returnDataConformanceVectorIds : List String :=
  [ returnDataCopyZeroPadVector.id
  , returnDataCopyStackVector.id
  , returnDataCopyStackUnderflowVector.id
  ]

theorem returnDataConformanceVectorIds_eq :
    returnDataConformanceVectorIds =
      [ "returndatacopy-zero-pad"
      , "returndatacopy-stack-decode"
      , "returndatacopy-stack-underflow"
      ] := rfl

theorem returnDataConformanceVectorIds_length :
    returnDataConformanceVectorIds.length = 3 := rfl

theorem returnDataConformanceVectorIds_nodup :
    returnDataConformanceVectorIds.Nodup := by
  decide

/-- Compact checked-vector batch for returndata executable helpers.
    Distinctive token: returnDataConformanceVectors #125 #114. -/
def returnDataConformanceVectors : List CheckResult :=
  [ checkVector runReturnDataCopy returnDataCopyZeroPadVector
  , checkVector? runReturnDataCopyStack? returnDataCopyStackVector
  , checkVector? runReturnDataCopyStack? returnDataCopyStackUnderflowVector
  ]

theorem returnDataConformanceVectors_passed :
    returnDataConformanceVectors =
      [.passed, .passed,
        .errored "returndatacopy-stack-underflow" "stack-underflow"] := by
  simp [returnDataConformanceVectors, returnDataCopyZeroPadVector_passed]
  exact ⟨returnDataCopyStackVector_passed,
    returnDataCopyStackUnderflowVector_errored⟩

end ReturnData
end Conformance
end EvmAsm.EL
