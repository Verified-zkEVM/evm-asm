/-
  EvmAsm.EL.Conformance.Calldata

  Initial Lean-side conformance vectors for executable calldata helpers
  (GH #125).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.Calldata.Basic
public import EvmAsm.Evm64.Calldata.Size
public import EvmAsm.Evm64.Calldata.LoadArgsStackDecode
public import EvmAsm.Evm64.Calldata.CopyArgsStackDecode

@[expose] public section

namespace EvmAsm.EL
namespace Conformance
namespace Calldata

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Input shape for a CALLDATALOAD executable-helper conformance vector. -/
structure CallDataLoadInput where
  data : List (BitVec 8)
  offset : Nat
  deriving Repr

/-- Input shape for a CALLDATALOAD stack-decoder conformance vector. -/
structure CallDataLoadStackInput where
  data : List (BitVec 8)
  stack : List EvmWord
  deriving Repr

/-- Input shape for a CALLDATASIZE executable-helper conformance vector. -/
structure CallDataSizeInput where
  data : List (BitVec 8)
  deriving Repr

/-- Input shape for a CALLDATACOPY executable-helper conformance vector. -/
structure CallDataCopyInput where
  data : List (BitVec 8)
  dataOffset : Nat
  size : Nat
  deriving Repr

/-- Input shape for a CALLDATACOPY stack-decoder conformance vector. -/
structure CallDataCopyStackInput where
  data : List (BitVec 8)
  stack : List EvmWord
  deriving Repr

def runCallDataLoad (input : CallDataLoadInput) : EvmWord :=
  EvmAsm.Evm64.Calldata.callDataLoadWord input.data input.offset

def runCallDataLoadStack? (input : CallDataLoadStackInput) :
    Option EvmWord :=
  EvmAsm.Evm64.CallDataLoadArgsStackDecode.decodeCallDataLoadStack? input.stack
    |>.map (EvmAsm.Evm64.CallDataLoadArgs.loadedWordFromArgs input.data)

def runCallDataSize (input : CallDataSizeInput) : EvmWord :=
  EvmAsm.Evm64.Calldata.callDataSizeOf input.data

def runCallDataCopy (input : CallDataCopyInput) : List (BitVec 8) :=
  EvmAsm.Evm64.Calldata.callDataCopyBytes
    input.data input.dataOffset input.size

def runCallDataCopyStack? (input : CallDataCopyStackInput) :
    Option (List (BitVec 8)) :=
  EvmAsm.Evm64.CallDataCopyArgsStackDecode.decodeCallDataCopyStack? input.stack
    |>.map (fun args =>
      EvmAsm.Evm64.Calldata.callDataCopyBytes input.data
        (EvmAsm.Evm64.CallDataCopyArgs.sourceOffsetNat args)
        (EvmAsm.Evm64.CallDataCopyArgs.sizeNat args))

/-- CALLDATALOAD reads zero when the requested 32-byte window starts at the
    end of calldata. Distinctive token: callDataLoadOutOfBoundsVector. -/
def callDataLoadOutOfBoundsVector : TestVector CallDataLoadInput EvmWord :=
  { id := "calldataload-oob-zero"
    input := { data := [(0x12 : BitVec 8)], offset := 1 }
    expected := .value 0 }

/-- Stack-decoded CALLDATALOAD uses the top EVM stack word as its calldata
    byte offset. Distinctive token: runCallDataLoadStack? #104 #125. -/
def callDataLoadStackVector : TestVector CallDataLoadStackInput EvmWord :=
  { id := "calldataload-stack-decode"
    input := { data := [(0x12 : BitVec 8)], stack := [(1 : EvmWord), 0] }
    expected := .value 0 }

/-- CALLDATALOAD stack decoding fails when the input stack is empty. -/
def callDataLoadStackUnderflowVector :
    TestVector CallDataLoadStackInput EvmWord :=
  { id := "calldataload-stack-underflow"
    input := { data := [(0x12 : BitVec 8)], stack := [] }
    expected := .error "stack-underflow" }

/-- CALLDATASIZE pushes the byte length of calldata as an EVM word. -/
def callDataSizeTwoBytesVector : TestVector CallDataSizeInput EvmWord :=
  { id := "calldatasize-two-bytes"
    input := { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)] }
    expected := .value 2 }

/-- CALLDATASIZE on empty calldata returns zero.
    Distinctive token: callDataSizeEmptyVector #104 #125. -/
def callDataSizeEmptyVector : TestVector CallDataSizeInput EvmWord :=
  { id := "calldatasize-empty"
    input := { data := [] }
    expected := .value 0 }

/-- CALLDATACOPY zero-pads bytes copied past the end of calldata.
    Distinctive token: callDataCopyZeroPadVector. -/
def callDataCopyZeroPadVector :
    TestVector CallDataCopyInput (List (BitVec 8)) :=
  { id := "calldatacopy-zero-pad"
    input := { data := [(0xaa : BitVec 8)], dataOffset := 0, size := 3 }
    expected := .value [(0xaa : BitVec 8), 0, 0] }

/-- Stack-decoded CALLDATACOPY uses stack words as
    `destOffset, dataOffset, size`; the executable helper here returns only
    the copied byte sequence. Distinctive token: runCallDataCopyStack?
    #104 #125. -/
def callDataCopyStackVector :
    TestVector CallDataCopyStackInput (List (BitVec 8)) :=
  { id := "calldatacopy-stack-decode"
    input := { data := [(0xaa : BitVec 8)], stack := [0, 0, (3 : EvmWord)] }
    expected := .value [(0xaa : BitVec 8), 0, 0] }

/-- CALLDATACOPY stack decoding fails unless all three stack operands exist. -/
def callDataCopyStackUnderflowVector :
    TestVector CallDataCopyStackInput (List (BitVec 8)) :=
  { id := "calldatacopy-stack-underflow"
    input := { data := [(0xaa : BitVec 8)], stack := [0, 0] }
    expected := .error "stack-underflow" }

theorem runCallDataLoad_outOfBounds :
    runCallDataLoad { data := [(0x12 : BitVec 8)], offset := 1 } = 0 := by
  exact EvmAsm.Evm64.Calldata.callDataLoadWord_of_ge_length (by decide)

theorem runCallDataLoadStack_decoded :
    runCallDataLoadStack?
      { data := [(0x12 : BitVec 8)], stack := [(1 : EvmWord), 0] } =
      some 0 := by
  unfold runCallDataLoadStack?
  rw [EvmAsm.Evm64.CallDataLoadArgsStackDecode.decodeCallDataLoadStack?_cons]
  simp [EvmAsm.Evm64.CallDataLoadArgs.loadedWordFromArgs,
    EvmAsm.Evm64.CallDataLoadArgs.loadArgs,
    EvmAsm.Evm64.CallDataLoadArgs.offsetNat]
  exact EvmAsm.Evm64.Calldata.callDataLoadWord_of_ge_length
    (data := [(0x12 : BitVec 8)]) (offset := 1) (by decide)

theorem runCallDataLoadStack_underflow :
    runCallDataLoadStack?
      { data := [(0x12 : BitVec 8)], stack := [] } = none := rfl

theorem runCallDataSize_twoBytes :
    runCallDataSize { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)] } =
      (2 : EvmWord) := rfl

theorem runCallDataSize_empty :
    runCallDataSize { data := [] } = (0 : EvmWord) := rfl

theorem runCallDataCopy_zeroPad :
    runCallDataCopy
      { data := [(0xaa : BitVec 8)], dataOffset := 0, size := 3 } =
      [(0xaa : BitVec 8), 0, 0] := rfl

theorem runCallDataCopyStack_decoded :
    runCallDataCopyStack?
      { data := [(0xaa : BitVec 8)], stack := [0, 0, (3 : EvmWord)] } =
      some [(0xaa : BitVec 8), 0, 0] := rfl

theorem runCallDataCopyStack_underflow :
    runCallDataCopyStack?
      { data := [(0xaa : BitVec 8)], stack := [0, 0] } = none := rfl

theorem callDataLoadOutOfBoundsVector_passed :
    checkVector runCallDataLoad callDataLoadOutOfBoundsVector = .passed :=
  checkVector_value_passed runCallDataLoad
    "calldataload-oob-zero"
    { data := [(0x12 : BitVec 8)], offset := 1 }
    (0 : EvmWord)
    runCallDataLoad_outOfBounds

theorem callDataLoadStackVector_passed :
    checkVector? runCallDataLoadStack? callDataLoadStackVector = .passed :=
  checkVector?_some_passed runCallDataLoadStack?
    "calldataload-stack-decode"
    { data := [(0x12 : BitVec 8)], stack := [(1 : EvmWord), 0] }
    (0 : EvmWord)
    runCallDataLoadStack_decoded

theorem callDataLoadStackUnderflowVector_errored :
    checkVector? runCallDataLoadStack? callDataLoadStackUnderflowVector =
      .errored "calldataload-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runCallDataLoadStack?
    "calldataload-stack-underflow"
    "stack-underflow"
    { data := [(0x12 : BitVec 8)], stack := [] }
    runCallDataLoadStack_underflow

theorem callDataSizeTwoBytesVector_passed :
    checkVector runCallDataSize callDataSizeTwoBytesVector = .passed :=
  checkVector_value_passed runCallDataSize
    "calldatasize-two-bytes"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)] }
    (2 : EvmWord)
    runCallDataSize_twoBytes

theorem callDataSizeEmptyVector_passed :
    checkVector runCallDataSize callDataSizeEmptyVector = .passed :=
  checkVector_value_passed runCallDataSize
    "calldatasize-empty"
    { data := [] }
    (0 : EvmWord)
    runCallDataSize_empty

theorem callDataCopyZeroPadVector_passed :
    checkVector runCallDataCopy callDataCopyZeroPadVector = .passed :=
  checkVector_value_passed runCallDataCopy
    "calldatacopy-zero-pad"
    { data := [(0xaa : BitVec 8)], dataOffset := 0, size := 3 }
    [(0xaa : BitVec 8), 0, 0]
    runCallDataCopy_zeroPad

theorem callDataCopyStackVector_passed :
    checkVector? runCallDataCopyStack? callDataCopyStackVector = .passed :=
  checkVector?_some_passed runCallDataCopyStack?
    "calldatacopy-stack-decode"
    { data := [(0xaa : BitVec 8)], stack := [0, 0, (3 : EvmWord)] }
    [(0xaa : BitVec 8), 0, 0]
    runCallDataCopyStack_decoded

theorem callDataCopyStackUnderflowVector_errored :
    checkVector? runCallDataCopyStack? callDataCopyStackUnderflowVector =
      .errored "calldatacopy-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runCallDataCopyStack?
    "calldatacopy-stack-underflow"
    "stack-underflow"
    { data := [(0xaa : BitVec 8)], stack := [0, 0] }
    runCallDataCopyStack_underflow

/-- Compact initial checked-vector batch for calldata executable helpers.
    Distinctive token: calldataConformanceVectors. -/
def calldataConformanceVectors : List CheckResult :=
  [ checkVector runCallDataLoad callDataLoadOutOfBoundsVector
  , checkVector? runCallDataLoadStack? callDataLoadStackVector
  , checkVector? runCallDataLoadStack? callDataLoadStackUnderflowVector
  , checkVector runCallDataSize callDataSizeTwoBytesVector
  , checkVector runCallDataSize callDataSizeEmptyVector
  , checkVector runCallDataCopy callDataCopyZeroPadVector
  , checkVector? runCallDataCopyStack? callDataCopyStackVector
  , checkVector? runCallDataCopyStack? callDataCopyStackUnderflowVector
  ]

theorem calldataConformanceVectors_passed :
    calldataConformanceVectors =
      [.passed, .passed, .errored "calldataload-stack-underflow" "stack-underflow",
        .passed, .passed, .passed, .passed,
        .errored "calldatacopy-stack-underflow" "stack-underflow"] := by
  simp [calldataConformanceVectors, callDataLoadOutOfBoundsVector_passed,
    callDataLoadStackVector_passed, callDataLoadStackUnderflowVector_errored,
    callDataSizeTwoBytesVector_passed, callDataSizeEmptyVector_passed,
    callDataCopyZeroPadVector_passed, callDataCopyStackVector_passed,
    callDataCopyStackUnderflowVector_errored]

end Calldata
end Conformance
end EvmAsm.EL
