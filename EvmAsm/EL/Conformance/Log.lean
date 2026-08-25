/-
  EvmAsm.EL.Conformance.Log

  Compact Lean-side conformance vectors for LOG data memory helpers
  (GH #125 / GH #112).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.EL.LogDataBridge

@[expose] public section

namespace EvmAsm.EL
namespace Conformance
namespace Log

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev LogArgs := EvmAsm.Evm64.LogArgs.Args

/-- Input shape for LOG data-memory executable-helper conformance vectors. -/
structure LogDataInput where
  memory : List Byte
  args : LogArgs
  deriving Repr

def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0

def runLogData (input : LogDataInput) : List Byte :=
  EvmAsm.EL.LogDataBridge.logDataFromMemory
    (readByteAt input.memory) input.args

def mkLogArgs (offset size : EvmWord) (topics : List EvmWord) : LogArgs :=
  { data := { offset := offset, size := size }, topics := topics }

/-- LOG data reads exactly the requested offset/size byte slice.
    Distinctive token: Log.logDataSliceVector #125 #112. -/
def logDataSliceVector : TestVector LogDataInput (List Byte) :=
  { id := "log-data-slice"
    input :=
      { memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
        args := mkLogArgs 1 2 [(0x01 : EvmWord)] }
    expected := .value [(0xbb : Byte), 0xcc] }

/-- LOG with zero data size reads no memory bytes. -/
def logDataZeroSizeVector : TestVector LogDataInput (List Byte) :=
  { id := "log-data-zero-size"
    input :=
      { memory := [(0xaa : Byte), 0xbb]
        args := mkLogArgs 1 0 [] }
    expected := .value [] }

theorem runLogData_slice :
    runLogData
      { memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
        args := mkLogArgs 1 2 [(0x01 : EvmWord)] } =
      [(0xbb : Byte), 0xcc] := rfl

theorem runLogData_zeroSize :
    runLogData
      { memory := [(0xaa : Byte), 0xbb]
        args := mkLogArgs 1 0 [] } = [] := rfl

theorem logDataSliceVector_passed :
    checkVector runLogData logDataSliceVector = .passed :=
  checkVector_value_passed runLogData
    "log-data-slice"
    { memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
      args := mkLogArgs 1 2 [(0x01 : EvmWord)] }
    [(0xbb : Byte), 0xcc]
    runLogData_slice

theorem logDataZeroSizeVector_passed :
    checkVector runLogData logDataZeroSizeVector = .passed :=
  checkVector_value_passed runLogData
    "log-data-zero-size"
    { memory := [(0xaa : Byte), 0xbb]
      args := mkLogArgs 1 0 [] }
    []
    runLogData_zeroSize

/-- Vector IDs for LOG data-memory conformance coverage.
    Distinctive token: logDataConformanceVectorIds #125 #112. -/
def logDataConformanceVectorIds : List String :=
  [ logDataSliceVector.id
  , logDataZeroSizeVector.id
  ]

theorem logDataConformanceVectorIds_eq :
    logDataConformanceVectorIds =
      [ "log-data-slice"
      , "log-data-zero-size"
      ] := rfl

theorem logDataConformanceVectorIds_length :
    logDataConformanceVectorIds.length = 2 := rfl

theorem logDataConformanceVectorIds_nodup :
    logDataConformanceVectorIds.Nodup := by
  decide

/-- Compact checked-vector batch for LOG data memory helpers.
    Distinctive token: Log.logDataConformanceVectors #125 #112. -/
def logDataConformanceVectors : List CheckResult :=
  [ checkVector runLogData logDataSliceVector
  , checkVector runLogData logDataZeroSizeVector
  ]

theorem logDataConformanceVectors_passed :
    logDataConformanceVectors = [.passed, .passed] := by
  simp [logDataConformanceVectors, logDataSliceVector_passed,
    logDataZeroSizeVector_passed]

end Log
end Conformance
end EvmAsm.EL
