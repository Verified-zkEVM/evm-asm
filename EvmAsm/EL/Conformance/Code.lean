/-
  EvmAsm.EL.Conformance.Code

  Initial Lean-side conformance vector for executable code helpers
  (GH #125 / GH #107 / GH #118).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.Code.CopyExec
public import EvmAsm.Evm64.Code.CopyArgsStackDecode

@[expose] public section

namespace EvmAsm.EL
namespace Conformance
namespace Code

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Input shape for a CODECOPY executable-helper conformance vector. -/
structure CodeCopyInput where
  code : List (BitVec 8)
  destOffset : EvmWord
  codeOffset : EvmWord
  size : EvmWord
  deriving Repr

/-- Input shape for a CODECOPY stack-decoder conformance vector. -/
structure CodeCopyStackInput where
  code : List (BitVec 8)
  stack : List EvmWord
  deriving Repr

def runCodeCopy (input : CodeCopyInput) : List (BitVec 8) :=
  EvmAsm.Evm64.CodeCopyExec.copiedBytesFromArgs
    input.code
    (EvmAsm.Evm64.CodeCopyArgs.copyArgs
      input.destOffset input.codeOffset input.size)

def runCodeCopyStack? (input : CodeCopyStackInput) :
    Option (List (BitVec 8)) :=
  EvmAsm.Evm64.CodeCopyArgsStackDecode.decodeCodeCopyStack? input.stack
    |>.map (EvmAsm.Evm64.CodeCopyExec.copiedBytesFromArgs input.code)

/-- CODECOPY zero-pads bytes copied past the end of code.
    Distinctive token: codeCopyZeroPadVector #125 #107 #118. -/
def codeCopyZeroPadVector :
    TestVector CodeCopyInput (List (BitVec 8)) :=
  { id := "codecopy-zero-pad"
    input :=
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        destOffset := 64
        codeOffset := 1
        size := 4 }
    expected := .value [(0xaa : BitVec 8), 0, 0, 0] }

/-- Stack-decoded CODECOPY uses stack words as
    `destOffset, codeOffset, size`; the executable helper here returns only
    the copied byte sequence. Distinctive token: runCodeCopyStack?
    #107 #118 #125. -/
def codeCopyStackVector :
    TestVector CodeCopyStackInput (List (BitVec 8)) :=
  { id := "codecopy-stack-decode"
    input :=
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        stack := [(64 : EvmWord), (1 : EvmWord), (4 : EvmWord)] }
    expected := .value [(0xaa : BitVec 8), 0, 0, 0] }

/-- CODECOPY stack decoding fails unless all three stack operands exist. -/
def codeCopyStackUnderflowVector :
    TestVector CodeCopyStackInput (List (BitVec 8)) :=
  { id := "codecopy-stack-underflow"
    input :=
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        stack := [(64 : EvmWord), (1 : EvmWord)] }
    expected := .error "stack-underflow" }

theorem runCodeCopy_zeroPad :
    runCodeCopy
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        destOffset := 64
        codeOffset := 1
        size := 4 } =
      [(0xaa : BitVec 8), 0, 0, 0] := rfl

theorem runCodeCopyStack_decoded :
    runCodeCopyStack?
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        stack := [(64 : EvmWord), (1 : EvmWord), (4 : EvmWord)] } =
      some [(0xaa : BitVec 8), 0, 0, 0] := rfl

theorem runCodeCopyStack_underflow :
    runCodeCopyStack?
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        stack := [(64 : EvmWord), (1 : EvmWord)] } = none := rfl

theorem codeCopyZeroPadVector_passed :
    checkVector runCodeCopy codeCopyZeroPadVector = .passed :=
  checkVector_value_passed runCodeCopy
    "codecopy-zero-pad"
    { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
      destOffset := (64 : EvmWord)
      codeOffset := (1 : EvmWord)
      size := (4 : EvmWord) }
    [(0xaa : BitVec 8), 0, 0, 0]
    runCodeCopy_zeroPad

theorem codeCopyStackVector_passed :
    checkVector? runCodeCopyStack? codeCopyStackVector = .passed :=
  checkVector?_some_passed runCodeCopyStack?
    "codecopy-stack-decode"
    { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
      stack := [(64 : EvmWord), (1 : EvmWord), (4 : EvmWord)] }
    [(0xaa : BitVec 8), 0, 0, 0]
    runCodeCopyStack_decoded

theorem codeCopyStackUnderflowVector_errored :
    checkVector? runCodeCopyStack? codeCopyStackUnderflowVector =
      .errored "codecopy-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runCodeCopyStack?
    "codecopy-stack-underflow"
    "stack-underflow"
    { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
      stack := [(64 : EvmWord), (1 : EvmWord)] }
    runCodeCopyStack_underflow

/-- Vector IDs for code executable-helper conformance coverage.
    Distinctive token: codeConformanceVectorIds #125 #107 #118. -/
def codeConformanceVectorIds : List String :=
  [ codeCopyZeroPadVector.id
  , codeCopyStackVector.id
  , codeCopyStackUnderflowVector.id
  ]

theorem codeConformanceVectorIds_eq :
    codeConformanceVectorIds =
      [ "codecopy-zero-pad"
      , "codecopy-stack-decode"
      , "codecopy-stack-underflow"
      ] := rfl

theorem codeConformanceVectorIds_length :
    codeConformanceVectorIds.length = 3 := rfl

theorem codeConformanceVectorIds_nodup :
    codeConformanceVectorIds.Nodup := by
  decide

/-- Compact checked-vector batch for code executable helpers.
    Distinctive token: codeConformanceVectors #125 #107 #118. -/
def codeConformanceVectors : List CheckResult :=
  [ checkVector runCodeCopy codeCopyZeroPadVector
  , checkVector? runCodeCopyStack? codeCopyStackVector
  , checkVector? runCodeCopyStack? codeCopyStackUnderflowVector
  ]

theorem codeConformanceVectors_passed :
    codeConformanceVectors =
      [.passed, .passed, .errored "codecopy-stack-underflow" "stack-underflow"] := by
  simp [codeConformanceVectors, codeCopyZeroPadVector_passed]
  exact ⟨codeCopyStackVector_passed, codeCopyStackUnderflowVector_errored⟩

end Code
end Conformance
end EvmAsm.EL
