/-
  EvmAsm.EL.Conformance.KeccakStackExecution

  Lean-side conformance vector for the KECCAK256 stack execution bridge
  (GH #111 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.KeccakStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace KeccakStackExecution

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev AcceleratorInput := EvmAsm.EL.KeccakInputBridge.AcceleratorInput
abbrev AcceleratorOutput := EvmAsm.EL.KeccakResultBridge.AcceleratorOutput

structure KeccakStackInput where
  memory : List Byte
  stack : List EvmWord
  deriving Repr

def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0

def zeroHash : EvmAsm.EL.KeccakResultBridge.HashBytes :=
  fun _ => 0

def vectorAccelerator (input : AcceleratorInput) : AcceleratorOutput :=
  if input.bytes = [(0xbb : Byte), 0xcc] then
    { hash := zeroHash }
  else
    { hash := fun _ => 0xff }

def runKeccakStack? (input : KeccakStackInput) : Option (List EvmWord) :=
  EvmAsm.EL.KeccakStackExecutionBridge.runKeccakStack?
    vectorAccelerator (readByteAt input.memory) input.stack

def keccakStackVector : TestVector KeccakStackInput (List EvmWord) :=
  { id := "keccak-stack-vector"
    input :=
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord), 2, 99] }
    expected := .value [(0 : EvmWord), 99] }

/-- KECCAK256 stack execution requires both offset and size operands.
    Distinctive token: keccakStackUnderflowConformanceVector #111 #125. -/
def keccakStackUnderflowConformanceVector :
    TestVector KeccakStackInput (List EvmWord) :=
  { id := "keccak-stack-underflow"
    input :=
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord)] }
    expected := .error "stack-underflow" }

/-- KECCAK stack conformance inputs as reusable test vectors.
    Distinctive token:
    KeccakStackExecutionConformance.keccakStackConformanceTestVectors #111 #125. -/
def keccakStackConformanceTestVectors :
    List (TestVector KeccakStackInput (List EvmWord)) :=
  [keccakStackVector, keccakStackUnderflowConformanceVector]

def keccakStackConformanceVectorIds : List String :=
  keccakStackConformanceTestVectors.map TestVector.id

theorem keccakStackConformanceTestVectors_length :
    keccakStackConformanceTestVectors.length = 2 := rfl

theorem keccakStackConformanceVectorIds_eq :
    keccakStackConformanceVectorIds =
      ["keccak-stack-vector", "keccak-stack-underflow"] := rfl

theorem keccakStackConformanceVectorIds_length :
    keccakStackConformanceVectorIds.length = 2 := rfl

theorem keccakStackConformanceVectorIds_nodup :
    keccakStackConformanceVectorIds.Nodup := by
  decide

theorem runKeccakStack?_vector :
    runKeccakStack?
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord), 2, 99] } =
      some [(0 : EvmWord), 99] := by
  rfl

theorem runKeccakStack?_underflow :
    runKeccakStack?
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord)] } =
      none := rfl

theorem keccakStackVector_passed :
    checkVector? runKeccakStack? keccakStackVector = .passed :=
  checkVector?_some_passed runKeccakStack?
    "keccak-stack-vector"
    { memory := [(0xaa : Byte), 0xbb, 0xcc]
      stack := [(1 : EvmWord), 2, 99] }
    [(0 : EvmWord), 99]
    runKeccakStack?_vector

theorem keccakStackUnderflowConformanceVector_errored :
    checkVector? runKeccakStack? keccakStackUnderflowConformanceVector =
      .errored "keccak-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runKeccakStack?
    "keccak-stack-underflow"
    "stack-underflow"
    { memory := [(0xaa : Byte), 0xbb, 0xcc]
      stack := [(1 : EvmWord)] }
    runKeccakStack?_underflow

/-- Compact checked-vector batch for KECCAK stack execution.
    Distinctive token:
    KeccakStackExecutionConformance.keccakStackConformanceVectors #111 #125. -/
def keccakStackConformanceVectors : List CheckResult :=
  checkBatch? runKeccakStack? keccakStackConformanceTestVectors

theorem keccakStackConformanceVectors_passed :
    keccakStackConformanceVectors =
      [.passed, .errored "keccak-stack-underflow" "stack-underflow"] := by
  simp [keccakStackConformanceVectors, keccakStackConformanceTestVectors,
    keccakStackVector_passed, keccakStackUnderflowConformanceVector_errored]

end KeccakStackExecution
end Conformance
end EvmAsm.EL
