/-
  EvmAsm.EL.Conformance.TerminatingStackExecution

  Lean-side conformance vector for the terminating-opcode stack execution bridge
  (GH #113 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.TerminatingStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace TerminatingStackExecution

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev TerminatingKind := EvmAsm.Evm64.TerminatingArgs.Kind
abbrev TerminatingStackState :=
  EvmAsm.EL.TerminatingStackExecutionBridge.TerminatingStackState

structure TerminatingVisibleResult where
  status : CallStatus
  output : List Byte
  gasRemaining : Nat
  stack : List EvmWord
  deriving DecidableEq, Repr

structure TerminatingStackInput where
  kind : TerminatingKind
  memory : List Byte
  gasRemaining : Nat
  stackState : TerminatingStackState

def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0

def visibleFromResult
    (out : EvmAsm.EL.TerminatingStackExecutionBridge.TerminatingStackResult) :
    TerminatingVisibleResult :=
  { status := out.result.status
    output := out.result.output
    gasRemaining := out.result.gasRemaining
    stack := out.stack }

def runTerminatingStackVisible? (input : TerminatingStackInput) :
    Option TerminatingVisibleResult :=
  (EvmAsm.EL.TerminatingStackExecutionBridge.runTerminatingStack?
    input.kind WorldState.empty (readByteAt input.memory)
    input.gasRemaining input.stackState).map visibleFromResult

def terminatingReturnVector :
    TestVector TerminatingStackInput TerminatingVisibleResult :=
  { id := "terminating-stack-return"
    input :=
      { kind := .return_
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gasRemaining := 123
        stackState := { stack := [(1 : EvmWord), 2, 99] } }
    expected :=
      .value
        { status := .success
          output := [(0xbb : Byte), 0xcc]
          gasRemaining := 123
          stack := [(99 : EvmWord)] } }

/-- REVERT threads memory data through while exposing reverted status.
    Distinctive token: terminatingRevertStackConformanceVector #113 #125. -/
def terminatingRevertStackConformanceVector :
    TestVector TerminatingStackInput TerminatingVisibleResult :=
  { id := "terminating-stack-revert"
    input :=
      { kind := .revert
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gasRemaining := 45
        stackState := { stack := [(1 : EvmWord), 2, 77] } }
    expected :=
      .value
        { status := .revert
          output := [(0xbb : Byte), 0xcc]
          gasRemaining := 45
          stack := [(77 : EvmWord)] } }

/-- Terminating stack conformance inputs as reusable test vectors.
    Distinctive token:
    TerminatingStackExecutionConformance.terminatingStackConformanceTestVectors #113 #125. -/
def terminatingStackConformanceTestVectors :
    List (TestVector TerminatingStackInput TerminatingVisibleResult) :=
  [terminatingReturnVector, terminatingRevertStackConformanceVector]

def terminatingStackConformanceVectorIds : List String :=
  terminatingStackConformanceTestVectors.map TestVector.id

theorem terminatingStackConformanceTestVectors_length :
    terminatingStackConformanceTestVectors.length = 2 := rfl

theorem terminatingStackConformanceVectorIds_eq :
    terminatingStackConformanceVectorIds =
      ["terminating-stack-return", "terminating-stack-revert"] := rfl

theorem terminatingStackConformanceVectorIds_length :
    terminatingStackConformanceVectorIds.length = 2 := rfl

theorem terminatingStackConformanceVectorIds_nodup :
    terminatingStackConformanceVectorIds.Nodup := by
  decide

theorem runTerminatingStackVisible?_return :
    runTerminatingStackVisible?
      { kind := .return_
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gasRemaining := 123
        stackState := { stack := [(1 : EvmWord), 2, 99] } } =
      some
        { status := .success
          output := [(0xbb : Byte), 0xcc]
          gasRemaining := 123
          stack := [(99 : EvmWord)] } := by
  rfl

theorem terminatingReturnVector_passed :
    checkVector? runTerminatingStackVisible? terminatingReturnVector = .passed :=
  checkVector?_some_passed runTerminatingStackVisible?
    "terminating-stack-return"
    { kind := .return_
      memory := [(0xaa : Byte), 0xbb, 0xcc]
      gasRemaining := 123
      stackState := { stack := [(1 : EvmWord), 2, 99] } }
    { status := .success
      output := [(0xbb : Byte), 0xcc]
      gasRemaining := 123
      stack := [(99 : EvmWord)] }
    runTerminatingStackVisible?_return

theorem runTerminatingStackVisible?_revert :
    runTerminatingStackVisible?
      { kind := .revert
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gasRemaining := 45
        stackState := { stack := [(1 : EvmWord), 2, 77] } } =
      some
        { status := .revert
          output := [(0xbb : Byte), 0xcc]
          gasRemaining := 45
          stack := [(77 : EvmWord)] } := by
  rfl

theorem terminatingRevertStackConformanceVector_passed :
    checkVector? runTerminatingStackVisible? terminatingRevertStackConformanceVector =
      .passed :=
  checkVector?_some_passed runTerminatingStackVisible?
    "terminating-stack-revert"
    { kind := .revert
      memory := [(0xaa : Byte), 0xbb, 0xcc]
      gasRemaining := 45
      stackState := { stack := [(1 : EvmWord), 2, 77] } }
    { status := .revert
      output := [(0xbb : Byte), 0xcc]
      gasRemaining := 45
      stack := [(77 : EvmWord)] }
    runTerminatingStackVisible?_revert

/-- Compact checked-vector batch for terminating stack execution.
    Distinctive token:
    TerminatingStackExecutionConformance.terminatingStackConformanceVectors #113 #125. -/
def terminatingStackConformanceVectors : List CheckResult :=
  checkBatch? runTerminatingStackVisible? terminatingStackConformanceTestVectors

theorem terminatingStackConformanceVectors_passed :
    terminatingStackConformanceVectors = [.passed, .passed] := by
  simp [terminatingStackConformanceVectors, terminatingStackConformanceTestVectors,
    terminatingReturnVector_passed, terminatingRevertStackConformanceVector_passed]

end TerminatingStackExecution
end Conformance
end EvmAsm.EL
