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

end TerminatingStackExecution
end Conformance
end EvmAsm.EL
