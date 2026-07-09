/-
  EvmAsm.EL.Conformance.CreateStackExecution

  Lean-side conformance vector for the CREATE stack execution bridge
  (GH #115 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.CreateStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace CreateStackExecution

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev CreateKind := EvmAsm.Evm64.CreateArgs.Kind
abbrev CreateStackState :=
  EvmAsm.EL.CreateStackExecutionBridge.CreateStackState

deriving instance DecidableEq for
  EvmAsm.EL.CreateStackExecutionBridge.CreateStackState

structure CreateStackInput where
  kind : CreateKind
  creator : Address
  memory : List Byte
  gas : EvmWord
  stackState : CreateStackState

def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0

def deployedAddress : Address := 0x1234
def create2DeployedAddress : Address := 0x5678

def createStackVector : TestVector CreateStackInput CreateStackState :=
  { id := "create-stack-execution"
    input :=
      { kind := .create
        creator := 0xabcd
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gas := 321
        stackState := { stack := [(7 : EvmWord), 1, 2, 99] } }
    expected :=
      .value { stack := [(deployedAddress.zeroExtend 256 : EvmWord), 99] } }

/-- CREATE2 consumes its salt operand and pushes the deployed address.
    Distinctive token: create2StackConformanceVector #115 #125. -/
def create2StackConformanceVector : TestVector CreateStackInput CreateStackState :=
  { id := "create2-stack-execution"
    input :=
      { kind := .create2
        creator := 0xabcd
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gas := 654
        stackState := { stack := [(11 : EvmWord), 1, 2, 0x55, 88] } }
    expected :=
      .value { stack := [(create2DeployedAddress.zeroExtend 256 : EvmWord), 88] } }

/-- CREATE stack conformance inputs as reusable test vectors.
    Distinctive token:
    CreateStackExecutionConformance.createStackConformanceTestVectors #115 #125. -/
def createStackConformanceTestVectors :
    List (TestVector CreateStackInput CreateStackState) :=
  [createStackVector, create2StackConformanceVector]

def createStackConformanceVectorIds : List String :=
  createStackConformanceTestVectors.map TestVector.id

theorem createStackConformanceTestVectors_length :
    createStackConformanceTestVectors.length = 2 := rfl

theorem createStackConformanceVectorIds_eq :
    createStackConformanceVectorIds =
      ["create-stack-execution", "create2-stack-execution"] := rfl

theorem createStackConformanceVectorIds_length :
    createStackConformanceVectorIds.length = 2 := rfl

theorem createStackConformanceVectorIds_nodup :
    createStackConformanceVectorIds.Nodup := by
  decide

end CreateStackExecution
end Conformance
end EvmAsm.EL
