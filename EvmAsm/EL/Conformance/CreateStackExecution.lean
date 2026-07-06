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

def vectorExecutor (request : CreateRequest) : CreateResult :=
  if request.kind = .create ∧ request.initcode = [(0xbb : Byte), 0xcc] ∧
      request.value = 7 ∧ request.gas = 321 ∧ request.salt? = none then
    { status := .deployed
      address? := some deployedAddress
      state := WorldState.empty
      returndata := []
      gasRemaining := 300 }
  else if request.kind = .create2 ∧ request.initcode = [(0xbb : Byte), 0xcc] ∧
      request.value = 11 ∧ request.gas = 654 ∧ request.salt? = some 0x55 then
    { status := .deployed
      address? := some create2DeployedAddress
      state := WorldState.empty
      returndata := []
      gasRemaining := 600 }
  else
    { status := .failed
      address? := none
      state := WorldState.empty
      returndata := []
      gasRemaining := 0 }

def runCreateStackVector? (input : CreateStackInput) : Option CreateStackState :=
  EvmAsm.EL.CreateStackExecutionBridge.runCreateStack?
    input.kind input.creator (readByteAt input.memory) input.gas vectorExecutor
    input.stackState

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

theorem runCreateStackVector?_create :
    runCreateStackVector?
      { kind := .create
        creator := (0xabcd : Address)
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gas := (321 : EvmWord)
        stackState := { stack := [(7 : EvmWord), 1, 2, 99] } } =
      some { stack := [(deployedAddress.zeroExtend 256 : EvmWord), 99] } := by
  rfl

theorem createStackVector_passed :
    checkVector? runCreateStackVector? createStackVector = .passed :=
  checkVector?_some_passed runCreateStackVector?
    "create-stack-execution"
    { kind := .create
      creator := (0xabcd : Address)
      memory := [(0xaa : Byte), 0xbb, 0xcc]
      gas := (321 : EvmWord)
      stackState := { stack := [(7 : EvmWord), 1, 2, 99] } }
    { stack := [(deployedAddress.zeroExtend 256 : EvmWord), 99] }
    runCreateStackVector?_create

theorem runCreateStackVector?_create2 :
    runCreateStackVector?
      { kind := .create2
        creator := (0xabcd : Address)
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gas := (654 : EvmWord)
        stackState := { stack := [(11 : EvmWord), 1, 2, 0x55, 88] } } =
      some { stack := [(create2DeployedAddress.zeroExtend 256 : EvmWord), 88] } := by
  rfl

theorem create2StackConformanceVector_passed :
    checkVector? runCreateStackVector? create2StackConformanceVector = .passed :=
  checkVector?_some_passed runCreateStackVector?
    "create2-stack-execution"
    { kind := .create2
      creator := (0xabcd : Address)
      memory := [(0xaa : Byte), 0xbb, 0xcc]
      gas := (654 : EvmWord)
      stackState := { stack := [(11 : EvmWord), 1, 2, 0x55, 88] } }
    { stack := [(create2DeployedAddress.zeroExtend 256 : EvmWord), 88] }
    runCreateStackVector?_create2

/-- Compact checked-vector batch for CREATE stack execution.
    Distinctive token:
    CreateStackExecutionConformance.createStackConformanceVectors #115 #125. -/
def createStackConformanceVectors : List CheckResult :=
  checkBatch? runCreateStackVector? createStackConformanceTestVectors

theorem createStackConformanceVectors_passed :
    createStackConformanceVectors = [.passed, .passed] := by
  simp [createStackConformanceVectors, createStackConformanceTestVectors,
    createStackVector_passed, create2StackConformanceVector_passed]

end CreateStackExecution
end Conformance
end EvmAsm.EL
