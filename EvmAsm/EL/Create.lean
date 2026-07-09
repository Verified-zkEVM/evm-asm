/-
  EvmAsm.EL.Create

  Pure contract-creation request surface for GH #115.
-/

import EvmAsm.EL.WorldState

namespace EvmAsm.EL

/-- CREATE-family opcode variant. -/
inductive CreateKind where
  | create
  | create2
  deriving DecidableEq, Repr

namespace CreateKind

def usesSalt : CreateKind → Bool
  | create => false
  | create2 => true

theorem usesSalt_create : usesSalt create = false := rfl
theorem usesSalt_create2 : usesSalt create2 = true := rfl

end CreateKind

/-- Pure input request for a CREATE or CREATE2 operation. -/
structure CreateRequest where
  kind : CreateKind
  creator : Address
  value : Word256
  initcode : List Byte
  gas : Nat
  salt? : Option Word256
  deriving Repr

namespace CreateRequest

def forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    CreateRequest :=
  { kind := .create
    creator := creator
    value := value
    initcode := initcode
    gas := gas
    salt? := none }

def forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) : CreateRequest :=
  { kind := .create2
    creator := creator
    value := value
    initcode := initcode
    gas := gas
    salt? := some salt }

def isCreate2 (request : CreateRequest) : Prop :=
  request.kind = .create2

def hasSalt (request : CreateRequest) : Prop :=
  request.salt?.isSome

theorem kind_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    (forCreate creator value initcode gas).kind = .create := rfl

theorem kind_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).kind = .create2 := rfl

theorem salt?_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    (forCreate creator value initcode gas).salt? = none := rfl

theorem salt?_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).salt? = some salt := rfl

theorem hasSalt_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).hasSalt := by
  unfold hasSalt
  rfl

theorem not_hasSalt_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    ¬ (forCreate creator value initcode gas).hasSalt := by
  simp [hasSalt, forCreate]

theorem isCreate2_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).isCreate2 := rfl

theorem not_isCreate2_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    ¬ (forCreate creator value initcode gas).isCreate2 := by
  simp [isCreate2, forCreate]

end CreateRequest

/-- Coarse result status for CREATE and CREATE2. -/
inductive CreateStatus where
  | deployed
  | reverted
  | failed
  deriving DecidableEq, Repr

namespace CreateResult

end CreateResult

end EvmAsm.EL
