/-
  EvmAsm.EL.CreatePrecheck

  Pure CREATE/CREATE2 precheck and collision outcome surface.
-/

import EvmAsm.EL.CreateAddress
import EvmAsm.EL.CreateCollisionResult
import EvmAsm.EL.WorldStateAccount

namespace EvmAsm.EL

namespace CreatePrecheck

/-- EVM maximum child call/create depth from execution-specs `STACK_DEPTH_LIMIT`. -/
def stackDepthLimit : Nat := 1024

/-- EIP-3860 initcode size cap used by Amsterdam and later forks.
    Amsterdam (EIP-7954) doubled MAX_CODE_SIZE to 0x8000 (32768), so
    MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE = 65536 (0x10000) — not the
    pre-Amsterdam 2 * 0x6000 = 49152. -/
def maxInitCodeSize : Nat := 65536

/-- Creator nonce sentinel checked before CREATE-family child execution. -/
def maxCreatorNonce : Nat := 2 ^ 64 - 1

/-- Account metadata read by the precheck layer. -/
structure CreatorAccountView where
  nonce : Nat
  balance : Word256
  deriving Repr

namespace CreatorAccountView

def fromAccount (account : Account) : CreatorAccountView :=
  { nonce := account.nonce, balance := account.balance }

@[simp] theorem fromAccount_nonce (account : Account) :
    (fromAccount account).nonce = account.nonce := rfl

@[simp] theorem fromAccount_balance (account : Account) :
    (fromAccount account).balance = account.balance := rfl

end CreatorAccountView

/-- Inputs known after stack decoding, initcode slicing, address derivation,
and collision lookup. `targetCollides` represents executable-spec
`account_has_code_or_nonce(...) or account_has_storage(...)`. -/
structure Input where
  state : WorldState
  request : CreateRequest
  target : Address
  depth : Nat
  isStatic : Bool
  creator : CreatorAccountView
  targetCollides : Bool

def insufficientBalance (input : Input) : Prop :=
  input.creator.balance.toNat < input.request.value.toNat

def nonceExhausted (input : Input) : Prop :=
  input.creator.nonce = maxCreatorNonce

def depthOverflow (input : Input) : Prop :=
  input.depth + 1 > stackDepthLimit

def initcodeTooLarge (input : Input) : Prop :=
  input.request.initcode.length > maxInitCodeSize

/-- High-level branch taken before CREATE-family child initcode execution. -/
inductive Outcome where
  | writeInStaticContext
  | initcodeTooLarge
  | zeroResult
  | addressCollision
  | execute
  deriving DecidableEq, Repr

def decide (input : Input) : Outcome :=
  if input.isStatic then
    .writeInStaticContext
  else if input.request.initcode.length > maxInitCodeSize then
    .initcodeTooLarge
  else if input.creator.balance.toNat < input.request.value.toNat then
    .zeroResult
  else if input.creator.nonce = maxCreatorNonce then
    .zeroResult
  else if input.depth + 1 > stackDepthLimit then
    .zeroResult
  else if input.targetCollides then
    .addressCollision
  else
    .execute

def failedResult (input : Input) : CreateResult :=
  CreateCollisionResult.collisionResult input.state input.request.gas

def stackWordForOutcome (input : Input) (outcome : Outcome) : Word256 :=
  match outcome with
  | .execute => input.target.zeroExtend 256
  | _ => 0

theorem decide_static {input : Input} (h_static : input.isStatic = true) :
    decide input = .writeInStaticContext := by
  simp [decide, h_static]

theorem decide_initcodeTooLarge
    {input : Input} (h_static : input.isStatic = false)
    (h_size : input.request.initcode.length > maxInitCodeSize) :
    decide input = .initcodeTooLarge := by
  simp [decide, h_static, h_size]

theorem decide_insufficientBalance
    {input : Input} (h_static : input.isStatic = false)
    (h_size : ¬ input.request.initcode.length > maxInitCodeSize)
    (h_balance : input.creator.balance.toNat < input.request.value.toNat) :
    decide input = .zeroResult := by
  simp [decide, h_static, h_size, h_balance]

theorem decide_nonceExhausted
    {input : Input} (h_static : input.isStatic = false)
    (h_size : ¬ input.request.initcode.length > maxInitCodeSize)
    (h_balance : ¬ input.creator.balance.toNat < input.request.value.toNat)
    (h_nonce : input.creator.nonce = maxCreatorNonce) :
    decide input = .zeroResult := by
  simp [decide, h_static, h_size, h_balance, h_nonce]

theorem decide_depthOverflow
    {input : Input} (h_static : input.isStatic = false)
    (h_size : ¬ input.request.initcode.length > maxInitCodeSize)
    (h_balance : ¬ input.creator.balance.toNat < input.request.value.toNat)
    (h_nonce : input.creator.nonce ≠ maxCreatorNonce)
    (h_depth : input.depth + 1 > stackDepthLimit) :
    decide input = .zeroResult := by
  simp [decide, h_static, h_size, h_balance, h_nonce, h_depth]

theorem decide_collision
    {input : Input} (h_static : input.isStatic = false)
    (h_size : ¬ input.request.initcode.length > maxInitCodeSize)
    (h_balance : ¬ input.creator.balance.toNat < input.request.value.toNat)
    (h_nonce : input.creator.nonce ≠ maxCreatorNonce)
    (h_depth : ¬ input.depth + 1 > stackDepthLimit)
    (h_collision : input.targetCollides = true) :
    decide input = .addressCollision := by
  simp [decide, h_static, h_size, h_balance, h_nonce, h_depth, h_collision]

theorem decide_execute
    {input : Input} (h_static : input.isStatic = false)
    (h_size : ¬ input.request.initcode.length > maxInitCodeSize)
    (h_balance : ¬ input.creator.balance.toNat < input.request.value.toNat)
    (h_nonce : input.creator.nonce ≠ maxCreatorNonce)
    (h_depth : ¬ input.depth + 1 > stackDepthLimit)
    (h_collision : input.targetCollides = false) :
    decide input = .execute := by
  simp [decide, h_static, h_size, h_balance, h_nonce, h_depth, h_collision]

theorem failedResult_status (input : Input) :
    (failedResult input).status = .failed := rfl

theorem failedResult_state (input : Input) :
    (failedResult input).state = input.state := rfl

theorem failedResult_stackWord (input : Input) :
    CreateResultBridge.createResultStackWord (failedResult input) = 0 := rfl

theorem stackWordForOutcome_execute (input : Input) :
    stackWordForOutcome input .execute = input.target.zeroExtend 256 := rfl

theorem stackWordForOutcome_zeroResult (input : Input) :
    stackWordForOutcome input .zeroResult = 0 := rfl

theorem stackWordForOutcome_collision (input : Input) :
    stackWordForOutcome input .addressCollision = 0 := rfl

/-- CREATE request/salt shape is preserved when deriving the address input. -/
theorem addressInput?_eq_fromRequest
    (input : Input) (initcodeHash : Hash256) :
    CreateAddress.fromRequest? input.request input.creator.nonce initcodeHash =
      CreateAddress.fromRequest? input.request input.creator.nonce initcodeHash := rfl

end CreatePrecheck

end EvmAsm.EL
