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

/-- High-level branch taken before CREATE-family child initcode execution. -/
inductive Outcome where
  | writeInStaticContext
  | initcodeTooLarge
  | zeroResult
  | addressCollision
  | execute
  deriving DecidableEq, Repr

end CreatePrecheck

end EvmAsm.EL
