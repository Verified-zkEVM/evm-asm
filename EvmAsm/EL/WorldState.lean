/-
  EvmAsm.EL.WorldState

  Pure Ethereum world-state model (GH #123 slice 1). This module deliberately
  has no RISC-V dependency; later Evm64 storage/syscall slices can bridge this
  model to concrete ECALL interfaces and separation-logic assertions.
-/

namespace EvmAsm.EL

abbrev Byte := BitVec 8
abbrev Address := BitVec 160
abbrev Word256 := BitVec 256
abbrev Hash256 := BitVec 256
abbrev StorageKey := Word256

/-- Ethereum account data relevant to the execution layer. Code bytes are kept
    with the account so CREATE/CALL-family slices can relate code hashes to the
    executable code region later. -/
structure Account where
  nonce : Nat
  balance : Word256
  storageRoot : Hash256
  codeHash : Hash256
  code : List Byte
  deriving Repr

end EvmAsm.EL
