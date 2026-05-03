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

/-- Pure world state: account existence plus per-account storage slots. Missing
    storage slots read as zero through `getStorage`. -/
structure WorldState where
  accounts : Address → Option Account
  storage : Address → StorageKey → Word256

namespace WorldState

def empty : WorldState :=
  { accounts := fun _ => none
    storage := fun _ _ => 0 }

def getAccount (state : WorldState) (addr : Address) : Option Account :=
  state.accounts addr

def setAccount (state : WorldState) (addr : Address) (account : Account) : WorldState :=
  { state with accounts := fun addr' => if addr' = addr then some account else state.accounts addr' }

def deleteAccount (state : WorldState) (addr : Address) : WorldState :=
  { state with accounts := fun addr' => if addr' = addr then none else state.accounts addr' }

def getStorage (state : WorldState) (addr : Address) (key : StorageKey) : Word256 :=
  state.storage addr key

def setStorage
    (state : WorldState) (addr : Address) (key : StorageKey) (value : Word256) :
    WorldState :=
  { state with storage := fun addr' key' =>
      if addr' = addr then
        if key' = key then value else state.storage addr' key'
      else
        state.storage addr' key' }

@[simp] theorem getAccount_empty (addr : Address) :
    getAccount empty addr = none := rfl

@[simp] theorem getStorage_empty (addr : Address) (key : StorageKey) :
    getStorage empty addr key = 0 := rfl

@[simp] theorem getAccount_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    getAccount (setAccount state addr account) addr = some account := by
  simp [getAccount, setAccount]

theorem getAccount_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    getAccount (setAccount state addr account) other = getAccount state other := by
  simp [getAccount, setAccount, h_ne]

@[simp] theorem getAccount_deleteAccount_same
    (state : WorldState) (addr : Address) :
    getAccount (deleteAccount state addr) addr = none := by
  simp [getAccount, deleteAccount]

theorem getAccount_deleteAccount_ne
    (state : WorldState) {addr other : Address} (h_ne : other ≠ addr) :
    getAccount (deleteAccount state addr) other = getAccount state other := by
  simp [getAccount, deleteAccount, h_ne]

@[simp] theorem getStorage_setStorage_same
    (state : WorldState) (addr : Address) (key : StorageKey) (value : Word256) :
    getStorage (setStorage state addr key value) addr key = value := by
  simp [getStorage, setStorage]

theorem getStorage_setStorage_addr_ne
    (state : WorldState) {addr other : Address} (key key' : StorageKey) (value : Word256)
    (h_ne : other ≠ addr) :
    getStorage (setStorage state addr key value) other key' =
      getStorage state other key' := by
  simp [getStorage, setStorage, h_ne]

theorem getStorage_setStorage_key_ne
    (state : WorldState) (addr : Address) {key other : StorageKey} (value : Word256)
    (h_ne : other ≠ key) :
    getStorage (setStorage state addr key value) addr other =
      getStorage state addr other := by
  simp [getStorage, setStorage, h_ne]

end WorldState

end EvmAsm.EL
