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

/-- Read an account's code bytes when the account exists. -/
def accountCode? (state : WorldState) (addr : Address) : Option (List Byte) :=
  (getAccount state addr).map (fun account => account.code)

/-- Read an account's code hash when the account exists. -/
def accountCodeHash? (state : WorldState) (addr : Address) : Option Hash256 :=
  (getAccount state addr).map (fun account => account.codeHash)

/-- Update an existing account's code bytes and code hash. Missing accounts are unchanged. -/
def setAccountCode
    (state : WorldState) (addr : Address) (codeHash : Hash256) (code : List Byte) :
    WorldState :=
  match getAccount state addr with
  | none => state
  | some account => setAccount state addr { account with codeHash := codeHash, code := code }

def accountBalance? (state : WorldState) (addr : Address) : Option Word256 :=
  (getAccount state addr).map (fun account => account.balance)

def setAccountBalance (state : WorldState) (addr : Address) (balance : Word256) :
    WorldState :=
  match getAccount state addr with
  | some account => setAccount state addr { account with balance := balance }
  | none => state

def accountNonce? (state : WorldState) (addr : Address) : Option Nat :=
  (getAccount state addr).map (fun account => account.nonce)

def setAccountNonce (state : WorldState) (addr : Address) (nonce : Nat) :
    WorldState :=
  match getAccount state addr with
  | some account => setAccount state addr { account with nonce := nonce }
  | none => state

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

@[simp] theorem accountCode?_empty (addr : Address) :
    accountCode? empty addr = none := rfl

@[simp] theorem accountCodeHash?_empty (addr : Address) :
    accountCodeHash? empty addr = none := rfl

@[simp] theorem accountCode?_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    accountCode? (setAccount state addr account) addr = some account.code := by
  simp [accountCode?]

@[simp] theorem accountCodeHash?_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    accountCodeHash? (setAccount state addr account) addr = some account.codeHash := by
  simp [accountCodeHash?]

theorem accountCode?_eq_some_iff
    {state : WorldState} {addr : Address} {code : List Byte} :
    accountCode? state addr = some code ↔
      ∃ account, getAccount state addr = some account ∧ code = account.code := by
  unfold accountCode?
  cases h_account : getAccount state addr with
  | none =>
      simp
  | some account =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro h_code
        exact ⟨account, rfl, h_code.symm⟩
      · rintro ⟨account', h_account', h_code⟩
        subst h_account'
        exact h_code.symm

theorem accountCode?_eq_none_iff {state : WorldState} {addr : Address} :
    accountCode? state addr = none ↔ getAccount state addr = none := by
  unfold accountCode?
  cases getAccount state addr <;> simp

theorem accountCodeHash?_eq_some_iff
    {state : WorldState} {addr : Address} {codeHash : Hash256} :
    accountCodeHash? state addr = some codeHash ↔
      ∃ account, getAccount state addr = some account ∧ codeHash = account.codeHash := by
  unfold accountCodeHash?
  cases h_account : getAccount state addr with
  | none =>
      simp
  | some account =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro h_codeHash
        exact ⟨account, rfl, h_codeHash.symm⟩
      · rintro ⟨account', h_account', h_codeHash⟩
        subst h_account'
        exact h_codeHash.symm

theorem accountCodeHash?_eq_none_iff {state : WorldState} {addr : Address} :
    accountCodeHash? state addr = none ↔ getAccount state addr = none := by
  unfold accountCodeHash?
  cases getAccount state addr <;> simp

theorem accountCode?_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    accountCode? (setAccount state addr account) other = accountCode? state other := by
  simp [accountCode?, getAccount_setAccount_ne, h_ne]

theorem accountCodeHash?_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    accountCodeHash? (setAccount state addr account) other = accountCodeHash? state other := by
  simp [accountCodeHash?, getAccount_setAccount_ne, h_ne]

theorem setAccountCode_of_missing
    {state : WorldState} {addr : Address} (codeHash : Hash256) (code : List Byte)
    (h_missing : getAccount state addr = none) :
    setAccountCode state addr codeHash code = state := by
  simp [setAccountCode, h_missing]

theorem getAccount_setAccountCode_same
    {state : WorldState} {addr : Address} {account : Account}
    (codeHash : Hash256) (code : List Byte)
    (h_account : getAccount state addr = some account) :
    getAccount (setAccountCode state addr codeHash code) addr =
      some { account with codeHash := codeHash, code := code } := by
  simp [setAccountCode, h_account]

theorem accountCode?_setAccountCode_same
    {state : WorldState} {addr : Address} {account : Account}
    (codeHash : Hash256) (code : List Byte)
    (h_account : getAccount state addr = some account) :
    accountCode? (setAccountCode state addr codeHash code) addr = some code := by
  simp [accountCode?, getAccount_setAccountCode_same codeHash code h_account]

theorem accountCodeHash?_setAccountCode_same
    {state : WorldState} {addr : Address} {account : Account}
    (codeHash : Hash256) (code : List Byte)
    (h_account : getAccount state addr = some account) :
    accountCodeHash? (setAccountCode state addr codeHash code) addr = some codeHash := by
  simp [accountCodeHash?, getAccount_setAccountCode_same codeHash code h_account]

theorem getAccount_setAccountCode_ne
    (state : WorldState) {addr other : Address} (codeHash : Hash256) (code : List Byte)
    (h_ne : other ≠ addr) :
    getAccount (setAccountCode state addr codeHash code) other = getAccount state other := by
  unfold setAccountCode
  cases h_account : getAccount state addr <;>
    simp [getAccount_setAccount_ne, h_ne]

theorem accountCode?_setAccountCode_ne
    (state : WorldState) {addr other : Address} (codeHash : Hash256) (code : List Byte)
    (h_ne : other ≠ addr) :
    accountCode? (setAccountCode state addr codeHash code) other =
      accountCode? state other := by
  simp [accountCode?, getAccount_setAccountCode_ne state codeHash code h_ne]

theorem accountCodeHash?_setAccountCode_ne
    (state : WorldState) {addr other : Address} (codeHash : Hash256) (code : List Byte)
    (h_ne : other ≠ addr) :
    accountCodeHash? (setAccountCode state addr codeHash code) other =
      accountCodeHash? state other := by
  simp [accountCodeHash?, getAccount_setAccountCode_ne state codeHash code h_ne]

@[simp] theorem accountBalance?_empty (addr : Address) :
    accountBalance? empty addr = none := rfl

@[simp] theorem accountBalance?_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    accountBalance? (setAccount state addr account) addr = some account.balance := by
  simp [accountBalance?]

theorem accountBalance?_eq_some_iff
    {state : WorldState} {addr : Address} {balance : Word256} :
    accountBalance? state addr = some balance ↔
      ∃ account, getAccount state addr = some account ∧ balance = account.balance := by
  unfold accountBalance?
  cases h_account : getAccount state addr with
  | none =>
      simp
  | some account =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro h_balance
        exact ⟨account, rfl, h_balance.symm⟩
      · rintro ⟨account', h_account', h_balance⟩
        subst h_account'
        exact h_balance.symm

theorem accountBalance?_eq_none_iff {state : WorldState} {addr : Address} :
    accountBalance? state addr = none ↔ getAccount state addr = none := by
  unfold accountBalance?
  cases getAccount state addr <;> simp

theorem accountBalance?_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    accountBalance? (setAccount state addr account) other = accountBalance? state other := by
  simp [accountBalance?, getAccount_setAccount_ne state account h_ne]

theorem getAccount_setAccountBalance_same
    {state : WorldState} {addr : Address} {account : Account} {balance : Word256}
    (h_account : getAccount state addr = some account) :
    getAccount (setAccountBalance state addr balance) addr =
      some { account with balance := balance } := by
  simp [setAccountBalance, h_account]

theorem accountBalance?_setAccountBalance_same
    {state : WorldState} {addr : Address} {account : Account} {balance : Word256}
    (h_account : getAccount state addr = some account) :
    accountBalance? (setAccountBalance state addr balance) addr = some balance := by
  simp [accountBalance?, getAccount_setAccountBalance_same h_account]

theorem setAccountBalance_of_missing
    {state : WorldState} {addr : Address} {balance : Word256}
    (h_missing : getAccount state addr = none) :
    setAccountBalance state addr balance = state := by
  simp [setAccountBalance, h_missing]

theorem getAccount_setAccountBalance_ne
    {state : WorldState} {addr other : Address} {balance : Word256}
    (h_ne : other ≠ addr) :
    getAccount (setAccountBalance state addr balance) other = getAccount state other := by
  unfold setAccountBalance
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      exact getAccount_setAccount_ne state { account with balance := balance } h_ne

theorem accountBalance?_setAccountBalance_ne
    {state : WorldState} {addr other : Address} {balance : Word256}
    (h_ne : other ≠ addr) :
    accountBalance? (setAccountBalance state addr balance) other =
      accountBalance? state other := by
  simp [accountBalance?, getAccount_setAccountBalance_ne h_ne]

@[simp] theorem accountNonce?_empty (addr : Address) :
    accountNonce? empty addr = none := rfl

@[simp] theorem accountNonce?_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    accountNonce? (setAccount state addr account) addr = some account.nonce := by
  simp [accountNonce?]

theorem accountNonce?_eq_some_iff
    {state : WorldState} {addr : Address} {nonce : Nat} :
    accountNonce? state addr = some nonce ↔
      ∃ account, getAccount state addr = some account ∧ nonce = account.nonce := by
  unfold accountNonce?
  cases h_account : getAccount state addr with
  | none =>
      simp
  | some account =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro h_nonce
        exact ⟨account, rfl, h_nonce.symm⟩
      · rintro ⟨account', h_account', h_nonce⟩
        subst h_account'
        exact h_nonce.symm

theorem accountNonce?_eq_none_iff {state : WorldState} {addr : Address} :
    accountNonce? state addr = none ↔ getAccount state addr = none := by
  unfold accountNonce?
  cases getAccount state addr <;> simp

theorem accountNonce?_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    accountNonce? (setAccount state addr account) other = accountNonce? state other := by
  simp [accountNonce?, getAccount_setAccount_ne state account h_ne]

theorem getAccount_setAccountNonce_same
    {state : WorldState} {addr : Address} {account : Account} {nonce : Nat}
    (h_account : getAccount state addr = some account) :
    getAccount (setAccountNonce state addr nonce) addr =
      some { account with nonce := nonce } := by
  simp [setAccountNonce, h_account]

theorem accountNonce?_setAccountNonce_same
    {state : WorldState} {addr : Address} {account : Account} {nonce : Nat}
    (h_account : getAccount state addr = some account) :
    accountNonce? (setAccountNonce state addr nonce) addr = some nonce := by
  simp [accountNonce?, getAccount_setAccountNonce_same h_account]

theorem setAccountNonce_of_missing
    {state : WorldState} {addr : Address} {nonce : Nat}
    (h_missing : getAccount state addr = none) :
    setAccountNonce state addr nonce = state := by
  simp [setAccountNonce, h_missing]

theorem getAccount_setAccountNonce_ne
    {state : WorldState} {addr other : Address} {nonce : Nat}
    (h_ne : other ≠ addr) :
    getAccount (setAccountNonce state addr nonce) other = getAccount state other := by
  unfold setAccountNonce
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      exact getAccount_setAccount_ne state { account with nonce := nonce } h_ne

theorem accountNonce?_setAccountNonce_ne
    {state : WorldState} {addr other : Address} {nonce : Nat}
    (h_ne : other ≠ addr) :
    accountNonce? (setAccountNonce state addr nonce) other =
      accountNonce? state other := by
  simp [accountNonce?, getAccount_setAccountNonce_ne h_ne]

/-! ### Cross-field projection preservation

`setAccountCode`, `setAccountBalance`, and `setAccountNonce` mutate disjoint
`Account` fields, so each preserves the projections corresponding to the
other two fields, *unconditionally* (regardless of whether `addr` equals the
projected `other`). These lemmas are useful by CALL/CREATE/SELFDESTRUCT and
transaction independence proofs that need to argue a balance/nonce/code
update doesn't perturb the other fields. Authored for GH #123,
beads `evm-asm-4k251`. -/

theorem accountBalance?_setAccountCode
    (state : WorldState) (addr other : Address) (codeHash : Hash256) (code : List Byte) :
    accountBalance? (setAccountCode state addr codeHash code) other =
      accountBalance? state other := by
  unfold setAccountCode
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      by_cases h_eq : other = addr
      · subst h_eq
        simp [accountBalance?, h_account]
      · simp [accountBalance?_setAccount_ne _ _ h_eq]

theorem accountNonce?_setAccountCode
    (state : WorldState) (addr other : Address) (codeHash : Hash256) (code : List Byte) :
    accountNonce? (setAccountCode state addr codeHash code) other =
      accountNonce? state other := by
  unfold setAccountCode
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      by_cases h_eq : other = addr
      · subst h_eq
        simp [accountNonce?, h_account]
      · simp [accountNonce?_setAccount_ne _ _ h_eq]

theorem accountCode?_setAccountBalance
    (state : WorldState) (addr other : Address) (balance : Word256) :
    accountCode? (setAccountBalance state addr balance) other =
      accountCode? state other := by
  unfold setAccountBalance
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      by_cases h_eq : other = addr
      · subst h_eq
        simp [accountCode?, h_account]
      · simp [accountCode?_setAccount_ne _ _ h_eq]

theorem accountCodeHash?_setAccountBalance
    (state : WorldState) (addr other : Address) (balance : Word256) :
    accountCodeHash? (setAccountBalance state addr balance) other =
      accountCodeHash? state other := by
  unfold setAccountBalance
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      by_cases h_eq : other = addr
      · subst h_eq
        simp [accountCodeHash?, h_account]
      · simp [accountCodeHash?_setAccount_ne _ _ h_eq]

theorem accountNonce?_setAccountBalance
    (state : WorldState) (addr other : Address) (balance : Word256) :
    accountNonce? (setAccountBalance state addr balance) other =
      accountNonce? state other := by
  unfold setAccountBalance
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      by_cases h_eq : other = addr
      · subst h_eq
        simp [accountNonce?, h_account]
      · simp [accountNonce?_setAccount_ne _ _ h_eq]

theorem accountCode?_setAccountNonce
    (state : WorldState) (addr other : Address) (nonce : Nat) :
    accountCode? (setAccountNonce state addr nonce) other =
      accountCode? state other := by
  unfold setAccountNonce
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      by_cases h_eq : other = addr
      · subst h_eq
        simp [accountCode?, h_account]
      · simp [accountCode?_setAccount_ne _ _ h_eq]

theorem accountCodeHash?_setAccountNonce
    (state : WorldState) (addr other : Address) (nonce : Nat) :
    accountCodeHash? (setAccountNonce state addr nonce) other =
      accountCodeHash? state other := by
  unfold setAccountNonce
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      by_cases h_eq : other = addr
      · subst h_eq
        simp [accountCodeHash?, h_account]
      · simp [accountCodeHash?_setAccount_ne _ _ h_eq]

theorem accountBalance?_setAccountNonce
    (state : WorldState) (addr other : Address) (nonce : Nat) :
    accountBalance? (setAccountNonce state addr nonce) other =
      accountBalance? state other := by
  unfold setAccountNonce
  cases h_account : getAccount state addr with
  | none => rfl
  | some account =>
      by_cases h_eq : other = addr
      · subst h_eq
        simp [accountBalance?, h_account]
      · simp [accountBalance?_setAccount_ne _ _ h_eq]

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

end WorldState

end EvmAsm.EL
