/-
  EvmAsm.EL.SelfdestructEffects

  Pure SELFDESTRUCT post-Cancun side-effect model (GH #113).

  This is the reference model the emitted `selfdestructTailAsm` handler will be
  proven to realize (Phase 4 of the SELFDESTRUCT verification plan). It is a
  faithful transcription of `ethereum/execution-specs` (`amsterdam` fork,
  `vm/instructions/system.py::selfdestruct`), covering the *data effects* only —
  gas is modeled elsewhere and framed out of the handler triple, as it is for
  every proven opcode.

  The spec, in order:
  * `move_ether(originator, beneficiary, balance(originator))` — transfer the
    full originator balance to the beneficiary (a no-op when they coincide);
  * EIP-7708 log (`emit_burn_log` / `emit_transfer_log`): a `Burn` LOG2 when the
    originator was created in this tx and self-destructs to itself, otherwise a
    `Transfer` LOG3 to a distinct beneficiary — both emitted from `SYSTEM_ADDRESS`
    with the amount as 32 big-endian data bytes, and both a no-op when the amount
    is zero;
  * EIP-6780 deletion: register the originator for deletion (and zero its
    balance) iff it was created in the current tx.
-/

import EvmAsm.EL.CallValueTransfer
import EvmAsm.EL.CreatedAccounts
import EvmAsm.EL.MessageCallExecution

namespace EvmAsm.EL

namespace SelfdestructEffects

abbrev CallSideEffects := MessageCallExecution.CallSideEffects

/-! ## EIP-7708 log constants -/

/-- `SYSTEM_ADDRESS` (`0xff…fe`), the emitter of EIP-7708 synthetic logs
    (`amsterdam/fork.py`). -/
def systemAddress : Address := 0xfffffffffffffffffffffffffffffffffffffffe

/-- `TRANSFER_TOPIC = keccak256("Transfer(address,address,uint256)")`
    (`amsterdam/vm/__init__.py`), as the canonical big-endian 256-bit topic
    word. Matches the codegen's `eip7708_transfer_topic` data (Phase 4 confirms
    byte-identity). -/
def transferTopic : Word256 :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

/-- `BURN_TOPIC = keccak256("Burn(address,uint256)")`
    (`amsterdam/vm/__init__.py`), canonical big-endian 256-bit topic word.
    Matches the codegen's `eip7708_burn_topic` data. -/
def burnTopic : Word256 :=
  0xcc16f5dbb4873280815c1ee09dbd06736cffcc184412cf7a71a0fdb75d397ca5

/-- An address as a LOG topic: left-pad-zero to 32 bytes
    (`left_pad_zero_bytes(addr, 32)` → `Hash32`), i.e. numeric zero-extension of
    the 160-bit address to a 256-bit word. -/
def addressTopic (a : Address) : Word256 := a.setWidth 256

/-- A 256-bit word as its 32 big-endian bytes (`U256.to_be_bytes32()`): byte `i`
    (`0 ≤ i < 32`) is bits `[8·(31−i), 8·(31−i)+8)`, most-significant first. -/
def toBytes32BE (w : Word256) : List Byte :=
  (List.range 32).map (fun i => (w >>> (8 * (31 - i))).setWidth 8)

@[simp] theorem toBytes32BE_length (w : Word256) : (toBytes32BE w).length = 32 := by
  simp [toBytes32BE]

/-- The EIP-7708 `Transfer(sender, recipient, amount)` LOG3 entry. -/
def transferLog (sender recipient : Address) (amount : Word256) : LogEntry :=
  { emitter := systemAddress
    topics := [transferTopic, addressTopic sender, addressTopic recipient]
    data := toBytes32BE amount }

/-- The EIP-7708 `Burn(account, amount)` LOG2 entry. -/
def burnLog (account : Address) (amount : Word256) : LogEntry :=
  { emitter := systemAddress
    topics := [burnTopic, addressTopic account]
    data := toBytes32BE amount }

theorem transferLog_topicCountOk (sender recipient : Address) (amount : Word256) :
    (transferLog sender recipient amount).topicCountOk := by
  simp [transferLog, LogEntry.topicCountOk]

theorem burnLog_topicCountOk (account : Address) (amount : Word256) :
    (burnLog account amount).topicCountOk := by
  simp [burnLog, LogEntry.topicCountOk]

/-! ## Balance transfer (`move_ether`) -/

/-- Point-update a balance map. -/
def setBalance (bal : Address → Word256) (a : Address) (v : Word256) :
    Address → Word256 :=
  fun x => if x = a then v else bal x

@[simp] theorem setBalance_same (bal : Address → Word256) (a : Address) (v : Word256) :
    setBalance bal a v a = v := by simp [setBalance]

theorem setBalance_other (bal : Address → Word256) (a : Address) (v : Word256)
    {x : Address} (h : x ≠ a) : setBalance bal a v x = bal x := by
  simp [setBalance, h]

/-- `move_ether(src, dst, amt)`: subtract `amt` from `src`, then add `amt` to
    `dst`. Sequential update, so `src = dst` is a net no-op (matching the Python
    subtract-then-add). -/
def moveEther (bal : Address → Word256) (src dst : Address) (amt : Word256) :
    Address → Word256 :=
  setBalance (setBalance bal src (bal src - amt)) dst
    ((setBalance bal src (bal src - amt)) dst + amt)

theorem moveEther_self (bal : Address → Word256) (a : Address) (amt : Word256) :
    moveEther bal a a amt = bal := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [moveEther, setBalance]; bv_omega
  · simp [moveEther, setBalance, hx]

theorem moveEther_dst (bal : Address → Word256) {src dst : Address} (amt : Word256)
    (h : dst ≠ src) : moveEther bal src dst amt dst = bal dst + amt := by
  simp [moveEther, setBalance, h]

theorem moveEther_src (bal : Address → Word256) {src dst : Address} (amt : Word256)
    (h : dst ≠ src) : moveEther bal src dst amt src = bal src - amt := by
  simp [moveEther, setBalance, h.symm]

/-! ## The SELFDESTRUCT effect -/

/-- Result of applying `postCancunSelfdestructEffect`: the updated balance map
    and the updated side-effect bundle (logs + accounts-to-delete). -/
structure Result where
  balances : Address → Word256
  effects : CallSideEffects

/-- **Pure post-Cancun SELFDESTRUCT data effect.** Given the pre-state balance
    map `bal`, the accumulated side effects `eff`, the executing contract
    `originator`, the popped `beneficiary`, and whether `originator` was created
    in the current tx (`createdInTx`, the EIP-6780 predicate), compute the new
    balances and side effects.

    Faithful to `amsterdam` `selfdestruct`: transfer the full balance, emit the
    EIP-7708 burn/transfer log (skipping zero amounts), and register the
    originator for deletion (zeroing its balance) exactly when created in tx. -/
def postCancunSelfdestructEffect
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool) : Result :=
  let amount := bal originator
  let moved := moveEther bal originator beneficiary amount
  let balances := if createdInTx then setBalance moved originator 0 else moved
  let isSelf := beneficiary = originator
  let logs :=
    if amount = 0 then eff.logs
    else if createdInTx ∧ isSelf then eff.logs.appendLog (burnLog originator amount)
    else if ¬ isSelf then eff.logs.appendLog (transferLog originator beneficiary amount)
    else eff.logs
  let accountsToDelete :=
    if createdInTx then originator :: eff.accountsToDelete else eff.accountsToDelete
  { balances := balances
    effects :=
      { refundCounter := eff.refundCounter
        logs := logs
        accountsToDelete := accountsToDelete
        touchedAccounts := eff.touchedAccounts } }

/-! ### Characterization lemmas -/

/-- The originator is registered for deletion iff it was created in the tx. -/
@[simp] theorem accountsToDelete_eq
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool) :
    (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).effects.accountsToDelete
      = if createdInTx then originator :: eff.accountsToDelete else eff.accountsToDelete := rfl

/-- SELFDESTRUCT never touches the refund counter or touched-accounts set. -/
@[simp] theorem refundCounter_eq
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool) :
    (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).effects.refundCounter
      = eff.refundCounter := rfl

@[simp] theorem touchedAccounts_eq
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool) :
    (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).effects.touchedAccounts
      = eff.touchedAccounts := rfl

/-- A zero-balance originator emits no log (the `emit_*_log` early return). -/
theorem logs_of_zero
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool) (h : bal originator = 0) :
    (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).effects.logs
      = eff.logs := by
  simp [postCancunSelfdestructEffect, h]

/-- Self-destruct to a distinct beneficiary with a nonzero balance emits the
    `Transfer` log and moves the balance out. -/
theorem transfer_case
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool)
    (hne : beneficiary ≠ originator) (hnz : bal originator ≠ 0) :
    (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).effects.logs
      = eff.logs.appendLog (transferLog originator beneficiary (bal originator)) := by
  simp only [postCancunSelfdestructEffect]
  rw [if_neg hnz]
  by_cases hc : createdInTx
  · simp [hc, hne]
  · simp [hc, hne]

/-- Self-destruct to self, created in tx, nonzero balance: `Burn` log, and the
    balance is burned (originator ends at 0). -/
theorem burn_case
    (bal : Address → Word256) (eff : CallSideEffects) (originator : Address)
    (hnz : bal originator ≠ 0) :
    (postCancunSelfdestructEffect bal eff originator originator true).effects.logs
      = eff.logs.appendLog (burnLog originator (bal originator))
    ∧ (postCancunSelfdestructEffect bal eff originator originator true).balances originator = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [postCancunSelfdestructEffect]
    rw [if_neg hnz]
    simp
  · simp [postCancunSelfdestructEffect]

/-- Self-destruct to self, NOT created in tx: complete no-op on balances, logs,
    and deletions. -/
theorem self_not_created_noop
    (bal : Address → Word256) (eff : CallSideEffects) (originator : Address) :
    postCancunSelfdestructEffect bal eff originator originator false
      = { balances := bal, effects := eff } := by
  simp only [postCancunSelfdestructEffect, moveEther_self]
  by_cases hz : bal originator = 0 <;> cases eff <;> simp [hz]

end SelfdestructEffects

end EvmAsm.EL
