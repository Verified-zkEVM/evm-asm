/-
  EvmAsm.EL.SelfdestructEffects

  Pure SELFDESTRUCT post-Cancun side-effect model (GH #113).

  This is the reference model the emitted `selfdestructTailAsm` handler will be
  proven to realize (a later phase of the SELFDESTRUCT verification plan). It is
  a faithful transcription of the **pinned oracle** `ethereum/execution-specs`
  `tests-zkevm@v0.5.0` (`bd8c673`), `amsterdam` fork,
  `vm/instructions/system.py::selfdestruct`, covering the *data effects* only —
  gas is modeled elsewhere and framed out of the handler triple, as it is for
  every proven opcode.

  The spec, in order (v0.5.0):
  * `move_ether(originator, beneficiary, balance(originator))` — transfer the
    full originator balance to the beneficiary (a no-op when they coincide);
  * `if beneficiary != originator: emit_transfer_log(originator, beneficiary,
    balance)` — a single EIP-7708 `Transfer` LOG3 from `SYSTEM_ADDRESS`, amount
    as 32 big-endian data bytes, skipped when the amount is zero. Self-destruct
    to self emits **no** log;
  * `if originator in created_accounts: accounts_to_delete.add(originator)` —
    register the originator for deletion iff created in the current tx. The
    balance is **not** zeroed here (end-of-tx deletion preserves the balance).

  NOTE on the pinned revision: v0.5.0 has **no burn log and no balance zeroing**
  (`git grep 'emit_burn_log\\|BURN_TOPIC' bd8c673 -- amsterdam` is empty). A
  *newer* execution-specs revision (`a0c182656`) adds `emit_burn_log`/`BURN_TOPIC`
  + balance zeroing; the emitted guest `selfdestructTailAsm` briefly implemented
  that newer behavior, and the guest-side repair aligning it back to v0.5.0
  (no burn log, balance preserved) is PR #10145 — after which guest, oracle,
  and this model agree, as the guest-realizes-model phase requires.
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
    word. Matches the codegen's `eip7708_transfer_topic` data. -/
def transferTopic : Word256 :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

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

theorem transferLog_topicCountOk (sender recipient : Address) (amount : Word256) :
    (transferLog sender recipient amount).topicCountOk := by
  simp [transferLog, LogEntry.topicCountOk]

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

/-- **Pure post-Cancun SELFDESTRUCT data effect** (pinned execution-specs
    v0.5.0). Given the pre-state balance map `bal`, the accumulated side effects
    `eff`, the executing contract `originator`, the popped `beneficiary`, and
    whether `originator` was created in the current tx (`createdInTx`, the
    EIP-6780 predicate), compute the new balances and side effects.

    Faithful to `amsterdam` `selfdestruct` at `bd8c673`: transfer the full
    balance; emit a single EIP-7708 `Transfer` log iff `beneficiary ≠ originator`
    and the amount is nonzero; register the originator for deletion iff created
    in tx (the balance is *not* zeroed). No burn log — that is a newer-spec
    behavior absent from the pinned oracle. -/
def postCancunSelfdestructEffect
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool) : Result :=
  let amount := bal originator
  let balances := moveEther bal originator beneficiary amount
  let logs :=
    if beneficiary ≠ originator ∧ amount ≠ 0 then
      eff.logs.appendLog (transferLog originator beneficiary amount)
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

/-- The balance map is always exactly `move_ether` — the deletion never zeros it
    (v0.5.0 preserves the balance). -/
@[simp] theorem balances_eq
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool) :
    (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).balances
      = moveEther bal originator beneficiary (bal originator) := rfl

/-- A zero-balance originator emits no log (the `emit_transfer_log` early
    return). -/
theorem logs_of_zero
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool) (h : bal originator = 0) :
    (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).effects.logs
      = eff.logs := by
  simp [postCancunSelfdestructEffect, h]

/-- Self-destruct to a distinct beneficiary with a nonzero balance emits the
    `Transfer` log and moves the balance out (originator → `−amount`,
    beneficiary → `+amount`). -/
theorem transfer_case
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator beneficiary : Address) (createdInTx : Bool)
    (hne : beneficiary ≠ originator) (hnz : bal originator ≠ 0) :
    (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).effects.logs
        = eff.logs.appendLog (transferLog originator beneficiary (bal originator))
    ∧ (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).balances originator
        = bal originator - bal originator
    ∧ (postCancunSelfdestructEffect bal eff originator beneficiary createdInTx).balances beneficiary
        = bal beneficiary + bal originator := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [postCancunSelfdestructEffect]; rw [if_pos ⟨hne, hnz⟩]
  · simpa using moveEther_src bal (bal originator) hne
  · simpa using moveEther_dst bal (bal originator) hne

/-- Self-destruct to self: no log and the balance is unchanged (`move_ether` is
    a no-op), regardless of `createdInTx`. Deletion still follows `createdInTx`
    (see `accountsToDelete_eq`). -/
theorem self_case
    (bal : Address → Word256) (eff : CallSideEffects)
    (originator : Address) (createdInTx : Bool) :
    (postCancunSelfdestructEffect bal eff originator originator createdInTx).effects.logs = eff.logs
    ∧ (postCancunSelfdestructEffect bal eff originator originator createdInTx).balances = bal := by
  refine ⟨?_, ?_⟩
  · simp [postCancunSelfdestructEffect]
  · simp [postCancunSelfdestructEffect, moveEther_self]

/-- Self-destruct to self, NOT created in tx: complete no-op on balances, logs,
    and deletions. -/
theorem self_not_created_noop
    (bal : Address → Word256) (eff : CallSideEffects) (originator : Address) :
    postCancunSelfdestructEffect bal eff originator originator false
      = { balances := bal, effects := eff } := by
  simp only [postCancunSelfdestructEffect, moveEther_self]
  cases eff
  simp

end SelfdestructEffects

end EvmAsm.EL
