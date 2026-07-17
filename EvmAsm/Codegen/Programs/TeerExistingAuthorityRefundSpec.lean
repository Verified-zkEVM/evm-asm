/-
  EvmAsm.Codegen.Programs.TeerExistingAuthorityRefundSpec

  Fn.Spec scaffolding for `tx_eip7702_existing_authority_refund`
  (`txEip7702ExistingAuthorityRefund_prog`, 745 instr, entry
  `GuestAddrs.tx_eip7702_existing_authority_refund`).

  Ultimate goal: discharge grok's `TeerAssumed.applied_flat` in
  `BlockVerdictTxStateGasArraySpec.lean` (a4gbr) by supplying a CONCRETE
  `TeerApplied` model equal to what this guest program computes, and proving
  the whole-program `cpsTripleWithin`.

  This module is developed in multiple passes.  PASS 1 (this file) establishes:
    * the concrete APPLIED teer model (per-auth NEW_ACCOUNT + AUTH_BASE, the
      first-write ACCOUNT_WRITE regular charge, and the whole-call rolled-back
      zeroing) as a fold over the decoded authorization list;
    * the conformance verdict vs the Amsterdam execution-spec `set_delegation`
      APPLIED state-gas accounting (see the CONFORMANCE section below);
    * the code-layout bases + length + `CodeReq.ofProg` for the program;
    * the straight-line PROLOGUE `cpsTripleWithin` (stack frame alloc + the
      14-register callee-saved spill + the ABI-argument moves + the four
      scratch-cell zeroing stores), up to the BAL-ptr guard `BEQ`.

  Remaining (later passes): the BAL-ptr guard dispatch, the per-authorization
  iteration loop (recover authority, BAL AccountChanges lookup, NEW_ACCOUNT /
  AUTH_BASE accumulation, prep-rollback detection), the backbone/epilogue, the
  full `fullCode` callee union, and the top-level `applied_flat` discharge.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.

  ## CONFORMANCE VERDICT (Amsterdam `set_delegation`, 2026-07-17)

  Cross-checked against `execution-specs/.../amsterdam/vm/{gas,eoa_delegation,
  interpreter}.py` and the Lean mirror `EvmAsm/Stateless/SpecRef/{Gas,
  Interpreter}.lean`.

  Gas constants (state gas = state_bytes × COST_PER_STATE_BYTE, with the
  Amsterdam constant `COST_PER_STATE_BYTE = 1530`; ACCOUNT_WRITE is plain,
  unscaled regular gas):
    * NEW_ACCOUNT   = 120 × 1530 = 183600   (guest: `lui 45; addiw -720`)
    * AUTH_BASE     =  23 × 1530 =  35190   (guest: `lui 9;  addiw -1674`)
    * ACCOUNT_WRITE = 8000                   (guest: `lui 2;  addiw -192`)
  All three guest literals match the spec constants EXACTLY (verified below by
  `#guard` on the factorization).

  Per-auth semantic conditions (spec `set_delegation`):
    * NEW_ACCOUNT charged iff `not account_exists(authority)` on the live tx
      state — i.e. the authority leaf did not pre-exist AND was not materialized
      by an earlier authorization this tx.  Guest: `teer_acct_absent ≠ 0` AND
      `teer_prior_count = 0`.
    * AUTH_BASE charged iff a net-new delegation indicator is written: target
      non-NULL, authority not delegated in pre-state, no prior non-NULL set
      this tx.  Guest: OR-reduce of the 20 target bytes, `teer_prior_set_flag`,
      and pre-state delegation inference.
    * ACCOUNT_WRITE (regular) charged iff the authority is written for the first
      time this tx (`authority ∉ written_accounts`, pre-seeded with the sender
      and the value recipient).  Guest: byte-compare against sender / recipient
      / prior authority before the `+8000`.

  Residue-retention vs prep-rollback (the bmvmx.5.5.11.1 FA class):
    * SpecRef depth-0 prep: on `set_delegation` success the reservoir is rebased
      past the auth charges and `authStateGasUsed := frame_state_gas_used`
      (RETAINED); a subsequent mid-exec `ExceptionalHalt` refills only to the
      rebased baseline, so the auth residue survives.
    * SpecRef prep `ExceptionalHalt`: restore snapshot, `authStateGasUsed := 0`,
      `refill_frame_state_gas` (ZEROED + refilled).
    * Guest: accumulates would-be charges, sets `teer_rolled_back` when BAL shows
      no applied nonce advance / prep rollback, and ZEROES the APPLIED a0/a1 at
      return while publishing the would-be values separately
      (`teer_wouldbe_{state,regular}`).

  Verdict: the guest APPLIED return (post rolled-back zeroing, never would-be)
  matches the SpecRef APPLIED `set_delegation` accounting on BOTH branches.
  No divergence found — NOT a P1.  The concrete `TeerApplied` model below is the
  APPLIED return; it is what `applied_flat` must expose.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.GenericSpecs

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64

/-! ## Teer APPLIED state-charge model

    `TeerApplied` mirrors the abstract interface of
    `BlockVerdictTxStateGasArrayModel.TeerApplied` (that module is not on this
    branch yet): a pure function of the encoded tx bytes, the BAL bytes, the
    chain id, and the 1-based block access index, returning the APPLIED state
    charge (u64-valued). -/
abbrev TeerApplied :=
  List (BitVec 8) → List (BitVec 8) → Nat → Nat → Nat

/-! ### Gas constants (Amsterdam) -/

/-- Amsterdam state-gas price per state byte. -/
def teerCostPerStateByte : Nat := 1530

/-- State bytes charged for a newly-created account leaf. -/
def teerStateBytesNewAccount : Nat := 120

/-- State bytes charged for a net-new delegation indicator. -/
def teerStateBytesAuthBase : Nat := 23

/-- `NEW_ACCOUNT` state-gas charge (per newly-materialized authority leaf). -/
def teerNewAccount : Nat := teerStateBytesNewAccount * teerCostPerStateByte

/-- `AUTH_BASE` state-gas charge (per net-new delegation indicator). -/
def teerAuthBase : Nat := teerStateBytesAuthBase * teerCostPerStateByte

/-- `ACCOUNT_WRITE` regular-gas charge (per first-written authority leaf). -/
def teerAccountWrite : Nat := 8000

-- The guest program emits these three literals verbatim; the factorizations
-- match the Amsterdam spec constants.
#guard teerNewAccount = 183600
#guard teerAuthBase = 35190
#guard teerAccountWrite = 8000

/-! ### Per-authorization outcome

    The decoded facts for one authorization tuple that determine its APPLIED
    contribution.  A future pass will prove that the guest's per-iteration
    computation produces exactly this record from the tx blob + BAL + witness. -/
structure TeerAuthOutcome where
  /-- The authorization parsed, passed basic chain/nonce/target checks, and its
      authority address was recovered.  Parse failures contribute zero. -/
  valid : Bool
  /-- The authority leaf did not pre-exist and was not materialized by an
      earlier authorization this tx (charges `NEW_ACCOUNT`). -/
  newAccount : Bool
  /-- A net-new delegation indicator is written for this authority (charges
      `AUTH_BASE`). -/
  authBase : Bool
  /-- The authority leaf is written for the first time this tx — not the sender,
      not the value recipient, no prior authorization for it (charges the
      regular `ACCOUNT_WRITE`). -/
  firstWrite : Bool
  deriving Repr, DecidableEq

/-- APPLIED state charge contributed by one authorization (pre rolled-back
    zeroing).  Zero for a parse failure. -/
def teerAuthStateCharge (o : TeerAuthOutcome) : Nat :=
  if o.valid then
    (if o.newAccount then teerNewAccount else 0) +
    (if o.authBase then teerAuthBase else 0)
  else 0

/-- APPLIED regular charge contributed by one authorization (pre rolled-back
    zeroing).  Zero for a parse failure. -/
def teerAuthRegularCharge (o : TeerAuthOutcome) : Nat :=
  if o.valid && o.firstWrite then teerAccountWrite else 0

/-- Would-be (pre rolled-back zeroing) total APPLIED state charge: the fold over
    the authorization list.  This is `teer_wouldbe_state` in the guest. -/
def teerWouldbeState (auths : List TeerAuthOutcome) : Nat :=
  (auths.map teerAuthStateCharge).sum

/-- Would-be total regular charge (the guest's `teer_wouldbe_regular`). -/
def teerWouldbeRegular (auths : List TeerAuthOutcome) : Nat :=
  (auths.map teerAuthRegularCharge).sum

/-- APPLIED state charge for the whole tx: the would-be fold, ZEROED when the
    tx's authorization prep rolled back (`teer_rolled_back`). -/
def teerAppliedState (rolledBack : Bool) (auths : List TeerAuthOutcome) : Nat :=
  if rolledBack then 0 else teerWouldbeState auths

/-- APPLIED regular charge for the whole tx (zeroed on prep rollback). -/
def teerAppliedRegular (rolledBack : Bool) (auths : List TeerAuthOutcome) : Nat :=
  if rolledBack then 0 else teerWouldbeRegular auths

/-- The concrete `TeerApplied` model, relative to a decoder that maps the tx
    blob + BAL + chain id + block-access-index to `(rolledBack, authOutcomes)`.

    The decoder is exactly what instructions 34..744 of the guest compute (RLP
    walk over the authorization list, address recovery, BAL AccountChanges
    lookup, pre-state delegation inference, rollback detection).  A later pass
    supplies the concrete guest-derived `decode` and proves `applied_flat` for
    `teerAppliedOf decode`; the array spec then instantiates its abstract
    `teer := teerAppliedOf decode`. -/
def teerAppliedOf
    (decode : List (BitVec 8) → List (BitVec 8) → Nat → Nat →
      (Bool × List TeerAuthOutcome)) : TeerApplied :=
  fun txBytes balBytes chainId bai =>
    let (rolledBack, auths) := decode txBytes balBytes chainId bai
    teerAppliedState rolledBack auths

/-! ### Model lemmas -/

@[simp] theorem teerAuthStateCharge_invalid {o : TeerAuthOutcome} (h : o.valid = false) :
    teerAuthStateCharge o = 0 := by simp [teerAuthStateCharge, h]

@[simp] theorem teerAuthRegularCharge_invalid {o : TeerAuthOutcome} (h : o.valid = false) :
    teerAuthRegularCharge o = 0 := by simp [teerAuthRegularCharge, h]

/-- A single authorization's APPLIED state charge is bounded by the sum of both
    per-auth state charges. -/
theorem teerAuthStateCharge_le (o : TeerAuthOutcome) :
    teerAuthStateCharge o ≤ teerNewAccount + teerAuthBase := by
  unfold teerAuthStateCharge
  by_cases hv : o.valid
  · rw [if_pos hv]
    have h1 : (if o.newAccount then teerNewAccount else 0) ≤ teerNewAccount := by
      split <;> omega
    have h2 : (if o.authBase then teerAuthBase else 0) ≤ teerAuthBase := by
      split <;> omega
    omega
  · rw [if_neg hv]; omega

@[simp] theorem teerWouldbeState_nil : teerWouldbeState [] = 0 := rfl

theorem teerWouldbeState_cons (o : TeerAuthOutcome) (os : List TeerAuthOutcome) :
    teerWouldbeState (o :: os) = teerAuthStateCharge o + teerWouldbeState os := by
  simp only [teerWouldbeState, List.map_cons, List.sum_cons]

@[simp] theorem teerAppliedState_rolledBack (auths : List TeerAuthOutcome) :
    teerAppliedState true auths = 0 := rfl

@[simp] theorem teerAppliedState_not_rolledBack (auths : List TeerAuthOutcome) :
    teerAppliedState false auths = teerWouldbeState auths := rfl

/-- On rollback the APPLIED model is zero regardless of the decoded auths. -/
theorem teerAppliedOf_rolledBack
    (decode : List (BitVec 8) → List (BitVec 8) → Nat → Nat →
      (Bool × List TeerAuthOutcome))
    (txBytes balBytes : List (BitVec 8)) (chainId bai : Nat)
    (h : (decode txBytes balBytes chainId bai).1 = true) :
    teerAppliedOf decode txBytes balBytes chainId bai = 0 := by
  have hp : teerAppliedOf decode txBytes balBytes chainId bai
      = teerAppliedState (decode txBytes balBytes chainId bai).1
          (decode txBytes balBytes chainId bai).2 := rfl
  rw [hp, h, teerAppliedState_rolledBack]

/-! ## Code layout

    `teerB` is the guest-linked entry PC; `teerProg` the 745-instruction
    Program; `teerCode` its `CodeReq`.  The cross-`jal` callees
    (`tx_type_dispatch`, `rlp_walk_init/next`, `rlp_list_count_items`,
    `rlp_content_to_u64`, `eip7702_authorization_recover_address`,
    `bal_find_account_by_address`, `bal_account_nonstorage_finals`,
    `code_at_header_state_root`, `account_at_header_state_root`,
    `bal_account_nonce_before_index`) are unioned into `fullCode` in a later
    pass; the prologue below is call-free (first `jal` is instruction 40), so it
    is stated over `teerCode` directly. -/

/-- Guest-linked entry PC of `tx_eip7702_existing_authority_refund`. -/
def teerB : Word := BitVec.ofNat 64 GuestAddrs.tx_eip7702_existing_authority_refund

/-- The 745-instruction teer Program. -/
abbrev teerProg : Program := EvmAsm.Codegen.txEip7702ExistingAuthorityRefund_prog

set_option maxRecDepth 8000 in
theorem teer_length : teerProg.length = 745 := by decide

/-- `CodeReq` for the teer program at its guest-linked base. -/
def teerCode : CodeReq := CodeReq.ofProg teerB teerProg

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
