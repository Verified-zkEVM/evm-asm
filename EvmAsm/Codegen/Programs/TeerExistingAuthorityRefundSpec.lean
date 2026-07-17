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

/-! ## Prologue: frame setup + ABI moves (instructions 0..20)

    From the guest entry PC, allocate the 160-byte stack frame (`addi sp,-160`),
    spill the 14 callee-saved / live registers (`ra`, `s0..s11`, `a5`) into the
    frame, move the five ABI arguments into their callee-saved homes
    (`a0..a4 → s0/s1/s2/s3/s4`), and zero the state-charge accumulator
    (`li s10, 0`).  Exit PC is `teerB + 84` — the first `la` of the four
    scratch-cell zeroing stores (the BAL-ptr guard `beq` follows at
    instruction 33).

    `sp0` is the incoming stack pointer; the 14 frame slots at `sp0-160 + k`
    (`k ∈ {0,8,…,104}`) are owned on entry and hold the saved values on exit;
    `a0..a4` are the incoming ABI values, `raIn`/`s*old`/`a5old` the incoming
    register values. -/
set_option maxRecDepth 8000 in
theorem teer_frame_setup_spec
    (sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old s8old s9old s10old
      s11old a5old a0 a1 a2 a3 a4 : Word) :
    cpsTripleWithin 21 teerB (teerB + 84) teerCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) **
        (.x8 ↦ᵣ s0old) ** (.x9 ↦ᵣ s1old) ** (.x15 ↦ᵣ a5old) **
        (.x18 ↦ᵣ s2old) ** (.x19 ↦ᵣ s3old) ** (.x20 ↦ᵣ s4old) **
        (.x21 ↦ᵣ s5old) ** (.x22 ↦ᵣ s6old) ** (.x23 ↦ᵣ s7old) **
        (.x24 ↦ᵣ s8old) ** (.x25 ↦ᵣ s9old) ** (.x26 ↦ᵣ s10old) **
        (.x27 ↦ᵣ s11old) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        memOwn ((sp0 - 160) + signExtend12 (0 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (8 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (16 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (24 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (32 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (40 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (48 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (56 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (64 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (72 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (80 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (88 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (96 : BitVec 12)) **
        memOwn ((sp0 - 160) + signExtend12 (104 : BitVec 12)))
      ((.x2 ↦ᵣ (sp0 - 160)) ** (.x1 ↦ᵣ raIn) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x15 ↦ᵣ a5old) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) **
        (.x21 ↦ᵣ s5old) ** (.x22 ↦ᵣ s6old) ** (.x23 ↦ᵣ s7old) **
        (.x24 ↦ᵣ s8old) ** (.x25 ↦ᵣ s9old) ** (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11old) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (((sp0 - 160) + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
        (((sp0 - 160) + signExtend12 (8 : BitVec 12)) ↦ₘ s0old) **
        (((sp0 - 160) + signExtend12 (16 : BitVec 12)) ↦ₘ s1old) **
        (((sp0 - 160) + signExtend12 (24 : BitVec 12)) ↦ₘ s2old) **
        (((sp0 - 160) + signExtend12 (32 : BitVec 12)) ↦ₘ s3old) **
        (((sp0 - 160) + signExtend12 (40 : BitVec 12)) ↦ₘ s4old) **
        (((sp0 - 160) + signExtend12 (48 : BitVec 12)) ↦ₘ s5old) **
        (((sp0 - 160) + signExtend12 (56 : BitVec 12)) ↦ₘ s6old) **
        (((sp0 - 160) + signExtend12 (64 : BitVec 12)) ↦ₘ s7old) **
        (((sp0 - 160) + signExtend12 (72 : BitVec 12)) ↦ₘ s8old) **
        (((sp0 - 160) + signExtend12 (80 : BitVec 12)) ↦ₘ s9old) **
        (((sp0 - 160) + signExtend12 (88 : BitVec 12)) ↦ₘ s10old) **
        (((sp0 - 160) + signExtend12 (96 : BitVec 12)) ↦ₘ s11old) **
        (((sp0 - 160) + signExtend12 (104 : BitVec 12)) ↦ₘ a5old)) := by
  have h0 := addi_spec_gen_same_within .x2 sp0 (-160 : BitVec 12) teerB (by decide)
  rw [show signExtend12 (-160 : BitVec 12) = (-160 : Word) from by decide,
      show sp0 + (-160 : Word) = sp0 - 160 from by bv_omega] at h0
  have h1 := sd_spec_gen_own_within .x2 .x1 (sp0 - 160) raIn (0 : BitVec 12) (teerB + 4)
  have h2 := sd_spec_gen_own_within .x2 .x8 (sp0 - 160) s0old (8 : BitVec 12) (teerB + 8)
  have h3 := sd_spec_gen_own_within .x2 .x9 (sp0 - 160) s1old (16 : BitVec 12) (teerB + 12)
  have h4 := sd_spec_gen_own_within .x2 .x18 (sp0 - 160) s2old (24 : BitVec 12) (teerB + 16)
  have h5 := sd_spec_gen_own_within .x2 .x19 (sp0 - 160) s3old (32 : BitVec 12) (teerB + 20)
  have h6 := sd_spec_gen_own_within .x2 .x20 (sp0 - 160) s4old (40 : BitVec 12) (teerB + 24)
  have h7 := sd_spec_gen_own_within .x2 .x21 (sp0 - 160) s5old (48 : BitVec 12) (teerB + 28)
  have h8 := sd_spec_gen_own_within .x2 .x22 (sp0 - 160) s6old (56 : BitVec 12) (teerB + 32)
  have h9 := sd_spec_gen_own_within .x2 .x23 (sp0 - 160) s7old (64 : BitVec 12) (teerB + 36)
  have h10 := sd_spec_gen_own_within .x2 .x24 (sp0 - 160) s8old (72 : BitVec 12) (teerB + 40)
  have h11 := sd_spec_gen_own_within .x2 .x25 (sp0 - 160) s9old (80 : BitVec 12) (teerB + 44)
  have h12 := sd_spec_gen_own_within .x2 .x26 (sp0 - 160) s10old (88 : BitVec 12) (teerB + 48)
  have h13 := sd_spec_gen_own_within .x2 .x27 (sp0 - 160) s11old (96 : BitVec 12) (teerB + 52)
  have h14 := sd_spec_gen_own_within .x2 .x15 (sp0 - 160) a5old (104 : BitVec 12) (teerB + 56)
  have h15 := mv_spec_gen_within .x8 .x10 a0 s0old (teerB + 60) (by decide)
  have h16 := mv_spec_gen_within .x9 .x11 a1 s1old (teerB + 64) (by decide)
  have h17 := mv_spec_gen_within .x18 .x12 a2 s2old (teerB + 68) (by decide)
  have h18 := mv_spec_gen_within .x19 .x13 a3 s3old (teerB + 72) (by decide)
  have h19 := mv_spec_gen_within .x20 .x14 a4 s4old (teerB + 76) (by decide)
  have h20 := li_spec_gen_within .x26 s10old (0 : Word) (teerB + 80) (by decide)
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
