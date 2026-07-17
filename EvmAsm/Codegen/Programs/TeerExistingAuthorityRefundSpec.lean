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
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.EL.RLP.Basic
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.CodeReqExtents
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64
open EvmAsm.EL.RLP (Nat.fromBytesBE)

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
abbrev teerCode : CodeReq := CodeReq.ofProg teerB teerProg

/-! ### Scratch-cell guest globals (`.bss`)

    The four accumulator / flag cells the prologue zeroes, as `Word` addresses. -/
abbrev teerRegularRefund : Word := (GuestAddrs.teer_regular_refund : Word)
abbrev teerSuccessCount : Word := (GuestAddrs.teer_success_count : Word)
abbrev teerPredelegatedCount : Word := (GuestAddrs.teer_predelegated_count : Word)
abbrev teerRolledBack : Word := (GuestAddrs.teer_rolled_back : Word)

/-! ## `fullCode`: the teer program plus its 7 cross-`jal` callee Programs

    The teer body (`jal`s begin at instruction 40) calls into seven linked
    callee Programs.  `fullCode` is their image-level union, assembled as a
    `CodeReqExtents.ofEntries` fold over the `(guestBase, Program)` table in
    strictly ascending address order (teer itself is the highest-addressed
    entry).  A single decidable extent check (`extentsOkFrom`) discharges the
    entire pairwise (8-way) disjointness — ascending, non-overlapping byte
    extents make every earlier block miss every later block's addresses — and
    `ofProg_sub_ofEntries_of_extentsOk` then yields the per-entry monotonicity
    witnesses that `cpsTripleWithin_extend_code` consumes to lift each
    per-callee (and the teer body's own) triple into `fullCode`.

    The four *string-only* callees (`rlp_walk_init`, `rlp_walk_next`,
    `rlp_content_to_u64`, `bal_account_nonce_before_index`) have no standalone
    linked Program (they are inlined into `rlp_list_count_items` / emitted as
    asm), so they are NOT `fullCode` entries; they enter the top theorem as the
    assumed sub-contracts below. -/

/-- Guest-linked `(base, Program)` table for the teer closure, in strictly
    ascending base-address order.  Extents:
    `rlp_list_count_items` (0x8001cae0, 186 instr) is byte-adjacent to
    `tx_type_dispatch` (0x8001cdc8); teer (0x8002d10c, 745 instr) is last. -/
def teerFullEntries : List (Nat × Program) :=
  [ (GuestAddrs.rlp_list_count_items, EvmAsm.Codegen.rlpListCountItems_prog),
    (GuestAddrs.tx_type_dispatch, EvmAsm.Codegen.txTypeDispatch_prog),
    (GuestAddrs.account_at_header_state_root, EvmAsm.Codegen.accountAtHeaderStateRoot_prog),
    (GuestAddrs.code_at_header_state_root, EvmAsm.Codegen.codeAtHeaderStateRoot_prog),
    (GuestAddrs.bal_find_account_by_address, EvmAsm.Codegen.balFindAccountByAddress_prog),
    (GuestAddrs.bal_account_nonstorage_finals, EvmAsm.Codegen.balAccountNonstorageFinals_prog),
    (GuestAddrs.eip7702_authorization_recover_address,
      EvmAsm.Codegen.eip7702AuthorizationRecoverAddress_prog),
    (GuestAddrs.tx_eip7702_existing_authority_refund, teerProg) ]

/-- The full linked closure: teer plus its 7 cross-`jal` callee Programs. -/
def fullCode : CodeReq := CodeReq.ofEntries teerFullEntries

/-- The high extent bound: the end of the (last, highest-addressed) teer block. -/
def teerFullHi : Nat := GuestAddrs.tx_eip7702_existing_authority_refund + 4 * 745

set_option maxRecDepth 8000 in
/-- The one decidable extent check: strictly ascending, non-overlapping byte
    extents from the lowest callee base to the teer block end.  This single
    `decide` is the 8-way disjointness of the whole closure. -/
theorem teerFullEntries_extentsOk :
    CodeReq.extentsOkFrom GuestAddrs.rlp_list_count_items teerFullHi teerFullEntries = true := by
  decide

theorem teerFullHi_lt : teerFullHi < 2 ^ 64 := by decide

/-- Per-entry image subsumption: every callee (and teer) `ofProg` block is
    subsumed by `fullCode`. -/
theorem teerFull_sub :
    ∀ e ∈ teerFullEntries, ∀ a i,
      (CodeReq.ofProg (BitVec.ofNat 64 e.1) e.2) a = some i → fullCode a = some i :=
  CodeReq.ofProg_sub_ofEntries_of_extentsOk teerFullEntries_extentsOk teerFullHi_lt

/-- The teer program's own code is subsumed by the full closure. -/
theorem teer_mono : ∀ a i, teerCode a = some i → fullCode a = some i :=
  teerFull_sub (GuestAddrs.tx_eip7702_existing_authority_refund, teerProg)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self))))))))

/-- `tx_type_dispatch` callee code is subsumed by the full closure. -/
theorem txTypeDispatch_mono : ∀ a i,
    CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.tx_type_dispatch)
      EvmAsm.Codegen.txTypeDispatch_prog a = some i → fullCode a = some i :=
  teerFull_sub (GuestAddrs.tx_type_dispatch, EvmAsm.Codegen.txTypeDispatch_prog)
    (List.mem_cons_of_mem _ (List.mem_cons_self))

/-- `rlp_list_count_items` callee code is subsumed by the full closure. -/
theorem rlpListCountItems_mono : ∀ a i,
    CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.rlp_list_count_items)
      EvmAsm.Codegen.rlpListCountItems_prog a = some i → fullCode a = some i :=
  teerFull_sub (GuestAddrs.rlp_list_count_items, EvmAsm.Codegen.rlpListCountItems_prog)
    (List.mem_cons_self)

/-- `account_at_header_state_root` callee code is subsumed by the full closure. -/
theorem accountAtHeaderStateRoot_mono : ∀ a i,
    CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.account_at_header_state_root)
      EvmAsm.Codegen.accountAtHeaderStateRoot_prog a = some i → fullCode a = some i :=
  teerFull_sub (GuestAddrs.account_at_header_state_root,
      EvmAsm.Codegen.accountAtHeaderStateRoot_prog)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

/-- `code_at_header_state_root` callee code is subsumed by the full closure. -/
theorem codeAtHeaderStateRoot_mono : ∀ a i,
    CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.code_at_header_state_root)
      EvmAsm.Codegen.codeAtHeaderStateRoot_prog a = some i → fullCode a = some i :=
  teerFull_sub (GuestAddrs.code_at_header_state_root,
      EvmAsm.Codegen.codeAtHeaderStateRoot_prog)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self))))

/-- `bal_find_account_by_address` callee code is subsumed by the full closure. -/
theorem balFindAccountByAddress_mono : ∀ a i,
    CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.bal_find_account_by_address)
      EvmAsm.Codegen.balFindAccountByAddress_prog a = some i → fullCode a = some i :=
  teerFull_sub (GuestAddrs.bal_find_account_by_address,
      EvmAsm.Codegen.balFindAccountByAddress_prog)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self)))))

/-- `bal_account_nonstorage_finals` callee code is subsumed by the full closure. -/
theorem balAccountNonstorageFinals_mono : ∀ a i,
    CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.bal_account_nonstorage_finals)
      EvmAsm.Codegen.balAccountNonstorageFinals_prog a = some i → fullCode a = some i :=
  teerFull_sub (GuestAddrs.bal_account_nonstorage_finals,
      EvmAsm.Codegen.balAccountNonstorageFinals_prog)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))

/-- `eip7702_authorization_recover_address` callee code is subsumed by the full closure. -/
theorem eip7702AuthorizationRecoverAddress_mono : ∀ a i,
    CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.eip7702_authorization_recover_address)
      EvmAsm.Codegen.eip7702AuthorizationRecoverAddress_prog a = some i → fullCode a = some i :=
  teerFull_sub (GuestAddrs.eip7702_authorization_recover_address,
      EvmAsm.Codegen.eip7702AuthorizationRecoverAddress_prog)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self)))))))

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

/-! ## Prologue: scratch-cell zeroing (instructions 21..32)

    Four `la rd, sym ; sd zero, 0(rd)` sequences that zero the state-charge
    accumulator refund, the success count, the pre-delegated count, and the
    rolled-back flag.  The `la` (`AUIPC` + `ADDI`) pairs resolve to the guest
    `.bss` symbol addresses via `la_materialize_within`; the stores use
    `sd_spec_gen_own_within` with `x0` as the (zero) data register.  Entry PC is
    `teerB + 84` (continuing the frame-setup block); exit is `teerB + 132`, the
    BAL-ptr guard `beq` at instruction 33. -/
set_option maxRecDepth 8000 in
theorem teer_scratch_zero_spec (x5In : Word) :
    cpsTripleWithin 12 (teerB + 84) (teerB + 132) teerCode
      ((.x5 ↦ᵣ x5In) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn teerRegularRefund ** memOwn teerSuccessCount **
        memOwn teerPredelegatedCount ** memOwn teerRolledBack)
      ((.x5 ↦ᵣ teerRolledBack) ** (.x0 ↦ᵣ (0 : Word)) **
        (teerRegularRefund ↦ₘ (0 : Word)) ** (teerSuccessCount ↦ₘ (0 : Word)) **
        (teerPredelegatedCount ↦ₘ (0 : Word)) **
        (teerRolledBack ↦ₘ (0 : Word))) := by
  -- la teer_regular_refund (instrs 21,22 @ teerB+84,+88)
  have hlaA := la_materialize_within .x5 x5In (teerB + 84) teerRegularRefund
    (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 84) teerProg 21
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 84) teerRegularRefund))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 88) teerProg 22
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 84) teerRegularRefund))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have sA := sd_spec_gen_own_within .x5 .x0 teerRegularRefund (0 : Word) (0 : BitVec 12)
    (teerB + 92)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show teerRegularRefund + (0 : Word) = teerRegularRefund from by bv_omega] at sA
  -- la teer_success_count (instrs 24,25 @ teerB+96,+100)
  have hlaB := la_materialize_within .x5 teerRegularRefund (teerB + 96) teerSuccessCount
    (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 96) teerProg 24
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 96) teerSuccessCount))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 100) teerProg 25
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 96) teerSuccessCount))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have sB := sd_spec_gen_own_within .x5 .x0 teerSuccessCount (0 : Word) (0 : BitVec 12)
    (teerB + 104)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show teerSuccessCount + (0 : Word) = teerSuccessCount from by bv_omega] at sB
  -- la teer_predelegated_count (instrs 27,28 @ teerB+108,+112)
  have hlaC := la_materialize_within .x5 teerSuccessCount (teerB + 108) teerPredelegatedCount
    (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 108) teerProg 27
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 108) teerPredelegatedCount))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 112) teerProg 28
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 108) teerPredelegatedCount))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have sC := sd_spec_gen_own_within .x5 .x0 teerPredelegatedCount (0 : Word) (0 : BitVec 12)
    (teerB + 116)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show teerPredelegatedCount + (0 : Word) = teerPredelegatedCount from by bv_omega] at sC
  -- la teer_rolled_back (instrs 30,31 @ teerB+120,+124)
  have hlaD := la_materialize_within .x5 teerPredelegatedCount (teerB + 120) teerRolledBack
    (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 120) teerProg 30
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 120) teerRolledBack))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 124) teerProg 31
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 120) teerRolledBack))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have sD := sd_spec_gen_own_within .x5 .x0 teerRolledBack (0 : Word) (0 : BitVec 12)
    (teerB + 128)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show teerRolledBack + (0 : Word) = teerRolledBack from by bv_omega] at sD
  runBlock hlaA sA hlaB sB hlaC sC hlaD sD

/-! ## Prologue body: frame-setup ;; scratch-zeroing (instructions 0..32)

    Sequential composition of `teer_frame_setup_spec` and
    `teer_scratch_zero_spec` over the same `teerCode`, framing each block's
    footprint over the other (the two blocks touch disjoint resources: the
    frame block never touches `x5`/`x0`/the scratch cells, the scratch block
    never touches the frame registers or spill slots).  Straight line
    `teerB → teerB + 132`; the BAL-ptr guard `beq` at instruction 33 follows. -/
set_option maxRecDepth 8000 in
theorem teer_prologue_body_spec
    (sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old s8old s9old s10old
      s11old a5old a0 a1 a2 a3 a4 x5In : Word) :
    cpsTripleWithin 33 teerB (teerB + 132) teerCode
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) **
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
        memOwn ((sp0 - 160) + signExtend12 (104 : BitVec 12))) **
       ((.x5 ↦ᵣ x5In) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn teerRegularRefund ** memOwn teerSuccessCount **
        memOwn teerPredelegatedCount ** memOwn teerRolledBack))
      (((.x2 ↦ᵣ (sp0 - 160)) ** (.x1 ↦ᵣ raIn) **
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
        (((sp0 - 160) + signExtend12 (104 : BitVec 12)) ↦ₘ a5old)) **
       ((.x5 ↦ᵣ teerRolledBack) ** (.x0 ↦ᵣ (0 : Word)) **
        (teerRegularRefund ↦ₘ (0 : Word)) ** (teerSuccessCount ↦ₘ (0 : Word)) **
        (teerPredelegatedCount ↦ₘ (0 : Word)) **
        (teerRolledBack ↦ₘ (0 : Word)))) := by
  have hfs := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ x5In) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn teerRegularRefund ** memOwn teerSuccessCount **
      memOwn teerPredelegatedCount ** memOwn teerRolledBack)
    (by pcFree)
    (teer_frame_setup_spec sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old
      s8old s9old s10old s11old a5old a0 a1 a2 a3 a4)
  have hsz := cpsTripleWithin_frameL
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
      (((sp0 - 160) + signExtend12 (104 : BitVec 12)) ↦ₘ a5old))
    (by pcFree)
    (teer_scratch_zero_spec x5In)
  exact cpsTripleWithin_seq_same_cr hfs hsz

/-- The prologue postcondition with the two BAL-guard registers (`x18`/`s2`
    holding the moved `a2`, and `x0`) factored out — i.e. everything the guard
    `beq` does NOT read.  Framed around the guard so both exits retain the full
    saved-frame + zeroed-scratch state. -/
def teerPrologueRest
    (sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old s8old s9old s10old
      s11old a5old a0 a1 a2 a3 a4 : Word) : Assertion :=
  (.x2 ↦ᵣ (sp0 - 160)) ** (.x1 ↦ᵣ raIn) **
  (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x15 ↦ᵣ a5old) **
  (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) **
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
  (((sp0 - 160) + signExtend12 (104 : BitVec 12)) ↦ₘ a5old) **
  (.x5 ↦ᵣ teerRolledBack) **
  (teerRegularRefund ↦ₘ (0 : Word)) ** (teerSuccessCount ↦ₘ (0 : Word)) **
  (teerPredelegatedCount ↦ₘ (0 : Word)) ** (teerRolledBack ↦ₘ (0 : Word))

/-! ## Prologue + BAL-ptr guard (instructions 0..33)

    Appends the BAL-ptr guard `beq s2, zero` at instruction 33 (`teerB + 132`)
    to the prologue body as a `cpsBranchWithin`.  `s2` (`x18`) holds the moved
    `a2` = the BAL pointer.  Two exits:
      * TAKEN (`a2 = 0`): PC = `teerB + 2856` (instruction 714) — the
        no-BAL epilogue path that returns `a0 = a1 = 0` without parsing;
      * NOT-TAKEN (`a2 ≠ 0`): PC = `teerB + 136` (instruction 34) — the body
        entry (tx-type dispatch → per-authorization loop).
    Both exit postconditions carry the full prologue post (framed as `REST`)
    plus the guard's decided equality.  `34 = 33 + 1` steps. -/
set_option maxRecDepth 8000 in
theorem teer_prologue_spec
    (sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old s8old s9old s10old
      s11old a5old a0 a1 a2 a3 a4 x5In : Word) :
    cpsBranchWithin 34 teerB teerCode
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) **
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
        memOwn ((sp0 - 160) + signExtend12 (104 : BitVec 12))) **
       ((.x5 ↦ᵣ x5In) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn teerRegularRefund ** memOwn teerSuccessCount **
        memOwn teerPredelegatedCount ** memOwn teerRolledBack))
      -- TAKEN: a2 = 0, no-BAL epilogue path
      (teerB + 2856)
      (((.x18 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 = (0 : Word)⌝) ** teerPrologueRest
        sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old s8old s9old s10old
        s11old a5old a0 a1 a2 a3 a4)
      -- NOT-TAKEN: a2 ≠ 0, body entry
      (teerB + 136)
      (((.x18 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 ≠ (0 : Word)⌝) ** teerPrologueRest
        sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old s8old s9old s10old
        s11old a5old a0 a1 a2 a3 a4) := by
  have hbeq := beq_spec_gen_within .x18 .x0 (2724 : BitVec 13) a2 (0 : Word) (teerB + 132)
  rw [show (teerB + 132) + signExtend13 (2724 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2724 : BitVec 13) = (2724 : Word) from by decide]; bv_omega,
      show (teerB + 132) + 4 = teerB + 136 from by bv_omega] at hbeq
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 132) teerProg 33
    (.BEQ .x18 .x0 (2724 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  have hbeqE := cpsBranchWithin_extend_code hmem hbeq
  have hbeqF := cpsBranchWithin_frameR
    (teerPrologueRest sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old s8old
      s9old s10old s11old a5old a0 a1 a2 a3 a4)
    (by unfold teerPrologueRest; pcFree) hbeqE
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by unfold teerPrologueRest; xperm_hyp hp)
    (teer_prologue_body_spec sp0 raIn s0old s1old s2old s3old s4old s5old s6old s7old
      s8old s9old s10old s11old a5old a0 a1 a2 a3 a4 x5In)
    hbeqF

/-! ## Assumed sub-contracts (hypotheses, not axioms)

    The teer body `jal`s into four callees that have NO standalone linked
    Program on this branch (they are inlined into `rlp_list_count_items` or
    emitted only as asm strings), so they cannot enter `fullCode` as `ofProg`
    blocks.  Instead each enters the eventual top theorem as an *assumed*
    `cpsTripleWithin` contract — a structure whose `entry`/`cr` a future
    converted-callee Fn.Spec instantiates (drop-in via
    `cpsTripleWithin_extend_code`), NOT an axiom and NO `sorry`.

    Faithfulness: each contract's ABI (input/output register footprint) and its
    semantic result mirror the corresponding EXISTING proven top spec
    (`rlp_walk_init_spec_within`, `rlp_walk_next_spec_within`,
    `rlp_content_to_u64_spec_within` in `EvmAsm/Rv64/RLP/*`) at grok's
    single-primary-outcome abstraction level (cf. `IntrinsicAssumed`/
    `TeerAssumed` on a4gbr).  The result is expressed with the very predicates
    those specs establish (`EvmAsm.Rv64.RLP.rlpWalkNextOk` /
    `rlpItemDecode`, `Nat.fromBytesBE`), so a later conversion discharges the
    contract by construction. -/

/-- Over-approximate step budget for the (asm-only) BAL nonce lookup callee. -/
def nBalNonceSteps : Nat := 4096

/-- Assumed contract for `rlp_walk_init` (RLP list-cursor initializer).

    ABI (from `rlp_walk_init_spec_within`): a0 = list pointer
    (`listBase + off`), a1 = list length; returns a0 = element cursor, a1 = list
    end pointer, a2 = status (0 = success, ≠ 0 = a parse-shape failure that the
    teer loop treats as end-of-list / no contribution).  On success the cursor
    is the first content byte (short-list `p+1`, long-list `p + (lenlen+1)`);
    `x5,x6,x7,x28..x31` are scratch (owned on return). -/
structure RlpWalkInitAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `rlp_walk_init` Program. -/
  entry : Word
  /-- Cursor-init contract: success positions a0 at the list's first content
      byte and a2 = 0; failure returns a2 ≠ 0.  (Provenance side-conditions of
      the proven top spec are omitted at this abstraction level.) -/
  flat :
    ∀ (ret listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
      (listBytes : List (BitVec 8)) (listOff : Nat)
      (_halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
      (_hover : listBase.toNat + listOff < 2 ^ 64)
      (_hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true),
      cpsTripleWithin 81 entry (ret &&& ~~~1) cr
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ ret) ** bytesRegion listBase listBytes)
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) **
          bytesRegion listBase listBytes) **
         (fun h =>
           -- short-list success (a2 = 0): cursor = p + 1
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           -- long-list success (a2 = 0): cursor = p + (lenlen + 1)
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           -- parse-shape failure (a2 ≠ 0): cursor/end unspecified
           (∃ cur endp st : Word,
             (((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) ** ⌜st ≠ (0 : Word)⌝) h))))

/-- Assumed contract for `rlp_walk_next` (RLP item-cursor advance).

    ABI (from `rlp_walk_next_spec_within`): a0 = current cursor
    (`srcBase + off`), a1 = end pointer; returns via
    `EvmAsm.Rv64.RLP.rlpWalkNextOk` on success (a0 = next item, a1 = 0,
    a2 = item length) or one of five non-advance statuses (a1 ∈ {2,3,4,5,6},
    a2 = 0) that the teer loop treats as end-of-list / malformed. -/
structure RlpWalkNextAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `rlp_walk_next` Program. -/
  entry : Word
  /-- Cursor-advance contract mirroring `rlp_walk_next_spec_within`. -/
  flat :
    ∀ (ret srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
      (srcBytes : List (BitVec 8)) (srcOff : Nat)
      (_halign : srcBase.toNat % 8 = 0) (_hoff : srcOff < srcBytes.length)
      (_hover : srcBase.toNat + srcOff < 2 ^ 64)
      (_hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true),
      cpsTripleWithin 87 entry (ret &&& ~~~1) cr
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ ret) ** bytesRegion srcBase srcBytes)
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))

/-- Assumed contract for `rlp_content_to_u64` (big-endian RLP content → u64).

    Verbatim ABI + result of `rlp_content_to_u64_spec_within`: a0 = content
    pointer (`srcBase + off`), a1 = content length; returns a0 = value / status
    and a1 = status code.  On the accepting arm a0 = the big-endian value
    `Nat.fromBytesBE` of the `len` content bytes and a1 = 0. -/
structure RlpContentToU64Assumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `rlp_content_to_u64` Program. -/
  entry : Word
  /-- Content-decode contract mirroring `rlp_content_to_u64_spec_within`. -/
  flat :
    ∀ (ret srcBase t0Old x6Old t2Old t3Old : Word) (srcBytes : List (BitVec 8))
      (srcOff len : Nat) (_hlen64 : len < 2 ^ 64) (_hsalign : srcBase.toNat % 8 = 0)
      (_hslen : srcOff + len ≤ srcBytes.length)
      (_hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
      (_hsvalid : ∀ k, k < len →
        isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true),
      cpsTripleWithin (7 * len + 11) entry (ret &&& ~~~1) cr
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) **
          bytesRegion srcBase srcBytes)
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ ret) ** bytesRegion srcBase srcBytes) **
         (fun h =>
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
              ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
           (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
              (.x11 ↦ᵣ (0 : Word)) **
              ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff ≠ 0⌝) h)))

/-- Assumed contract for `bal_account_nonce_before_index` (asm-only callee).

    ABI (from `balAccountNonceBeforeIndexFunction`): a0 = AccountChanges
    pointer (`regionBase + off`), a1 = length, a2 = current block-access index;
    returns a0 = status (0 found / 1 no earlier change / 2 malformed) and, on
    the found arm, a1 = the latest post-nonce strictly before the index.  The
    found-nonce is exposed via the model field `nonceModel`, which a future
    conversion pins to the concrete `nonce_changes` scan. -/
structure BalAccountNonceBeforeIndexAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `bal_account_nonce_before_index`. -/
  entry : Word
  /-- The latest pre-index post-nonce, as a pure function of the AccountChanges
      bytes, its base offset, and the (1-based) block-access index; `none` when
      no strictly-earlier nonce change exists. -/
  nonceModel : List (BitVec 8) → Nat → Nat → Option Word
  /-- Nonce-lookup contract.  `x5,x6,x7,x28..x31` and `x11..x17` are scratch;
      the found arm publishes `nonceModel` into a1. -/
  flat :
    ∀ (ret regionBase loadPtr lenW baiW : Word) (bs : List (BitVec 8))
      (off len bai : Nat)
      (_hret : (ret &&& ~~~(1 : Word)) = ret)
      (_hload : loadPtr = regionBase + BitVec.ofNat 64 off)
      (_hlen : lenW = BitVec.ofNat 64 len) (_hbai : baiW = BitVec.ofNat 64 bai)
      (_hbound : off + len ≤ bs.length),
      cpsTripleWithin nBalNonceSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ baiW) **
          bytesRegion regionBase bs **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) ** bytesRegion regionBase bs **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (fun h =>
            -- found (a0 = 0): a1 = the modelled pre-index nonce
            (∃ nonce, nonceModel bs off bai = some nonce ∧
              (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ nonce)) h)) ∨
            -- no earlier change (a0 = 1)
            (nonceModel bs off bai = none ∧ (((.x10 ↦ᵣ (1 : Word)) ** regOwn .x11) h)) ∨
            -- malformed (a0 = 2)
            (((.x10 ↦ᵣ (2 : Word)) ** regOwn .x11) h)))

/-- Combined modular hypotheses for the eventual teer top theorem: the four
    string-only callee contracts over the shared `fullCode`. -/
structure TeerAssumedCallees (cr : CodeReq) where
  walkInit : RlpWalkInitAssumed cr
  walkNext : RlpWalkNextAssumed cr
  contentToU64 : RlpContentToU64Assumed cr
  nonceBeforeIndex : BalAccountNonceBeforeIndexAssumed cr

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
