/-
  EvmAsm.Codegen.Programs.AccountAccessorTopSpec

  Lives under Codegen/Programs (not Evm64) because it pins concrete linked
  `GuestAddrs`/emitted `Codegen` programs (layering L1: verified core may not
  import Codegen) — same shape as the other `*SAsm.lean` linked-PC
  verification files in this directory. Its theorems still describe genuine
  Evm64-level opcode semantics (`open EvmAsm.Evm64` below).

  Top-level success-path `cpsTripleWithin` triple for the migrated
  `account_extract_balance` accessor body
  (`EvmAsm/Codegen/Programs/AccountFieldExtract.lean`):

    * `account_extract_balance_spec_within` — `accountExtractBalance_prog`
      (35 instructions, entry `GuestAddrs.account_extract_balance`): from
      `a0 = ptr(encodeAccount a)`, `a1 = |encodeAccount a|`, `a2 = out ptr`,
      the body terminates at the caller's return address with `a0 = 0` and
      the 32-byte output cell holding `word256Bytes32 a.balance`.

  `account_extract_nonce`'s top-level triple (same shape, `a.nonce < 2^64`
  per EIP-2681, u64 output cell) is split out into
  `AccountAccessorNonceSpec.lean` (file-size guardrail); that file imports
  this one for the shared infrastructure below.

  ## Composition structure

  Each accessor body keeps a real stack frame (`ADDI sp, sp, -N` +
  `SD`/`LD` of `ra`/`s0`(/`s1`)), performs three (nonce) / four (balance)
  fixed-guest-address `jal` calls composed via `WP.cpsCallWithin`, and
  branches to a shared failure arm after each call — refuted here by the
  deterministic-success callee triples from
  `EvmAsm/Evm64/AccountAccessorSpec.lean`.

  The scratch registers are threaded through the call chain as `regOwn`
  ownership: the `ownifyN` helpers below convert the ∀-quantified
  pinned-scratch callee triples into ownership-precondition form
  (`cpsTripleWithin_of_forall_regIs_to_regOwn`), so each callee's clobbered
  `regOwn` post feeds the next callee's pre without re-pinning. The single
  accessor instruction that *reads* a clobbered scratch register (`SUB x5
  x10 x12`, deriving the content pointer) lives in a `…_tail_spec_within`
  lemma ∀-quantified over that register and ownified once.

  ## Code layout

  The four verified helper bodies sit at their linked guest addresses
  (`EvmAsm/Codegen/GuestAddrs.lean`), pinned here as `Word` constants with
  `rfl` guards. The layout is contiguous:
    rlp_walk_init  (53 instrs)
    rlp_walk_next  (103)
    rlp_content_to_u64  (22)
    rlp_content_to_u256_be (26)
    account_extract_balance (35)
    account_extract_nonce   (23)

  Address ranges are deliberately not restated here: they regenerate from
  `GuestAddrs`, and restating literals recreates the drift condition
  (GH #10790).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Evm64.AccountAccessorSpec
import EvmAsm.Codegen.Programs.AccountFieldExtract
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen

open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.Tactics

/-! ## Fixed guest addresses (pinned to `Codegen.GuestAddrs`) -/

/-- Guest entry of `rlp_walk_init`. -/
def walkInitBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.rlp_walk_init
/-- Guest entry of `rlp_walk_next`. -/
def walkNextBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.rlp_walk_next
/-- Guest entry of `rlp_content_to_u64`. -/
def contentU64Base : Word := BitVec.ofNat 64 Codegen.GuestAddrs.rlp_content_to_u64
/-- Guest entry of `rlp_content_to_u256_be`. -/
def contentU256Base : Word := BitVec.ofNat 64 Codegen.GuestAddrs.rlp_content_to_u256_be
/-- Guest entry of `account_extract_nonce`. -/
def extractNonceBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.account_extract_nonce
/-- Guest entry of `account_extract_balance`. -/
def extractBalanceBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.account_extract_balance

theorem accountExtractNonce_prog_length :
    Codegen.accountExtractNonce_prog.length = 23 := by decide
theorem accountExtractBalance_prog_length :
    Codegen.accountExtractBalance_prog.length = 35 := by decide

/-! ## Deployed code layouts -/

/-- The `account_extract_nonce` body at its linked guest address. -/
abbrev accountExtractNonceCode : CodeReq :=
  CodeReq.ofProg extractNonceBase Codegen.accountExtractNonce_prog

/-- The `account_extract_balance` body at its linked guest address. -/
abbrev accountExtractBalanceCode : CodeReq :=
  CodeReq.ofProg extractBalanceBase Codegen.accountExtractBalance_prog

/-- Full deployed layout for `account_extract_nonce`: the accessor body plus
    its three callees at their linked guest addresses. -/
abbrev accountExtractNonceFullCode : CodeReq :=
  accountExtractNonceCode.union
    ((rlp_walk_init_code walkInitBase).union
      ((rlp_walk_next_code walkNextBase).union
        (rlp_content_to_u64_code contentU64Base)))

/-- Full deployed layout for `account_extract_balance`. -/
abbrev accountExtractBalanceFullCode : CodeReq :=
  accountExtractBalanceCode.union
    ((rlp_walk_init_code walkInitBase).union
      ((rlp_walk_next_code walkNextBase).union
        (rlp_content_to_u256_be_code contentU256Base)))

/-! ## Layout disjointness -/

private theorem aen_wi_disjoint :
    accountExtractNonceCode.Disjoint (rlp_walk_init_code walkInitBase) :=
  CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 53
    accountExtractNonce_prog_length rlp_walk_init_prog_length
    (fun k1 k2 hk1 hk2 => by unfold extractNonceBase walkInitBase Codegen.GuestAddrs.account_extract_nonce Codegen.GuestAddrs.rlp_walk_init; bv_omega)

private theorem aen_wn_disjoint :
    accountExtractNonceCode.Disjoint (rlp_walk_next_code walkNextBase) :=
  CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 103
    accountExtractNonce_prog_length rlp_walk_next_prog_length
    (fun k1 k2 hk1 hk2 => by unfold extractNonceBase walkNextBase Codegen.GuestAddrs.account_extract_nonce Codegen.GuestAddrs.rlp_walk_next; bv_omega)

private theorem aen_cu64_disjoint :
    accountExtractNonceCode.Disjoint (rlp_content_to_u64_code contentU64Base) :=
  CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 22
    accountExtractNonce_prog_length rlp_content_to_u64_prog_length
    (fun k1 k2 hk1 hk2 => by unfold extractNonceBase contentU64Base Codegen.GuestAddrs.account_extract_nonce Codegen.GuestAddrs.rlp_content_to_u64; bv_omega)

private theorem aeb_wi_disjoint :
    accountExtractBalanceCode.Disjoint (rlp_walk_init_code walkInitBase) :=
  CodeReq.ofProg_disjoint_range_len _ _ 35 _ _ 53
    accountExtractBalance_prog_length rlp_walk_init_prog_length
    (fun k1 k2 hk1 hk2 => by unfold extractBalanceBase walkInitBase Codegen.GuestAddrs.account_extract_balance Codegen.GuestAddrs.rlp_walk_init; bv_omega)

private theorem aeb_wn_disjoint :
    accountExtractBalanceCode.Disjoint (rlp_walk_next_code walkNextBase) :=
  CodeReq.ofProg_disjoint_range_len _ _ 35 _ _ 103
    accountExtractBalance_prog_length rlp_walk_next_prog_length
    (fun k1 k2 hk1 hk2 => by unfold extractBalanceBase walkNextBase Codegen.GuestAddrs.account_extract_balance Codegen.GuestAddrs.rlp_walk_next; bv_omega)

private theorem aeb_cu256_disjoint :
    accountExtractBalanceCode.Disjoint (rlp_content_to_u256_be_code contentU256Base) :=
  CodeReq.ofProg_disjoint_range_len _ _ 35 _ _ 26
    accountExtractBalance_prog_length rlp_content_to_u256_be_prog_length
    (fun k1 k2 hk1 hk2 => by unfold extractBalanceBase contentU256Base Codegen.GuestAddrs.account_extract_balance Codegen.GuestAddrs.rlp_content_to_u256_be; bv_omega)

private theorem wi_wn_disjoint :
    (rlp_walk_init_code walkInitBase).Disjoint (rlp_walk_next_code walkNextBase) :=
  CodeReq.ofProg_disjoint_range_len _ _ 53 _ _ 103
    rlp_walk_init_prog_length rlp_walk_next_prog_length
    (fun k1 k2 hk1 hk2 => by unfold walkInitBase walkNextBase Codegen.GuestAddrs.rlp_walk_init Codegen.GuestAddrs.rlp_walk_next; bv_omega)

private theorem wi_cu64_disjoint :
    (rlp_walk_init_code walkInitBase).Disjoint (rlp_content_to_u64_code contentU64Base) :=
  CodeReq.ofProg_disjoint_range_len _ _ 53 _ _ 22
    rlp_walk_init_prog_length rlp_content_to_u64_prog_length
    (fun k1 k2 hk1 hk2 => by unfold walkInitBase contentU64Base Codegen.GuestAddrs.rlp_walk_init Codegen.GuestAddrs.rlp_content_to_u64; bv_omega)

private theorem wn_cu64_disjoint :
    (rlp_walk_next_code walkNextBase).Disjoint (rlp_content_to_u64_code contentU64Base) :=
  CodeReq.ofProg_disjoint_range_len _ _ 103 _ _ 22
    rlp_walk_next_prog_length rlp_content_to_u64_prog_length
    (fun k1 k2 hk1 hk2 => by unfold walkNextBase contentU64Base Codegen.GuestAddrs.rlp_walk_next Codegen.GuestAddrs.rlp_content_to_u64; bv_omega)

private theorem wi_cu256_disjoint :
    (rlp_walk_init_code walkInitBase).Disjoint (rlp_content_to_u256_be_code contentU256Base) :=
  CodeReq.ofProg_disjoint_range_len _ _ 53 _ _ 26
    rlp_walk_init_prog_length rlp_content_to_u256_be_prog_length
    (fun k1 k2 hk1 hk2 => by unfold walkInitBase contentU256Base Codegen.GuestAddrs.rlp_walk_init Codegen.GuestAddrs.rlp_content_to_u256_be; bv_omega)

private theorem wn_cu256_disjoint :
    (rlp_walk_next_code walkNextBase).Disjoint (rlp_content_to_u256_be_code contentU256Base) :=
  CodeReq.ofProg_disjoint_range_len _ _ 103 _ _ 26
    rlp_walk_next_prog_length rlp_content_to_u256_be_prog_length
    (fun k1 k2 hk1 hk2 => by unfold walkNextBase contentU256Base Codegen.GuestAddrs.rlp_walk_next Codegen.GuestAddrs.rlp_content_to_u256_be; bv_omega)

/-! ### Subsumption of each layout piece into the full layouts -/

/-- Exposed (not `private`): shared by `AccountAccessorNonceSpec.lean`,
    which the file-size guardrail split off `account_extract_nonce`'s
    top-level triple into. -/
theorem aen_sub : ∀ a i, accountExtractNonceCode a = some i →
    accountExtractNonceFullCode a = some i :=
  CodeReq.union_mono_left

/-- Exposed (not `private`): see `aen_sub`. -/
theorem aen_wi_sub : ∀ a i, (rlp_walk_init_code walkInitBase) a = some i →
    accountExtractNonceFullCode a = some i :=
  CodeReq.mono_union_right aen_wi_disjoint CodeReq.union_mono_left

/-- Exposed (not `private`): see `aen_sub`. -/
theorem aen_wn_sub : ∀ a i, (rlp_walk_next_code walkNextBase) a = some i →
    accountExtractNonceFullCode a = some i :=
  CodeReq.mono_union_right aen_wn_disjoint
    (CodeReq.mono_union_right wi_wn_disjoint CodeReq.union_mono_left)

/-- Exposed (not `private`): see `aen_sub`. -/
theorem aen_cu64_sub : ∀ a i, (rlp_content_to_u64_code contentU64Base) a = some i →
    accountExtractNonceFullCode a = some i :=
  CodeReq.mono_union_right aen_cu64_disjoint
    (CodeReq.mono_union_right wi_cu64_disjoint
      (CodeReq.mono_union_right wn_cu64_disjoint (fun _ _ h => h)))

private theorem aeb_sub : ∀ a i, accountExtractBalanceCode a = some i →
    accountExtractBalanceFullCode a = some i :=
  CodeReq.union_mono_left

private theorem aeb_wi_sub : ∀ a i, (rlp_walk_init_code walkInitBase) a = some i →
    accountExtractBalanceFullCode a = some i :=
  CodeReq.mono_union_right aeb_wi_disjoint CodeReq.union_mono_left

private theorem aeb_wn_sub : ∀ a i, (rlp_walk_next_code walkNextBase) a = some i →
    accountExtractBalanceFullCode a = some i :=
  CodeReq.mono_union_right aeb_wn_disjoint
    (CodeReq.mono_union_right wi_wn_disjoint CodeReq.union_mono_left)

private theorem aeb_cu256_sub : ∀ a i, (rlp_content_to_u256_be_code contentU256Base) a = some i →
    accountExtractBalanceFullCode a = some i :=
  CodeReq.mono_union_right aeb_cu256_disjoint
    (CodeReq.mono_union_right wi_cu256_disjoint
      (CodeReq.mono_union_right wn_cu256_disjoint (fun _ _ h => h)))

/-! ## `ownifyN`: convert pinned-scratch triples to ownership-precondition form

    `cpsTripleWithin_of_forall_regIs_to_regOwn` peels one trailing
    `(r ↦ᵣ v)` pin into `regOwn r`; these helpers iterate it for the 2–5
    scratch pins of the callee triples, with `xperm_hyp` regrouping the
    precondition between peels. -/

/-- Exposed (not `private`): see `aen_sub`. -/
theorem ownify1 {n : Nat} {e x : Word} {cr : CodeReq} {P Q : Assertion} {r : Reg}
    (h : ∀ v, cpsTripleWithin n e x cr (P ** (r ↦ᵣ v)) Q) :
    cpsTripleWithin n e x cr (P ** regOwn r) Q :=
  cpsTripleWithin_of_forall_regIs_to_regOwn h

private theorem ownify2 {n : Nat} {e x : Word} {cr : CodeReq} {P Q : Assertion} {r1 r2 : Reg}
    (h : ∀ v1 v2, cpsTripleWithin n e x cr (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)) Q) :
    cpsTripleWithin n e x cr (P ** regOwn r1 ** regOwn r2) Q := by
  have h1 : ∀ v1, cpsTripleWithin n e x cr ((P ** (r1 ↦ᵣ v1)) ** regOwn r2) Q := fun v1 =>
    ownify1 (fun v2 =>
      cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) (h v1 v2))
  have h2 : cpsTripleWithin n e x cr ((P ** regOwn r2) ** regOwn r1) Q :=
    ownify1 (fun v1 =>
      cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) (h1 v1))
  exact cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) h2

private theorem ownify3 {n : Nat} {e x : Word} {cr : CodeReq} {P Q : Assertion} {r1 r2 r3 : Reg}
    (h : ∀ v1 v2 v3, cpsTripleWithin n e x cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin n e x cr (P ** regOwn r1 ** regOwn r2 ** regOwn r3) Q := by
  have h1 : ∀ v1, cpsTripleWithin n e x cr
      ((P ** (r1 ↦ᵣ v1)) ** regOwn r2 ** regOwn r3) Q := fun v1 =>
    ownify2 (fun v2 v3 =>
      cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) (h v1 v2 v3))
  have h2 : cpsTripleWithin n e x cr ((P ** regOwn r2 ** regOwn r3) ** regOwn r1) Q :=
    ownify1 (fun v1 =>
      cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) (h1 v1))
  exact cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) h2

private theorem ownify4 {n : Nat} {e x : Word} {cr : CodeReq} {P Q : Assertion}
    {r1 r2 r3 r4 : Reg}
    (h : ∀ v1 v2 v3 v4, cpsTripleWithin n e x cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4)) Q) :
    cpsTripleWithin n e x cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4) Q := by
  have h1 : ∀ v1, cpsTripleWithin n e x cr
      ((P ** (r1 ↦ᵣ v1)) ** regOwn r2 ** regOwn r3 ** regOwn r4) Q := fun v1 =>
    ownify3 (fun v2 v3 v4 =>
      cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) (h v1 v2 v3 v4))
  have h2 : cpsTripleWithin n e x cr
      ((P ** regOwn r2 ** regOwn r3 ** regOwn r4) ** regOwn r1) Q :=
    ownify1 (fun v1 =>
      cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) (h1 v1))
  exact cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) h2

private theorem ownify5 {n : Nat} {e x : Word} {cr : CodeReq} {P Q : Assertion}
    {r1 r2 r3 r4 r5 : Reg}
    (h : ∀ v1 v2 v3 v4 v5, cpsTripleWithin n e x cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5)) Q) :
    cpsTripleWithin n e x cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5) Q := by
  have h1 : ∀ v1, cpsTripleWithin n e x cr
      ((P ** (r1 ↦ᵣ v1)) ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5) Q := fun v1 =>
    ownify4 (fun v2 v3 v4 v5 =>
      cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) (h v1 v2 v3 v4 v5))
  have h2 : cpsTripleWithin n e x cr
      ((P ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5) ** regOwn r1) Q :=
    ownify1 (fun v1 =>
      cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) (h1 v1))
  exact cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq) h2

/-! ## Ownership-precondition forms of the callee triples -/

/-- `account_rlp_walk_next_field0_spec_within` with ownership-only scratch:
    all five clobbered scratch registers enter as `regOwn`, so a preceding
    callee's `regOwn` post feeds this directly. -/
theorem account_rlp_walk_next_field0_own_spec_within
    (base listBase raVal a2Old : Word) (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      (((.x10 ↦ᵣ (listBase + 2)) **
        (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29)
      ((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase (encodeAccount a)) := by
  refine ownify5 (fun t0Old t1Old t2Old t3Old t4Old =>
    cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq)
      (account_rlp_walk_next_field0_spec_within base listBase raVal a2Old t0Old t1Old t2Old
        t3Old t4Old a hnonce hsalign hover hvalid))

/-- `account_rlp_walk_next_field1_spec_within` with ownership-only scratch. -/
theorem account_rlp_walk_next_field1_own_spec_within
    (base listBase raVal a2Old : Word) (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      (((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
        (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29)
      ((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase (encodeAccount a)) := by
  refine ownify5 (fun t0Old t1Old t2Old t3Old t4Old =>
    cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq)
      (account_rlp_walk_next_field1_spec_within base listBase raVal a2Old t0Old t1Old t2Old
        t3Old t4Old a hnonce hsalign hover hvalid))

/-- `account_rlp_content_to_u64_nonce_spec_within` with ownership-only
    `x6`/`x7`/`x28` scratch (`x5`, concretely known at the accessor's call
    site as the just-derived content pointer, stays a pin). -/
theorem account_rlp_content_to_u64_nonce_own_spec_within
    (base listBase raVal t0Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * (Nat.toBytesBE a.nonce).length + 11) base (raVal &&& ~~~1)
      (rlp_content_to_u64_code base)
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64
          ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            - (Nat.toBytesBE a.nonce).length))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
        (.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase (encodeAccount a)) **
       ((.x10 ↦ᵣ (BitVec.ofNat 64 a.nonce)) ** (.x11 ↦ᵣ (0 : Word)))) := by
  refine ownify3 (fun x6Old t2Old t3Old =>
    cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq)
      (account_rlp_content_to_u64_nonce_spec_within base listBase raVal t0Old x6Old t2Old
        t3Old a hnonce hsalign hover hvalid))

/-- `account_rlp_content_to_u256_be_balance_spec_within` with ownership-only
    `x6`/`x7`/`x28`/`x29` scratch (`x5` stays a pin, as above). -/
theorem account_rlp_content_to_u256_be_balance_own_spec_within
    (base listBase outPtr raVal x5Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hdvalid : ∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * (Nat.toBytesBE a.balance.toNat).length + 16) base (raVal &&& ~~~1)
      (rlp_content_to_u256_be_code base)
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64
          (((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
              + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length)
            - (Nat.toBytesBE a.balance.toNat).length))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ x5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a) ** memOwnU256 outPtr) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29)
      (((.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        (.x12 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a)) **
       ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance))) := by
  refine ownify4 (fun x6Old x7Old x28Old x29Old =>
    cpsTripleWithin_weaken (fun hh hp => by xperm_hyp hp) (fun _ hq => hq)
      (account_rlp_content_to_u256_be_balance_spec_within base listBase outPtr raVal x5Old
        x6Old x7Old x28Old x29Old a hnonce hsalign hoalign hover hoover hvalid hdvalid))

/-- `memOwnU256` is PC-free — lets `pcFree` discharge frame side-conditions. -/
instance (outPtr : Word) : Assertion.PCFree (memOwnU256 outPtr) :=
  ⟨by unfold memOwnU256; pcFree⟩

/-! ## `account_extract_balance`: success tail (idx 17..24, 30..34) -/

set_option maxRecDepth 8000 in
/-- **Success tail of `account_extract_balance`** (from `+68`, right after the
    second `rlp_walk_next` success branch): derive the content window
    (`SUB x5, a0, a2` / `MV` glue), call `rlp_content_to_u256_be` (which
    right-aligns the balance into the 32-byte cell), set `a0 = 0`, skip the
    failure arm, restore `ra`/`s0`/`s1`/`sp` from the stack frame, and return.
    ∀-quantified over `x5`'s incoming value `t0Old` (the sole scratch register
    the accessor itself reads), packaged as the trailing factor for `ownify1`. -/
theorem account_extract_balance_tail_spec_within
    (listBase outPtr raVal s0Old s1Old spF x1Val x9Val t0Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hdvalid : ∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * (Nat.toBytesBE a.balance.toNat).length + 29)
      (extractBalanceBase + 68) (raVal &&& ~~~1) accountExtractBalanceFullCode
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64
          ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        (.x1 ↦ᵣ x1Val) ** (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion listBase (encodeAccount a) ** memOwnU256 outPtr **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old)) **
        (.x5 ↦ᵣ t0Old))
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ (spF + 32)) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion listBase (encodeAccount a) **
        memOwn spF ** memOwn (spF + 8) ** memOwn (spF + 16)) := by
  set encN := (encodeBytes (Nat.toBytesBE a.nonce)).length with hencN
  set encB := (encodeBytes (Nat.toBytesBE a.balance.toNat)).length with hencB
  set cB := (Nat.toBytesBE a.balance.toNat).length with hcB
  -- `cB ≤ (2 + encN) + encB`, so the wrap-free pointer subtraction below is exact.
  have hcb_le : cB ≤ (2 + encN) + encB := by
    obtain ⟨pre, _, hplen⟩ := encodeBytes_toBytesBE_split a.balance.toNat (by
      have := account_balance_field_len_le_32 a
      omega)
    omega
  set advanced := listBase + BitVec.ofNat 64 ((2 + encN) + encB) with hadv
  set cLenW : Word := BitVec.ofNat 64 cB with hcLenW
  set contentPtr := listBase + BitVec.ofNat 64 (((2 + encN) + encB) - cB) with hcp
  have hsub_eq : advanced - cLenW = contentPtr := by
    rw [hadv, hcLenW, hcp]
    have h1 : ((2 + encN) + encB) = (((2 + encN) + encB) - cB) + cB := by omega
    rw [h1]
    bv_omega
  -- Glue block idx 17..20 (`+68 → +84`): SUB x5 x10 x12 ; MV x10 x5 ; MV x11 x12 ;
  -- MV x12 x8.
  have hsub := sub_spec_gen_within .x5 .x10 .x12 advanced cLenW t0Old
    (extractBalanceBase + 68) (by decide)
  rw [hsub_eq] at hsub
  have hmv10 := mv_spec_gen_within .x10 .x5 contentPtr advanced (extractBalanceBase + 72)
    (by decide)
  have hmv11 := mv_spec_gen_within .x11 .x12 cLenW (0 : Word) (extractBalanceBase + 76)
    (by decide)
  have hmv12 := mv_spec_gen_within .x12 .x8 outPtr cLenW (extractBalanceBase + 80)
    (by decide)
  have hGlue : cpsTripleWithin 4 (extractBalanceBase + 68) (extractBalanceBase + 84)
      accountExtractBalanceCode
      ((.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ cLenW) ** (.x5 ↦ᵣ t0Old) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ outPtr))
      ((.x10 ↦ᵣ contentPtr) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ contentPtr) **
        (.x11 ↦ᵣ cLenW) ** (.x8 ↦ᵣ outPtr)) := by
    runBlock hsub hmv10 hmv11 hmv12
  have hGlue' := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ x1Val) ** (.x2 ↦ᵣ spF) ** (.x9 ↦ᵣ x9Val) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase (encodeAccount a) ** memOwnU256 outPtr **
      (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old))
    (by pcFree) (cpsTripleWithin_extend_code aeb_sub hGlue)
  -- Call `rlp_content_to_u256_be` (idx 21, `+84 → +88`).
  have hoffset : (extractBalanceBase + 84) + signExtend21
      (Codegen.jalOff Codegen.GuestAddrs.rlp_content_to_u256_be
        (Codegen.GuestAddrs.account_extract_balance + 84)) = contentU256Base := by decide
  have halign : (extractBalanceBase + 84 + 4) &&& ~~~(1 : Word) =
      extractBalanceBase + 84 + 4 := by decide
  have hdisj : (CodeReq.singleton (extractBalanceBase + 84)
      (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_content_to_u256_be
        (Codegen.GuestAddrs.account_extract_balance + 84)))).Disjoint
      (rlp_content_to_u256_be_code contentU256Base) :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len contentU256Base rlp_content_to_u256_be_prog 26 _
        rlp_content_to_u256_be_prog_length
        (fun k hk => by unfold extractBalanceBase contentU256Base Codegen.GuestAddrs.account_extract_balance Codegen.GuestAddrs.rlp_content_to_u256_be; bv_omega))
  have hcallee_raw := account_rlp_content_to_u256_be_balance_own_spec_within
    contentU256Base listBase outPtr (extractBalanceBase + 84 + 4) contentPtr a hnonce
    hsalign hoalign hover hoover hvalid hdvalid
  rw [← hencN, ← hencB, ← hcB, ← hcp, ← hcLenW] at hcallee_raw
  have hcallee_framed := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) ** regOwn .x30 ** regOwn .x31 **
      (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old))
    (by pcFree) hcallee_raw
  have hPrest : (((.x10 ↦ᵣ contentPtr) ** (.x11 ↦ᵣ cLenW) ** (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ contentPtr) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase (encodeAccount a) ** memOwnU256 outPtr **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29) **
      ((.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) ** regOwn .x30 ** regOwn .x31 **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old))).pcFree := by
    pcFree
  have hcall := WP.cpsCallWithin
    (offset := Codegen.jalOff Codegen.GuestAddrs.rlp_content_to_u256_be
      (Codegen.GuestAddrs.account_extract_balance + 84))
    (vOld := x1Val) hoffset halign hPrest hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hcallee_framed)
  have hmono21 : ∀ a' i,
      ((CodeReq.singleton (extractBalanceBase + 84)
        (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_content_to_u256_be
          (Codegen.GuestAddrs.account_extract_balance + 84)))).union
        (rlp_content_to_u256_be_code contentU256Base)) a' = some i →
      accountExtractBalanceFullCode a' = some i :=
    CodeReq.union_split_mono
      (fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 21
          (extractBalanceBase + 84) (by decide) (by decide) (by decide)) a' i h))
      aeb_cu256_sub
  have hCall := cpsTripleWithin_extend_code hmono21 hcall
  rw [show (extractBalanceBase + 84 + 4 : Word) = extractBalanceBase + 88 from by decide]
    at hCall
  -- BNE x10 x0 (idx 22, `+88 → +92`): not taken since `a0 = 0`.
  have hbne := bne_spec_gen_within .x10 .x0 (12 : BitVec 13) (0 : Word) (0 : Word)
    (extractBalanceBase + 88)
  rw [show (extractBalanceBase + 88) + signExtend13 (12 : BitVec 13)
        = extractBalanceBase + 100 from by decide,
      show (extractBalanceBase + 88 : Word) + 4 = extractBalanceBase + 92 from by decide]
    at hbne
  have hmono22 : ∀ a' i, CodeReq.singleton (extractBalanceBase + 88)
      (.BNE .x10 .x0 (12 : BitVec 13)) a' = some i →
      accountExtractBalanceFullCode a' = some i :=
    fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 22
        (extractBalanceBase + 88) (by decide) (by decide) (by decide)) a' i h)
  have hBne := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono22 (cpsBranchWithin_frameR
      (bytesRegion outPtr (word256Bytes32 a.balance) ** (.x11 ↦ᵣ cLenW) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x1 ↦ᵣ (extractBalanceBase + 88)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) ** regOwn .x30 ** regOwn .x31 **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old))
      (by pcFree) hbne))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- LI x10 0 (idx 23, `+92 → +96`).
  have hli := li_spec_gen_within .x10 (0 : Word) (0 : Word) (extractBalanceBase + 92)
    (by decide)
  have hmono23 : ∀ a' i, CodeReq.singleton (extractBalanceBase + 92)
      (.LI .x10 (0 : Word)) a' = some i → accountExtractBalanceFullCode a' = some i :=
    fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 23
        (extractBalanceBase + 92) (by decide) (by decide) (by decide)) a' i h)
  have hLi := cpsTripleWithin_frameR
    (bytesRegion outPtr (word256Bytes32 a.balance) ** (.x11 ↦ᵣ cLenW) ** (.x12 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x1 ↦ᵣ (extractBalanceBase + 88)) ** bytesRegion listBase (encodeAccount a) **
      (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) ** regOwn .x30 ** regOwn .x31 **
      (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) (cpsTripleWithin_extend_code hmono23 hli)
  rw [show (extractBalanceBase + 92 + 4 : Word) = extractBalanceBase + 96 from by decide]
    at hLi
  -- JAL x0 24 (idx 24, `+96 → +120`): skip the failure arm.
  have hjal := jal_x0_spec_gen_within (24 : BitVec 21) (extractBalanceBase + 96)
  rw [show (extractBalanceBase + 96) + signExtend21 (24 : BitVec 21)
        = extractBalanceBase + 120 from by decide] at hjal
  have hmono24 : ∀ a' i, CodeReq.singleton (extractBalanceBase + 96)
      (.JAL .x0 (24 : BitVec 21)) a' = some i → accountExtractBalanceFullCode a' = some i :=
    fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 24
        (extractBalanceBase + 96) (by decide) (by decide) (by decide)) a' i h)
  have hJal : cpsTripleWithin 1 (extractBalanceBase + 96) (extractBalanceBase + 120)
      accountExtractBalanceFullCode
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance) **
        (.x11 ↦ᵣ cLenW) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x1 ↦ᵣ (extractBalanceBase + 88)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) ** regOwn .x30 ** regOwn .x31 **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance) **
        (.x11 ↦ᵣ cLenW) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x1 ↦ᵣ (extractBalanceBase + 88)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) ** regOwn .x30 ** regOwn .x31 **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old) **
        (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (cpsTripleWithin_frameR
        ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance) **
          (.x11 ↦ᵣ cLenW) ** (.x12 ↦ᵣ outPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x1 ↦ᵣ (extractBalanceBase + 88)) ** bytesRegion listBase (encodeAccount a) **
          (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) ** regOwn .x30 ** regOwn .x31 **
          (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old) **
          (.x0 ↦ᵣ (0 : Word)))
        (by pcFree) (cpsTripleWithin_extend_code hmono24 hjal))
  -- Restore block idx 30..34 (`+120 → ra`): LD ra ; LD s0 ; LD s1 ; ADDI sp ; JALR.
  have hld1 := ld_spec_gen_within .x1 .x2 spF (extractBalanceBase + 88) raVal
    (0 : BitVec 12) (extractBalanceBase + 120) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show spF + (0 : Word) = spF from by bv_omega] at hld1
  have hld8 := ld_spec_gen_within .x8 .x2 spF outPtr s0Old
    (8 : BitVec 12) (extractBalanceBase + 124) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hld8
  have hld9 := ld_spec_gen_within .x9 .x2 spF x9Val s1Old
    (16 : BitVec 12) (extractBalanceBase + 128) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hld9
  have haddi := addi_spec_gen_same_within .x2 spF (32 : BitVec 12)
    (extractBalanceBase + 132) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at haddi
  have hret := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (extractBalanceBase + 136)
  simp only [signExtend12_0] at hret
  rw [show (raVal + 0 : Word) = raVal from by bv_omega] at hret
  have hRestore : cpsTripleWithin 5 (extractBalanceBase + 120) (raVal &&& ~~~1)
      accountExtractBalanceCode
      ((.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ (extractBalanceBase + 88)) ** (.x8 ↦ᵣ outPtr) **
        (.x9 ↦ᵣ x9Val) ** (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old))
      ((.x2 ↦ᵣ (spF + 32)) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old)) := by
    runBlock hld1 hld8 hld9 haddi hret
  have hRestore' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance) **
      (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion listBase (encodeAccount a) **
      regOwn .x11 ** regOwn .x12)
    (by pcFree) (cpsTripleWithin_extend_code aeb_sub hRestore)
  -- Compose glue ⨾ call ⨾ BNE ⨾ LI ⨾ JAL ⨾ restore.
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hGlue' hCall; intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hBne; intro h hp; xperm_hyp hp
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hLi
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s3 hJal; intro h hp; xperm_hyp hp
  have s5 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s4 hRestore'
    intro h hp
    -- Weaken the now-owned `a1`/`a2` (`x11`/`x12`) pins into `regOwn` before
    -- handing the state to the restore block's frame.
    have hp2 := sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x)))) h hp
    xperm_hyp hp2
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s5)
  -- Release the stack-frame save cells back as raw ownership.
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))))) h hp
  xperm_hyp hp2

/-- `account_extract_balance_tail_spec_within` with the `x5` pin released to
    `regOwn` — the form the second `rlp_walk_next`'s `regOwn` post feeds. -/
theorem account_extract_balance_tail_own_spec_within
    (listBase outPtr raVal s0Old s1Old spF x1Val x9Val : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hdvalid : ∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * (Nat.toBytesBE a.balance.toNat).length + 29)
      (extractBalanceBase + 68) (raVal &&& ~~~1) accountExtractBalanceFullCode
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64
          ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        (.x1 ↦ᵣ x1Val) ** (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ x9Val) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion listBase (encodeAccount a) ** memOwnU256 outPtr **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** ((spF + 16) ↦ₘ s1Old)) **
        regOwn .x5)
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ (spF + 32)) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion listBase (encodeAccount a) **
        memOwn spF ** memOwn (spF + 8) ** memOwn (spF + 16)) :=
  ownify1 (fun t0Old => account_extract_balance_tail_spec_within listBase outPtr raVal
    s0Old s1Old spF x1Val x9Val t0Old a hnonce hsalign hoalign hover hoover hvalid hdvalid)

/-! ## `account_extract_balance`: the top-level triple -/

set_option maxRecDepth 8000 in
/-- **Top-level success triple for `account_extract_balance`** (35-instruction
    body at its fixed guest address `GuestAddrs.account_extract_balance`,
    composed with `rlp_walk_init`, two `rlp_walk_next` steps and
    `rlp_content_to_u256_be` at theirs).

    From the accessor entry with `a0` = pointer to `encodeAccount a`, `a1` =
    its byte length, `a2` = a 32-byte output pointer, a stack pointer with
    three owned spill slots below it, and return address `raVal`, the body
    deterministically returns to `raVal &&& ~~~1` with `a0 = 0` (success),
    the output cell holding the 32-byte big-endian balance
    (`word256Bytes32 a.balance`), callee-saved `s0`/`s1`/`sp` and the input
    region preserved, and the stack slots returned to the caller. -/
theorem account_extract_balance_spec_within
    (listBase outPtr spVal raVal s0Old s1Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hdvalid : ∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 340 extractBalanceBase (raVal &&& ~~~1) accountExtractBalanceFullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (BitVec.ofNat 64 (encodeAccount a).length)) **
        (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ spVal) ** (.x8 ↦ᵣ s0Old) **
        (.x9 ↦ᵣ s1Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encodeAccount a) **
        memOwnU256 outPtr **
        memOwn (spVal - 32) ** memOwn (spVal - 24) ** memOwn (spVal - 16))
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ spVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion listBase (encodeAccount a) **
        memOwn (spVal - 32) ** memOwn (spVal - 24) ** memOwn (spVal - 16)) := by
  have hlen70 : 70 ≤ (encodeAccount a).length := by
    rw [encodeAccount_length_eq a hnonce]
    have := accountPayload_length_ge a
    omega
  have hvalid0 : isValidByteAccess listBase = true := by
    have h := hvalid 0 (by omega)
    rwa [show listBase + BitVec.ofNat 64 0 = listBase from by bv_omega] at h
  have hvalid1 : isValidByteAccess (listBase + 1) = true := by
    have h := hvalid 1 (by omega)
    rwa [show listBase + BitVec.ofNat 64 1 = listBase + 1 from by bv_omega] at h
  -- Prefix block idx 0..8 (`B → B+36`): allocate the stack frame, save
  -- `ra`/`s0`/`s1`, set `s0 := outPtr`, zero the 32-byte output cell.
  have haddisp := addi_spec_gen_same_within .x2 spVal (-32 : BitVec 12) extractBalanceBase
    (by decide)
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
      show spVal + (-32 : Word) = spVal - 32 from by bv_omega] at haddisp
  have hsd1 := sd_spec_gen_own_within .x2 .x1 (spVal - 32) raVal (0 : BitVec 12)
    (extractBalanceBase + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (spVal - 32) + (0 : Word) = spVal - 32 from by bv_omega] at hsd1
  have hsd2 := sd_spec_gen_own_within .x2 .x8 (spVal - 32) s0Old (8 : BitVec 12)
    (extractBalanceBase + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show (spVal - 32) + (8 : Word) = spVal - 24 from by bv_omega] at hsd2
  have hsd3 := sd_spec_gen_own_within .x2 .x9 (spVal - 32) s1Old (16 : BitVec 12)
    (extractBalanceBase + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
      show (spVal - 32) + (16 : Word) = spVal - 16 from by bv_omega] at hsd3
  have hmv8 := mv_spec_gen_within .x8 .x12 outPtr s0Old (extractBalanceBase + 16) (by decide)
  have hsdo0 := sd_spec_gen_own_within .x8 .x0 outPtr (0 : Word) (0 : BitVec 12)
    (extractBalanceBase + 20)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show outPtr + (0 : Word) = outPtr from by bv_omega] at hsdo0
  have hsdo1 := sd_spec_gen_own_within .x8 .x0 outPtr (0 : Word) (8 : BitVec 12)
    (extractBalanceBase + 24)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hsdo1
  have hsdo2 := sd_spec_gen_own_within .x8 .x0 outPtr (0 : Word) (16 : BitVec 12)
    (extractBalanceBase + 28)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hsdo2
  have hsdo3 := sd_spec_gen_own_within .x8 .x0 outPtr (0 : Word) (24 : BitVec 12)
    (extractBalanceBase + 32)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at hsdo3
  have hPrefix : cpsTripleWithin 9 extractBalanceBase (extractBalanceBase + 36)
      accountExtractBalanceCode
      ((.x2 ↦ᵣ spVal) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (spVal - 32) ** memOwn (spVal - 24) ** memOwn (spVal - 16) **
        memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) ** memOwn (outPtr + 24))
      ((.x2 ↦ᵣ (spVal - 32)) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) **
        (.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old) **
        ((outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
          ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word)))) := by
    runBlock haddisp hsd1 hsd2 hsd3 hmv8 hsdo0 hsdo1 hsdo2 hsdo3
  -- Repackage the zeroed output cell as `memOwnU256` for the callee chain.
  have hPrefix2 : cpsTripleWithin 9 extractBalanceBase (extractBalanceBase + 36)
      accountExtractBalanceCode
      ((.x2 ↦ᵣ spVal) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (spVal - 32) ** memOwn (spVal - 24) ** memOwn (spVal - 16) **
        memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) ** memOwn (outPtr + 24))
      ((.x2 ↦ᵣ (spVal - 32)) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) **
        (.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old) **
        memOwnU256 outPtr) :=
    cpsTripleWithin_weaken (fun h hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (fun h' hp' => by
              simp only [memOwnU256]
              exact sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)) h' hp'))))))))) h hp)
      hPrefix
  have hPrefix' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (BitVec.ofNat 64 (encodeAccount a).length)) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      bytesRegion listBase (encodeAccount a))
    (by pcFree) (cpsTripleWithin_extend_code aeb_sub hPrefix2)
  -- Call `rlp_walk_init` (idx 9, `+36 → +40`).
  have hoffsetWI : (extractBalanceBase + 36) + signExtend21
      (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_init
        (Codegen.GuestAddrs.account_extract_balance + 36)) = walkInitBase := by decide
  have halignWI : (extractBalanceBase + 36 + 4) &&& ~~~(1 : Word) =
      extractBalanceBase + 36 + 4 := by decide
  have hdisjWI : (CodeReq.singleton (extractBalanceBase + 36)
      (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_init
        (Codegen.GuestAddrs.account_extract_balance + 36)))).Disjoint
      (rlp_walk_init_code walkInitBase) :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len walkInitBase rlp_walk_init_prog 53 _
        rlp_walk_init_prog_length
        (fun k hk => by unfold extractBalanceBase walkInitBase Codegen.GuestAddrs.account_extract_balance Codegen.GuestAddrs.rlp_walk_init; bv_omega))
  have hWIcallee := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) ** memOwnU256 outPtr **
      ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old))
    (by pcFree)
    (account_rlp_walk_init_spec_within walkInitBase listBase (extractBalanceBase + 36 + 4)
      outPtr t0Old t1Old t2Old t3Old t4Old t5Old t6Old a hnonce hsalign hover hvalid0 hvalid1)
  have hPrestWI : (((.x10 ↦ᵣ listBase) **
      (.x11 ↦ᵣ (BitVec.ofNat 64 (encodeAccount a).length)) ** (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase (encodeAccount a)) **
      ((.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) ** memOwnU256 outPtr **
        ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) **
        ((spVal - 16) ↦ₘ s1Old))).pcFree := by pcFree
  have hcallWI := WP.cpsCallWithin
    (offset := Codegen.jalOff Codegen.GuestAddrs.rlp_walk_init
      (Codegen.GuestAddrs.account_extract_balance + 36))
    (vOld := raVal) hoffsetWI halignWI hPrestWI hdisjWI
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hWIcallee)
  have hmonoWI : ∀ a' i,
      ((CodeReq.singleton (extractBalanceBase + 36)
        (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_init
          (Codegen.GuestAddrs.account_extract_balance + 36)))).union
        (rlp_walk_init_code walkInitBase)) a' = some i →
      accountExtractBalanceFullCode a' = some i :=
    CodeReq.union_split_mono
      (fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 9
          (extractBalanceBase + 36) (by decide) (by decide) (by decide)) a' i h))
      aeb_wi_sub
  have hCallWI := cpsTripleWithin_extend_code hmonoWI hcallWI
  rw [show (extractBalanceBase + 36 + 4 : Word) = extractBalanceBase + 40 from by decide]
    at hCallWI
  -- BNE x12 x0 (idx 10, `+40 → +44`): not taken (walk_init status 0).
  have hbne10 := bne_spec_gen_within .x12 .x0 (60 : BitVec 13) (0 : Word) (0 : Word)
    (extractBalanceBase + 40)
  rw [show (extractBalanceBase + 40) + signExtend13 (60 : BitVec 13)
        = extractBalanceBase + 100 from by decide,
      show (extractBalanceBase + 40 : Word) + 4 = extractBalanceBase + 44 from by decide]
    at hbne10
  have hmono10 : ∀ a' i, CodeReq.singleton (extractBalanceBase + 40)
      (.BNE .x12 .x0 (60 : BitVec 13)) a' = some i →
      accountExtractBalanceFullCode a' = some i :=
    fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 10
        (extractBalanceBase + 40) (by decide) (by decide) (by decide)) a' i h)
  have hBne10 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono10 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (listBase + 2)) **
        (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (extractBalanceBase + 40)) **
        bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) ** memOwnU256 outPtr **
        ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old))
      (by pcFree) hbne10))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- MV x9 x11 (idx 11, `+44 → +48`): save `end` into `s1`.
  have hmv9 := mv_spec_gen_within .x9 .x11
    (listBase + BitVec.ofNat 64 (encodeAccount a).length) s1Old (extractBalanceBase + 44)
    (by decide)
  have hmono11 : ∀ a' i, CodeReq.singleton (extractBalanceBase + 44)
      (.MV .x9 .x11) a' = some i → accountExtractBalanceFullCode a' = some i :=
    fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 11
        (extractBalanceBase + 44) (by decide) (by decide) (by decide)) a' i h)
  have hMv9 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (listBase + 2)) ** (.x12 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (extractBalanceBase + 40)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encodeAccount a) **
      (.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) ** memOwnU256 outPtr **
      ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old))
    (by pcFree) (cpsTripleWithin_extend_code hmono11 hmv9)
  rw [show (extractBalanceBase + 44 + 4 : Word) = extractBalanceBase + 48 from by decide]
    at hMv9
  -- Call `rlp_walk_next` for field 0 (idx 12, `+48 → +52`).
  have hoffsetW0 : (extractBalanceBase + 48) + signExtend21
      (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
        (Codegen.GuestAddrs.account_extract_balance + 48)) = walkNextBase := by decide
  have halignW0 : (extractBalanceBase + 48 + 4) &&& ~~~(1 : Word) =
      extractBalanceBase + 48 + 4 := by decide
  have hdisjW0 : (CodeReq.singleton (extractBalanceBase + 48)
      (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
        (Codegen.GuestAddrs.account_extract_balance + 48)))).Disjoint
      (rlp_walk_next_code walkNextBase) :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len walkNextBase rlp_walk_next_prog 103 _
        rlp_walk_next_prog_length
        (fun k hk => by unfold extractBalanceBase walkNextBase Codegen.GuestAddrs.account_extract_balance Codegen.GuestAddrs.rlp_walk_next; bv_omega))
  have hW0callee := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) **
      (.x9 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
      regOwn .x30 ** regOwn .x31 ** memOwnU256 outPtr **
      ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old))
    (by pcFree)
    (account_rlp_walk_next_field0_own_spec_within walkNextBase listBase
      (extractBalanceBase + 48 + 4) (0 : Word) a hnonce hsalign hover hvalid)
  have hPrestW0 : ((((.x10 ↦ᵣ (listBase + 2)) **
      (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase (encodeAccount a)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29) **
      ((.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) **
        (.x9 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        regOwn .x30 ** regOwn .x31 ** memOwnU256 outPtr **
        ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) **
        ((spVal - 16) ↦ₘ s1Old))).pcFree := by pcFree
  have hcallW0 := WP.cpsCallWithin
    (offset := Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
      (Codegen.GuestAddrs.account_extract_balance + 48))
    (vOld := extractBalanceBase + 40) hoffsetW0 halignW0 hPrestW0 hdisjW0
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hW0callee)
  have hmonoW0 : ∀ a' i,
      ((CodeReq.singleton (extractBalanceBase + 48)
        (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
          (Codegen.GuestAddrs.account_extract_balance + 48)))).union
        (rlp_walk_next_code walkNextBase)) a' = some i →
      accountExtractBalanceFullCode a' = some i :=
    CodeReq.union_split_mono
      (fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 12
          (extractBalanceBase + 48) (by decide) (by decide) (by decide)) a' i h))
      aeb_wn_sub
  have hCallW0 := cpsTripleWithin_extend_code hmonoW0 hcallW0
  rw [show (extractBalanceBase + 48 + 4 : Word) = extractBalanceBase + 52 from by decide]
    at hCallW0
  -- BNE x11 x0 (idx 13, `+52 → +56`): not taken (walk_next status 0).
  have hbne13 := bne_spec_gen_within .x11 .x0 (48 : BitVec 13) (0 : Word) (0 : Word)
    (extractBalanceBase + 52)
  rw [show (extractBalanceBase + 52) + signExtend13 (48 : BitVec 13)
        = extractBalanceBase + 100 from by decide,
      show (extractBalanceBase + 52 : Word) + 4 = extractBalanceBase + 56 from by decide]
    at hbne13
  have hmono13 : ∀ a' i, CodeReq.singleton (extractBalanceBase + 52)
      (.BNE .x11 .x0 (48 : BitVec 13)) a' = some i →
      accountExtractBalanceFullCode a' = some i :=
    fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 13
        (extractBalanceBase + 52) (by decide) (by decide) (by decide)) a' i h)
  have hBne13 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono13 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x1 ↦ᵣ (extractBalanceBase + 52)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) **
        (.x9 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        regOwn .x30 ** regOwn .x31 ** memOwnU256 outPtr **
        ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old))
      (by pcFree) hbne13))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- MV x11 x9 (idx 14, `+56 → +60`): restore `end` into `a1`.
  have hmv11b := mv_spec_gen_within .x11 .x9
    (listBase + BitVec.ofNat 64 (encodeAccount a).length) (0 : Word)
    (extractBalanceBase + 56) (by decide)
  have hmono14 : ∀ a' i, CodeReq.singleton (extractBalanceBase + 56)
      (.MV .x11 .x9) a' = some i → accountExtractBalanceFullCode a' = some i :=
    fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 14
        (extractBalanceBase + 56) (by decide) (by decide) (by decide)) a' i h)
  have hMv11 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (listBase +
        BitVec.ofNat 64 (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x1 ↦ᵣ (extractBalanceBase + 52)) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase (encodeAccount a) **
      (.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) ** regOwn .x30 ** regOwn .x31 **
      memOwnU256 outPtr **
      ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old))
    (by pcFree) (cpsTripleWithin_extend_code hmono14 hmv11b)
  rw [show (extractBalanceBase + 56 + 4 : Word) = extractBalanceBase + 60 from by decide]
    at hMv11
  -- Call `rlp_walk_next` for field 1 (idx 15, `+60 → +64`).
  have hoffsetW1 : (extractBalanceBase + 60) + signExtend21
      (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
        (Codegen.GuestAddrs.account_extract_balance + 60)) = walkNextBase := by decide
  have halignW1 : (extractBalanceBase + 60 + 4) &&& ~~~(1 : Word) =
      extractBalanceBase + 60 + 4 := by decide
  have hdisjW1 : (CodeReq.singleton (extractBalanceBase + 60)
      (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
        (Codegen.GuestAddrs.account_extract_balance + 60)))).Disjoint
      (rlp_walk_next_code walkNextBase) :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len walkNextBase rlp_walk_next_prog 103 _
        rlp_walk_next_prog_length
        (fun k hk => by unfold extractBalanceBase walkNextBase Codegen.GuestAddrs.account_extract_balance Codegen.GuestAddrs.rlp_walk_next; bv_omega))
  have hW1callee := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) **
      (.x9 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
      regOwn .x30 ** regOwn .x31 ** memOwnU256 outPtr **
      ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old))
    (by pcFree)
    (account_rlp_walk_next_field1_own_spec_within walkNextBase listBase
      (extractBalanceBase + 60 + 4) (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length) a
      hnonce hsalign hover hvalid)
  have hPrestW1 : ((((.x10 ↦ᵣ (listBase +
      BitVec.ofNat 64 (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
      (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase (encodeAccount a)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29) **
      ((.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) **
        (.x9 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        regOwn .x30 ** regOwn .x31 ** memOwnU256 outPtr **
        ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) **
        ((spVal - 16) ↦ₘ s1Old))).pcFree := by pcFree
  have hcallW1 := WP.cpsCallWithin
    (offset := Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
      (Codegen.GuestAddrs.account_extract_balance + 60))
    (vOld := extractBalanceBase + 52) hoffsetW1 halignW1 hPrestW1 hdisjW1
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hW1callee)
  have hmonoW1 : ∀ a' i,
      ((CodeReq.singleton (extractBalanceBase + 60)
        (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
          (Codegen.GuestAddrs.account_extract_balance + 60)))).union
        (rlp_walk_next_code walkNextBase)) a' = some i →
      accountExtractBalanceFullCode a' = some i :=
    CodeReq.union_split_mono
      (fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 15
          (extractBalanceBase + 60) (by decide) (by decide) (by decide)) a' i h))
      aeb_wn_sub
  have hCallW1 := cpsTripleWithin_extend_code hmonoW1 hcallW1
  rw [show (extractBalanceBase + 60 + 4 : Word) = extractBalanceBase + 64 from by decide]
    at hCallW1
  -- BNE x11 x0 (idx 16, `+64 → +68`): not taken (walk_next status 0).
  have hbne16 := bne_spec_gen_within .x11 .x0 (36 : BitVec 13) (0 : Word) (0 : Word)
    (extractBalanceBase + 64)
  rw [show (extractBalanceBase + 64) + signExtend13 (36 : BitVec 13)
        = extractBalanceBase + 100 from by decide,
      show (extractBalanceBase + 64 : Word) + 4 = extractBalanceBase + 68 from by decide]
    at hbne16
  have hmono16 : ∀ a' i, CodeReq.singleton (extractBalanceBase + 64)
      (.BNE .x11 .x0 (36 : BitVec 13)) a' = some i →
      accountExtractBalanceFullCode a' = some i :=
    fun a' i h => aeb_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractBalanceBase Codegen.accountExtractBalance_prog 16
        (extractBalanceBase + 64) (by decide) (by decide) (by decide)) a' i h)
  have hBne16 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono16 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length))) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x1 ↦ᵣ (extractBalanceBase + 64)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ (spVal - 32)) ** (.x8 ↦ᵣ outPtr) **
        (.x9 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        regOwn .x30 ** regOwn .x31 ** memOwnU256 outPtr **
        ((spVal - 32) ↦ₘ raVal) ** ((spVal - 24) ↦ₘ s0Old) ** ((spVal - 16) ↦ₘ s1Old))
      (by pcFree) hbne16))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- The verified tail from `+68`.
  have hTail := account_extract_balance_tail_own_spec_within listBase outPtr raVal s0Old
    s1Old (spVal - 32) (extractBalanceBase + 64)
    (listBase + BitVec.ofNat 64 (encodeAccount a).length) a hnonce hsalign hoalign hover
    hoover hvalid hdvalid
  rw [show ((spVal - 32 : Word) + 8) = spVal - 24 from by bv_omega,
      show ((spVal - 32 : Word) + 16) = spVal - 16 from by bv_omega,
      show ((spVal - 32 : Word) + 32) = spVal from by bv_omega] at hTail
  -- Compose the whole chain.
  have t1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hPrefix' hCallWI; intro h hp; xperm_hyp hp
  have t2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t1 hBne10; intro h hp; xperm_hyp hp
  have t3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t2 hMv9
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have t4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t3 hCallW0; intro h hp; xperm_hyp hp
  have t5 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t4 hBne13; intro h hp; xperm_hyp hp
  have t6 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t5 hMv11
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have t7 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t6 hCallW1; intro h hp; xperm_hyp hp
  have t8 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t7 hBne16; intro h hp; xperm_hyp hp
  have t9 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t8 hTail
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have hcb32 : (Nat.toBytesBE a.balance.toNat).length ≤ 32 :=
    account_balance_field_len_le_32 a
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by simp only [memOwnU256] at hp ⊢; xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) t9)


end EvmAsm.Codegen
