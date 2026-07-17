/-
  EvmAsm.Codegen.Programs.TeerBodyAssumptions

  PASS 3 of the `tx_eip7702_existing_authority_refund` Fn.Spec development.

  The teer body `jal`s into seven LINKED callee Programs whose behavioural
  `cpsTripleWithin` specs are not yet proven on this branch (only the
  image-subsumption `_mono` lemmas in `TeerExistingAuthorityRefundSpec` exist).
  This module supplies each as an ASSUMED sub-contract — a `structure … (cr :
  CodeReq)` carrying the callee `entry : Word`, any pure result `*Model`
  fields, and a single `flat : cpsTripleWithin …` field — mirroring the four
  existing string-only `*Assumed` contracts.  NO axioms / `sorry`; the
  contracts are HYPOTHESES a future converted-callee Fn.Spec discharges
  drop-in via `cpsTripleWithin_extend_code`.

  Faithfulness: each `flat`'s ABI (input/output/scratch register + memory
  footprint) mirrors the callee's calling-convention doc-comment and concrete
  instruction sequence, and its result is expressed with the very models the
  conformance analysis relies on — the concrete `teerTxTypeDispatch`
  classification, the `FinalsOut`/`FinalsDerivation` EIP-7928 AccountChanges
  model (`BalAccountNonstorageFinalsSpec`), and abstract `*Model` fields for
  the address-recovery / BAL-scan / pre-state-lookup routines (pinned by a
  later conversion, exactly as `BalAccountNonceBeforeIndexAssumed.nonceModel`).

  The seven new contracts plus the four existing `TeerAssumedCallees` are
  bundled into `TeerBodyAssumptions`, the full 11-hypothesis footing under
  which the teer body is proved.  This discharges grok's `TeerAssumed`
  conditionally (net conditionality reduction: 11 spec-aligned callee
  contracts instead of an opaque whole-program assumption).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerBodyDecode
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsSpec
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64
open EvmAsm.Codegen.BalAccountNonstorageFinalsSpec (FinalsOut FinalsDerivation)

/-! ## Result models for the assumed callees

    A boolean `has_*` flag stored as its `Word` image (the guest stores 0/1). -/
def boolWord (b : Bool) : Word := if b then 1 else 0

/-- Concrete EIP-2718 type dispatch performed by `tx_type_dispatch`
    (`(status, tx_type, inner_offset)`), verbatim from `txTypeDispatch_prog`:
    empty input ⇒ status 1; leading byte ≥ 0xc0 ⇒ legacy (type 0, off 0);
    0x01..0x04 ⇒ typed (off 1); anything else ⇒ status 1. -/
def teerTxTypeDispatch (txBytes : List (BitVec 8)) : Word × Word × Word :=
  match txBytes with
  | [] => (1, 0, 0)
  | b :: _ =>
    if 192 ≤ b.toNat then (0, 0, 0)
    else if b = (1 : BitVec 8) then (0, 1, 1)
    else if b = (2 : BitVec 8) then (0, 2, 1)
    else if b = (3 : BitVec 8) then (0, 3, 1)
    else if b = (4 : BitVec 8) then (0, 4, 1)
    else (1, 0, 0)

/-! ## Over-approximate per-callee step budgets

    The `nSteps` fuel for each assumed triple; a converted callee proves the
    exact count `≤` these (via `cpsTripleWithin_mono_nSteps`). -/
def nTxTypeDispatchSteps : Nat := 256
def nRlpListCountItemsSteps : Nat := 262144
def nRecoverAddressSteps : Nat := 262144
def nBalFindAccountSteps : Nat := 262144
def nBalFinalsSteps : Nat := 262144
def nCodeAtHeaderSteps : Nat := 1048576
def nAccountAtHeaderSteps : Nat := 1048576

/-! ## 1. `tx_type_dispatch`

    Leaf routine (no frame).  ABI: a0 = tx-bytes ptr, a1 = tx-bytes length,
    a2 = &type out cell, a3 = &inner-offset out cell; returns a0 = status and
    writes the two out cells.  Scratch: `t0 (x5)`, `t1 (x6)`.  The result is
    the concrete `teerTxTypeDispatch` classification of the leading byte. -/
structure TxTypeDispatchAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `tx_type_dispatch` Program. -/
  entry : Word
  /-- Type-dispatch contract: publishes `teerTxTypeDispatch` into a0 / the two
      out cells; `t0`/`t1` scratch. -/
  flat :
    ∀ (ret txBase txLen typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
      (txBytes : List (BitVec 8))
      (_hret : ret &&& ~~~(1 : Word) = ret)
      (_hlen : txLen = BitVec.ofNat 64 txBytes.length)
      (_halign : txBase.toNat % 8 = 0)
      (_hover : txBase.toNat + txBytes.length < 2 ^ 64)
      (_hvalid : ∀ k, k < txBytes.length →
        isValidByteAccess (txBase + BitVec.ofNat 64 k) = true),
      cpsTripleWithin nTxTypeDispatchSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLen) **
          (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes ** (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld))
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes) **
         (fun h =>
           ((.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) **
             (typePtr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
             (innerPtr ↦ₘ (teerTxTypeDispatch txBytes).2.2)) h))

/-! ## 2. `rlp_list_count_items`

    ABI: a0 = list ptr, a1 = list length, a2 = &count out cell; returns
    a0 = status (0 ok / ≠ 0 parse failure) and, on success, writes the item
    count to the out cell.  Scratch: `t0,t1,t2 (x5,x6,x7)`, `t3..t6
    (x28..x31)`.  The count is the abstract `countModel`. -/
structure RlpListCountItemsAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `rlp_list_count_items` Program. -/
  entry : Word
  /-- The item count as a pure function of the list bytes and declared length;
      `none` on a parse-shape failure. -/
  countModel : List (BitVec 8) → Nat → Option Word
  /-- Count contract mirroring `rlpListCountItems_flat_spec_within` at the
      single-primary-outcome abstraction level. -/
  flat :
    ∀ (ret listBase listLenW outPtr outOld t0Old t1Old t2Old t3Old t4Old t5Old
        t6Old : Word) (listBytes : List (BitVec 8)) (listLen : Nat)
      (_hret : ret &&& ~~~(1 : Word) = ret)
      (_hlen : listLenW = BitVec.ofNat 64 listLen)
      (_halign : listBase.toNat % 8 = 0)
      (_hbound : listLen ≤ listBytes.length)
      (_hover : listBase.toNat + listBytes.length < 2 ^ 64)
      (_hvalid : ∀ k, k < listBytes.length →
        isValidByteAccess (listBase + BitVec.ofNat 64 k) = true),
      cpsTripleWithin nRlpListCountItemsSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
          (.x12 ↦ᵣ outPtr) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes ** (outPtr ↦ₘ outOld))
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 **
          (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           -- success (a0 = 0): out cell = the modelled count
           (∃ cnt, countModel listBytes listLen = some cnt ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt)) h)) ∨
           -- parse failure (a0 ≠ 0): out cell clobbered
           (countModel listBytes listLen = none ∧
             (∃ st, (((.x10 ↦ᵣ st) ** memOwn outPtr ** ⌜st ≠ (0 : Word)⌝) h)))))

/-! ## 3. `eip7702_authorization_recover_address`

    ABI: a0 = authorization-tuple RLP ptr, a1 = tuple length, a2 = 20-byte
    authority out ptr, a3 = ≥360-byte 8-aligned scratch ptr; returns a0 =
    status (0 success / ≠ 0 one of the recovery failure codes) and, on
    success, writes the recovered 20-byte authority to `*a2`.  Callee-saved
    `s0..s5` are restored (invisible); `a4..a7`, `t0..t6` are clobbered.  The
    authority is the abstract `authorityModel` (the SpecRef `recover_authority`
    image at the byte level). -/
structure Eip7702AuthorizationRecoverAddressAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `eip7702_authorization_recover_address`. -/
  entry : Word
  /-- The recovered 20-byte authority as a pure function of the tuple bytes;
      `none` on any recovery failure (bad y-parity, r/s out of range, …). -/
  authorityModel : List (BitVec 8) → Option (List (BitVec 8))
  /-- Address-recovery contract. -/
  flat :
    ∀ (ret tupleBase tupleLen authOutBase scratchBase a4Old a5Old a6Old a7Old
        t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
      (tupleBytes authOutOld scratchIn : List (BitVec 8))
      (_hret : ret &&& ~~~(1 : Word) = ret)
      (_hout20 : authOutOld.length = 20)
      (_hscratch : 360 ≤ scratchIn.length)
      (_halign : tupleBase.toNat % 8 = 0)
      (_hsalign : scratchBase.toNat % 8 = 0),
      cpsTripleWithin nRecoverAddressSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ tupleBase) ** (.x11 ↦ᵣ tupleLen) **
          (.x12 ↦ᵣ authOutBase) ** (.x13 ↦ᵣ scratchBase) **
          (.x14 ↦ᵣ a4Old) ** (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) ** (.x17 ↦ᵣ a7Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion tupleBase tupleBytes ** bytesRegion authOutBase authOutOld **
          bytesRegion scratchBase scratchIn)
        ((regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** regOwn .x17 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion tupleBase tupleBytes **
          (fun h => ∃ sb : List (BitVec 8), bytesRegion scratchBase sb h)) **
         (fun h =>
           -- success (a0 = 0): out region holds the recovered authority
           (∃ abytes, authorityModel tupleBytes = some abytes ∧ abytes.length = 20 ∧
             (((.x10 ↦ᵣ (0 : Word)) ** bytesRegion authOutBase abytes) h)) ∨
           -- failure (a0 ≠ 0): out region clobbered
           (authorityModel tupleBytes = none ∧
             (∃ st bs, bs.length = 20 ∧
               (((.x10 ↦ᵣ st) ** bytesRegion authOutBase bs ** ⌜st ≠ (0 : Word)⌝) h)))))

/-! ## 4. `bal_find_account_by_address`

    ABI: a0 = BAL section RLP ptr, a1 = length, a2 = 20-byte target address
    ptr, a3 = &matched-ptr out cell, a4 = &matched-len out cell; returns a0 =
    status (0 found / 1 not found / 2 parse error) and, on a hit, writes the
    matched AccountChanges RLP span `(ptr, len)` to `*a3`/`*a4`.  Callee-saved
    `s0..s9` restored; `t0,t1,t3..t6` and `a0..a4` clobbered.  The match span
    is the abstract `findModel`. -/
structure BalFindAccountByAddressAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `bal_find_account_by_address`. -/
  entry : Word
  /-- The matched AccountChanges span `(rlpPtr, rlpLen)` as a pure function of
      the BAL bytes and the 20-byte target address; `none` when absent. -/
  findModel : List (BitVec 8) → List (BitVec 8) → Option (Word × Word)
  /-- Account-lookup contract. -/
  flat :
    ∀ (ret balBase balLen addrBase ptrCell lenCell ptrOld lenOld
        t0Old t1Old t3Old t4Old t5Old t6Old : Word)
      (balBytes addrBytes : List (BitVec 8))
      (_hret : ret &&& ~~~(1 : Word) = ret)
      (_haddr20 : addrBytes.length = 20)
      (_halign : balBase.toNat % 8 = 0)
      (_hover : balBase.toNat + balBytes.length < 2 ^ 64)
      (_hvalid : ∀ k, k < balBytes.length →
        isValidByteAccess (balBase + BitVec.ofNat 64 k) = true),
      cpsTripleWithin nBalFindAccountSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ balBase) ** (.x11 ↦ᵣ balLen) ** (.x12 ↦ᵣ addrBase) **
          (.x13 ↦ᵣ ptrCell) ** (.x14 ↦ᵣ lenCell) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion balBase balBytes ** bytesRegion addrBase addrBytes **
          (ptrCell ↦ₘ ptrOld) ** (lenCell ↦ₘ lenOld))
        ((regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x5 **
          regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion balBase balBytes ** bytesRegion addrBase addrBytes) **
         (fun h =>
           -- found (a0 = 0): the two out cells receive the matched span
           (∃ p l, findModel balBytes addrBytes = some (p, l) ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (ptrCell ↦ₘ p) ** (lenCell ↦ₘ l)) h)) ∨
           -- not found (a0 = 1)
           (findModel balBytes addrBytes = none ∧
             (((.x10 ↦ᵣ (1 : Word)) ** memOwn ptrCell ** memOwn lenCell) h)) ∨
           -- parse error (a0 = 2)
           (((.x10 ↦ᵣ (2 : Word)) ** memOwn ptrCell ** memOwn lenCell) h)))

/-! ## 5. `bal_account_nonstorage_finals`

    ABI: a0 = AccountChanges RLP ptr, a1 = length, a2 = ≥88-byte out block;
    returns a0 = status (0 ok / 1 parse failure).  On success the out block
    receives the FINAL balance / nonce / code fields per EIP-7928, exactly the
    `FinalsOut` result of `FinalsDerivation` (`BalAccountNonstorageFinalsSpec`).
    This is the FA-critical callee: the teer body reads `has_nonce`(+40) /
    `post_nonce`(+48) to drive the BAL nonce-advance / rollback detection. -/
structure BalAccountNonstorageFinalsAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `bal_account_nonstorage_finals`. -/
  entry : Word
  /-- Finals contract: the out block cells hold the `FinalsOut` components of
      the genuine `FinalsDerivation` of the AccountChanges window. -/
  flat :
    ∀ (ret acctBase acctLenW outBase b0 b8 b16 b24 b32 nn48 hc56 co64 cl72 hn40 hb0 : Word)
      (acctBytes : List (BitVec 8)) (acctLen : Nat)
      (_hret : ret &&& ~~~(1 : Word) = ret)
      (_hlen : acctLenW = BitVec.ofNat 64 acctLen)
      (_halign : acctBase.toNat % 8 = 0)
      (_hbound : acctLen ≤ acctBytes.length)
      (_hover : acctBase.toNat + acctBytes.length < 2 ^ 64)
      (_hvalid : ∀ k, k < acctBytes.length →
        isValidByteAccess (acctBase + BitVec.ofNat 64 k) = true),
      cpsTripleWithin nBalFinalsSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ acctBase) ** (.x11 ↦ᵣ acctLenW) ** (.x12 ↦ᵣ outBase) **
          (.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ b8) ** (.x29 ↦ᵣ b16) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion acctBase acctBytes **
          (outBase ↦ₘ hb0) ** ((outBase + 8) ↦ₘ b8) ** ((outBase + 16) ↦ₘ b16) **
          ((outBase + 24) ↦ₘ b24) ** ((outBase + 32) ↦ₘ b32) ** ((outBase + 40) ↦ₘ hn40) **
          ((outBase + 48) ↦ₘ nn48) ** ((outBase + 56) ↦ₘ hc56) ** ((outBase + 64) ↦ₘ co64) **
          ((outBase + 72) ↦ₘ cl72))
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x29 ** regOwn .x11 ** regOwn .x12 **
          (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion acctBase acctBytes) **
         (fun h =>
           -- ok (a0 = 0): out block = FinalsOut of the derivation
           (∃ out : FinalsOut, FinalsDerivation acctBytes acctBase acctLen out ∧
             (((.x10 ↦ᵣ (0 : Word)) **
               memOwn outBase ** memOwn (outBase + 8) ** memOwn (outBase + 16) **
               memOwn (outBase + 24) ** memOwn (outBase + 32) **
               ((outBase + 40) ↦ₘ boolWord out.hasNonce) ** ((outBase + 48) ↦ₘ out.nonce) **
               ((outBase + 56) ↦ₘ boolWord out.hasCode) ** ((outBase + 64) ↦ₘ out.codeOff) **
               ((outBase + 72) ↦ₘ out.codeLen)) h)) ∨
           -- parse failure (a0 = 1): out block clobbered
           (((.x10 ↦ᵣ (1 : Word)) **
             memOwn outBase ** memOwn (outBase + 8) ** memOwn (outBase + 16) **
             memOwn (outBase + 24) ** memOwn (outBase + 32) ** memOwn (outBase + 40) **
             memOwn (outBase + 48) ** memOwn (outBase + 56) ** memOwn (outBase + 64) **
             memOwn (outBase + 72)) h)))

/-! ## 6. `code_at_header_state_root`

    ABI: a0 = header RLP ptr, a1 = header length, a2 = 20-byte address ptr,
    a3 = witness.state ptr, a4 = witness.state length, a5 = witness.codes ptr,
    a6 = witness.codes length; returns a0 = status (0 found / 1 account absent /
    2 state-mpt error / 3 account-decode fail / 4 header fail / 5 code-hash
    not in codes).  On a full hit writes the pre-state contract-code
    `(offset, length)` into `witness.codes` to the two out cells.  Drives the
    `0xef 0x01 0x00` delegation-marker byte check.  The window is the abstract
    `codeModel`. -/
structure CodeAtHeaderStateRootAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `code_at_header_state_root`. -/
  entry : Word
  /-- The pre-state code `(offsetIntoCodes, length)` as a pure function of the
      header / address / witness bytes; `none` when the account or its code is
      absent. -/
  codeModel : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8) →
    Option (Word × Word)
  /-- Pre-state-code lookup contract. -/
  flat :
    ∀ (ret hdrBase hdrLen addrBase witStateBase witStateLen witCodesBase witCodesLen
        offCell lenCell offOld lenOld : Word)
      (hdrBytes addrBytes witStateBytes witCodesBytes : List (BitVec 8))
      (_hret : ret &&& ~~~(1 : Word) = ret)
      (_haddr20 : addrBytes.length = 20)
      (_halign : hdrBase.toNat % 8 = 0),
      cpsTripleWithin nCodeAtHeaderSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ hdrLen) ** (.x12 ↦ᵣ addrBase) **
          (.x13 ↦ᵣ witStateBase) ** (.x14 ↦ᵣ witStateLen) ** (.x15 ↦ᵣ witCodesBase) **
          (.x16 ↦ᵣ witCodesLen) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion hdrBase hdrBytes ** bytesRegion addrBase addrBytes **
          bytesRegion witStateBase witStateBytes ** bytesRegion witCodesBase witCodesBytes **
          (offCell ↦ₘ offOld) ** (lenCell ↦ₘ lenOld))
        ((regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion hdrBase hdrBytes ** bytesRegion addrBase addrBytes **
          bytesRegion witStateBase witStateBytes ** bytesRegion witCodesBase witCodesBytes) **
         (fun h =>
           -- full hit (a0 = 0): the code window is published
           (∃ off len, codeModel hdrBytes addrBytes witStateBytes witCodesBytes = some (off, len) ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (offCell ↦ₘ off) ** (lenCell ↦ₘ len)) h)) ∨
           -- no code (a0 ≠ 0): out cells clobbered
           (codeModel hdrBytes addrBytes witStateBytes witCodesBytes = none ∧
             (∃ st, (((.x10 ↦ᵣ st) ** memOwn offCell ** memOwn lenCell **
               ⌜st ≠ (0 : Word)⌝) h)))))

/-! ## 7. `account_at_header_state_root`

    ABI: a0 = header RLP ptr, a1 = header length, a2 = address ptr, a3 =
    address length, a4 = witness.state ptr, a5 = witness.state length, a6 =
    104-byte out account struct ptr; returns a0 = status (0 found / 1 absent /
    2 mpt error / 3 decode fail / 4 header fail).  On a hit the out struct
    receives the pre-state account record (nonce @+0, balance @+8, storage
    root @+40, code hash @+72).  Drives the pre-state nonce / delegation
    resolution.  The pre-state nonce is the abstract `nonceModel`. -/
structure AccountAtHeaderStateRootAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted `account_at_header_state_root`. -/
  entry : Word
  /-- The pre-state account nonce as a pure function of the header / address /
      witness bytes; `none` when the account is absent from the trie. -/
  nonceModel : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option Word
  /-- Pre-state-account lookup contract (nonce @+0 published; the remaining
      struct cells owned). -/
  flat :
    ∀ (ret hdrBase hdrLen addrBase addrLen witStateBase witStateLen outBase
        n0 b8 b16 b24 b32 b40 b48 b56 b64 b72 b80 b88 b96 : Word)
      (hdrBytes addrBytes witStateBytes : List (BitVec 8))
      (_hret : ret &&& ~~~(1 : Word) = ret)
      (_halign : hdrBase.toNat % 8 = 0)
      (_hoalign : outBase.toNat % 8 = 0),
      cpsTripleWithin nAccountAtHeaderSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ hdrLen) ** (.x12 ↦ᵣ addrBase) **
          (.x13 ↦ᵣ addrLen) ** (.x14 ↦ᵣ witStateBase) ** (.x15 ↦ᵣ witStateLen) **
          (.x16 ↦ᵣ outBase) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion hdrBase hdrBytes ** bytesRegion addrBase addrBytes **
          bytesRegion witStateBase witStateBytes **
          (outBase ↦ₘ n0) ** ((outBase + 8) ↦ₘ b8) ** ((outBase + 16) ↦ₘ b16) **
          ((outBase + 24) ↦ₘ b24) ** ((outBase + 32) ↦ₘ b32) ** ((outBase + 40) ↦ₘ b40) **
          ((outBase + 48) ↦ₘ b48) ** ((outBase + 56) ↦ₘ b56) ** ((outBase + 64) ↦ₘ b64) **
          ((outBase + 72) ↦ₘ b72) ** ((outBase + 80) ↦ₘ b80) ** ((outBase + 88) ↦ₘ b88) **
          ((outBase + 96) ↦ₘ b96))
        ((regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion hdrBase hdrBytes ** bytesRegion addrBase addrBytes **
          bytesRegion witStateBase witStateBytes **
          memOwn (outBase + 8) ** memOwn (outBase + 16) ** memOwn (outBase + 24) **
          memOwn (outBase + 32) ** memOwn (outBase + 40) ** memOwn (outBase + 48) **
          memOwn (outBase + 56) ** memOwn (outBase + 64) ** memOwn (outBase + 72) **
          memOwn (outBase + 80) ** memOwn (outBase + 88) ** memOwn (outBase + 96)) **
         (fun h =>
           -- found (a0 = 0): nonce cell = the modelled pre-state nonce
           (∃ nonce, nonceModel hdrBytes addrBytes witStateBytes = some nonce ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outBase ↦ₘ nonce)) h)) ∨
           -- absent / error (a0 ≠ 0): nonce cell owned
           (nonceModel hdrBytes addrBytes witStateBytes = none ∧
             (∃ st, (((.x10 ↦ᵣ st) ** memOwn outBase ** ⌜st ≠ (0 : Word)⌝) h)))))

/-! ## The 11-hypothesis footing

    Bundles the seven `fullCode` callee contracts above with the four
    string-only `TeerAssumedCallees` (from `TeerExistingAuthorityRefundSpec`)
    into the complete set of assumed callee contracts under which the teer
    body is proved.  All eleven are stated over the SHARED `cr` (instantiated
    to `fullCode` in the eventual top theorem). -/
structure TeerBodyAssumptions (cr : CodeReq) where
  /-- The four string-only callees (`rlp_walk_init/next`, `rlp_content_to_u64`,
      `bal_account_nonce_before_index`). -/
  strCallees : TeerAssumedCallees cr
  txTypeDispatch : TxTypeDispatchAssumed cr
  rlpListCountItems : RlpListCountItemsAssumed cr
  recoverAddress : Eip7702AuthorizationRecoverAddressAssumed cr
  balFindAccount : BalFindAccountByAddressAssumed cr
  balNonstorageFinals : BalAccountNonstorageFinalsAssumed cr
  codeAtHeaderStateRoot : CodeAtHeaderStateRootAssumed cr
  accountAtHeaderStateRoot : AccountAtHeaderStateRootAssumed cr

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
