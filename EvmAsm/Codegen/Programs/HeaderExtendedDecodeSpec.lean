/-
  Whole-program caller-contract scaffolding for `headerExtendedDecode_prog`
  (`Programs/HeaderDecode.lean`, PR-K39, 174 instructions, entry
  `GuestAddrs.header_extended_decode`).

  The decoder walks an RLP-encoded Ethereum block header SEQUENTIALLY with one
  `rlp_walk_init` + nineteen `rlp_walk_next` calls (fields 0..18), extracting the
  nine STF-essential fields into a flat 144-byte output struct:

       0.. 32  parent_hash       (field 0,  32-byte copy, len = 32)
      32.. 64  state_root        (field 3,  32-byte copy, len = 32)
      64.. 72  number            (field 8,  u64)
      72.. 80  timestamp         (field 11, u64)
      80.. 88  gas_limit         (field 9,  u64)
      88.. 96  gas_used          (field 10, u64)
      96..128  base_fee_per_gas  (field 15, u256 big-endian)
     128..136  blob_gas_used     (field 17, u64)
     136..144  excess_blob_gas   (field 18, u64)

  Calling convention:
    a0 (input)  : header_rlp ptr        (saved into s0/x8)
    a1 (input)  : header byte length
    a2 (input)  : 144-byte output struct ptr (saved into s2/x18)
    ra (input)  : return
    a0 (output) : 0 success / 1 parse fail (any walk failure, a wrong-length
                  parent_hash/state_root, or a numeric-field decode failure —
                  in particular a missing field 15, pre-London headers).

  Reuses the merged strict cursor-walk primitives `rlp_walk_init` /
  `rlp_walk_next` (`Rv64.RLP.WalkInit`/`WalkNext`), the numeric decoders
  `rlp_content_to_u64` / `rlp_content_to_u256_be` (`Rv64.RLP.ContentToU64`/
  `ContentToU256Be`), and the forward byte-copy accumulator `copyIntoRegion`.

  This module hosts the code layout, disjointness/mono lemmas, and the semantic
  decode model.  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3
  axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-! ## Code layout -/

/-- The decoder body's fixed guest base address. -/
abbrev HB : Word := (GuestAddrs.header_extended_decode : Word)

/-- The four merged RLP callee base addresses. -/
abbrev WIB : Word := (GuestAddrs.rlp_walk_init : Word)
abbrev WNB : Word := (GuestAddrs.rlp_walk_next : Word)
abbrev CU64B : Word := (GuestAddrs.rlp_content_to_u64 : Word)
abbrev CU256B : Word := (GuestAddrs.rlp_content_to_u256_be : Word)

set_option maxRecDepth 8000 in
theorem hed_length : headerExtendedDecode_prog.length = 174 := by decide

/-- The decoder's own re-emitted instructions at `header_extended_decode`. -/
def hedCode : CodeReq := CodeReq.ofProg HB headerExtendedDecode_prog

/-- The four independent merged RLP callee leaves (each `CodeReq.ofProg` at its
    own guest base): the cursor walkers and the two numeric content decoders. -/
def tailCode : CodeReq :=
  (rlp_walk_init_code WIB).union ((rlp_walk_next_code WNB).union
    ((rlp_content_to_u64_code CU64B).union (rlp_content_to_u256_be_code CU256B)))

/-- The full linked closure: this decoder plus the four RLP callee leaves. -/
def fullCode : CodeReq := hedCode.union tailCode

/-- The decoder body is disjoint from every one of the four callee leaves (all
    reside far below the decoder base in the guest image). -/
theorem hed_disjoint : hedCode.Disjoint tailCode := by
  unfold hedCode tailCode rlp_walk_init_code rlp_walk_next_code
    rlp_content_to_u64_code rlp_content_to_u256_be_code
  refine CodeReq.Disjoint.union_right ?_
    (CodeReq.Disjoint.union_right ?_
      (CodeReq.Disjoint.union_right ?_ ?_))
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [hed_length]; decide
    · rw [rlp_walk_init_prog_length]; decide
    · rw [hed_length, rlp_walk_init_prog_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [hed_length]; decide
    · rw [rlp_walk_next_prog_length]; decide
    · rw [hed_length, rlp_walk_next_prog_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [hed_length]; decide
    · rw [rlp_content_to_u64_prog_length]; decide
    · rw [hed_length, rlp_content_to_u64_prog_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [hed_length]; decide
    · rw [rlp_content_to_u256_be_prog_length]; decide
    · rw [hed_length, rlp_content_to_u256_be_prog_length]; decide

#print axioms hed_disjoint

theorem hed_mono : ∀ a i, hedCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-- The callee closure is subsumed by the decoder's full closure. -/
theorem tail_mono : ∀ a i, tailCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right hed_disjoint (fun _ _ h => h) a i hi

/-! ### Callee-leaf subsumption

    Each of the four RLP leaves is a sub-union of `tailCode`, hence of
    `fullCode`.  The pairwise disjointness of the leaves lets `mono_union_right`
    skip the non-matching heads. -/

private theorem di_wi_wn :
    (rlp_walk_init_code WIB).Disjoint (rlp_walk_next_code WNB) := by
  unfold rlp_walk_init_code rlp_walk_next_code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_walk_init_prog_length]; decide
  · rw [rlp_walk_next_prog_length]; decide
  · rw [rlp_walk_init_prog_length, rlp_walk_next_prog_length]; decide

private theorem di_wi_u64 :
    (rlp_walk_init_code WIB).Disjoint (rlp_content_to_u64_code CU64B) := by
  unfold rlp_walk_init_code rlp_content_to_u64_code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_walk_init_prog_length]; decide
  · rw [rlp_content_to_u64_prog_length]; decide
  · rw [rlp_walk_init_prog_length, rlp_content_to_u64_prog_length]; decide

private theorem di_wi_u256 :
    (rlp_walk_init_code WIB).Disjoint (rlp_content_to_u256_be_code CU256B) := by
  unfold rlp_walk_init_code rlp_content_to_u256_be_code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_walk_init_prog_length]; decide
  · rw [rlp_content_to_u256_be_prog_length]; decide
  · rw [rlp_walk_init_prog_length, rlp_content_to_u256_be_prog_length]; decide

private theorem di_wn_u64 :
    (rlp_walk_next_code WNB).Disjoint (rlp_content_to_u64_code CU64B) := by
  unfold rlp_walk_next_code rlp_content_to_u64_code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_walk_next_prog_length]; decide
  · rw [rlp_content_to_u64_prog_length]; decide
  · rw [rlp_walk_next_prog_length, rlp_content_to_u64_prog_length]; decide

private theorem di_wn_u256 :
    (rlp_walk_next_code WNB).Disjoint (rlp_content_to_u256_be_code CU256B) := by
  unfold rlp_walk_next_code rlp_content_to_u256_be_code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_walk_next_prog_length]; decide
  · rw [rlp_content_to_u256_be_prog_length]; decide
  · rw [rlp_walk_next_prog_length, rlp_content_to_u256_be_prog_length]; decide

private theorem di_u64_u256 :
    (rlp_content_to_u64_code CU64B).Disjoint (rlp_content_to_u256_be_code CU256B) := by
  unfold rlp_content_to_u64_code rlp_content_to_u256_be_code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_content_to_u64_prog_length]; decide
  · rw [rlp_content_to_u256_be_prog_length]; decide
  · rw [rlp_content_to_u64_prog_length, rlp_content_to_u256_be_prog_length]; decide

theorem walkInit_mono : ∀ a i, rlp_walk_init_code WIB a = some i → fullCode a = some i := by
  intro a i hi
  exact tail_mono a i (CodeReq.union_mono_left a i hi)

theorem walkNext_mono : ∀ a i, rlp_walk_next_code WNB a = some i → fullCode a = some i := by
  intro a i hi
  refine tail_mono a i ?_
  unfold tailCode
  exact CodeReq.mono_union_right di_wi_wn (fun a i h => CodeReq.union_mono_left a i h) a i hi

theorem u64_mono : ∀ a i, rlp_content_to_u64_code CU64B a = some i → fullCode a = some i := by
  intro a i hi
  refine tail_mono a i ?_
  unfold tailCode
  refine CodeReq.mono_union_right di_wi_u64 ?_ a i hi
  intro a i h
  exact CodeReq.mono_union_right di_wn_u64 (fun a i h => CodeReq.union_mono_left a i h) a i h

theorem u256_mono : ∀ a i, rlp_content_to_u256_be_code CU256B a = some i → fullCode a = some i := by
  intro a i hi
  refine tail_mono a i ?_
  unfold tailCode
  refine CodeReq.mono_union_right di_wi_u256 ?_ a i hi
  intro a i h
  refine CodeReq.mono_union_right di_wn_u256 ?_ a i h
  intro a i h
  exact CodeReq.mono_union_right di_u64_u256 (fun _ _ h => h) a i h

#print axioms hed_mono
#print axioms walkInit_mono
#print axioms walkNext_mono
#print axioms u64_mono
#print axioms u256_mono

/-! ## Semantic decode model

    The decoder threads a single cursor through the header list body with 19
    successive `rlp_walk_next` steps (fields 0..18).  Each field's raw decode is
    the merged callee relation `rlpItemDecode`; the nine essential fields are
    pinned to that step's `(next, len)` and to the numeric/copy decode the
    program performs on the field content.  No decode-determinism is assumed. -/

/-- The threaded sequential walk: for every field `i < 19`, the RLP item at the
    absolute cursor `cur i` (byte offset `(cur i − srcBase)`) decodes via
    `rlpItemDecode`, advancing the cursor to `cur (i+1)` with content length
    `len i`.  `srcBase` is the header base pointer and `endPtr` the list end. -/
def WalkOk (bytes : List (BitVec 8)) (srcBase endPtr : Word)
    (cur len : Nat → Word) : Prop :=
  ∀ i, i < 19 →
    rlpItemDecode bytes (cur i - srcBase).toNat (cur i) endPtr (cur (i + 1)) (len i)

/-- A `k`-field prefix of the sequential walk (fields `0 .. k-1` decode). -/
def WalkPrefix (bytes : List (BitVec 8)) (srcBase endPtr : Word)
    (cur len : Nat → Word) (k : Nat) : Prop :=
  ∀ i, i < k →
    rlpItemDecode bytes (cur i - srcBase).toNat (cur i) endPtr (cur (i + 1)) (len i)

/-- Byte offset of field `i`'s content into `bytes`: the content of a decoded
    RLP item ends at its `next` cursor, so it starts at `next − len`.  Here
    `next = cur (i+1)` and `len = len i`. -/
def contentOff (srcBase : Word) (cur len : Nat → Word) (i : Nat) : Nat :=
  (cur (i + 1) - len i - srcBase).toNat

/-- The `rlp_content_to_u64` status-0 verdict on a field's content: an empty
    string decodes to `0`, or a canonical 1..8-byte big-endian scalar (no leading
    zero) decodes to its `fromBytesBE` value. -/
def u64Ok (bytes : List (BitVec 8)) (off : Nat) (l : Word) (v : Word) : Prop :=
  (l.toNat = 0 ∧ v = 0) ∨
  (0 < l.toNat ∧ l.toNat ≤ 8 ∧ getByteAt bytes off ≠ 0 ∧
    v = BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop off).take l.toNat)))

/-- The `rlp_content_to_u64` non-zero-status (failure) verdict: content longer
    than 8 bytes, or a non-canonical (leading-zero) 1..8-byte scalar. -/
def u64Fail (bytes : List (BitVec 8)) (off : Nat) (l : Word) : Prop :=
  8 < l.toNat ∨ (0 < l.toNat ∧ l.toNat ≤ 8 ∧ getByteAt bytes off = 0)

/-- The `rlp_content_to_u256_be` status-0 verdict on a field's content: an empty
    string writes 32 zero bytes; a canonical 1..32-byte scalar (no leading zero)
    is written big-endian, right-aligned, into a zeroed 32-byte buffer. -/
def u256Ok (bytes : List (BitVec 8)) (off : Nat) (l : Word)
    (out : List (BitVec 8)) : Prop :=
  (l.toNat = 0 ∧ out = List.replicate 32 (0 : BitVec 8)) ∨
  (0 < l.toNat ∧ getByteAt bytes off ≠ 0 ∧
    out = copyN (List.replicate 32 (0 : BitVec 8)) bytes (32 - l.toNat) off l.toNat)

/-- The `rlp_content_to_u256_be` non-zero-status (failure) verdict: content
    longer than 32 bytes, or a non-canonical (leading-zero) scalar. -/
def u256Fail (bytes : List (BitVec 8)) (off : Nat) (l : Word) : Prop :=
  32 < l.toNat ∨ (0 < l.toNat ∧ getByteAt bytes off = 0)

/-- A 32-byte hash field copied forward from the input `bytes` (at content offset
    `off`) into the caller's old 32-byte struct slot. -/
def hashCopied (bytes old : List (BitVec 8)) (off : Nat) : List (BitVec 8) :=
  copyIntoRegion old bytes 0 off 32

theorem hashCopied_length (bytes old : List (BitVec 8)) (off : Nat)
    (hlen : old.length = 32) : (hashCopied bytes old off).length = 32 := by
  unfold hashCopied; rw [copyIntoRegion_length]; exact hlen

/-- The genuine success verdict: the initial cursor from `rlp_walk_init`, the
    full 19-field walk (`WalkOk`), the two 32-byte hash-length checks, the six
    u64 field decodes, and the base_fee u256 decode.  Each numeric value / copy
    is pinned to the field's threaded content offset. -/
def Decoded (bytes : List (BitVec 8)) (srcBase endPtr initCursor : Word)
    (cur len : Nat → Word)
    (vNumber vTimestamp vGasLimit vGasUsed vBlobGas vExcessBlob : Word)
    (baseFeeOut : List (BitVec 8)) : Prop :=
  cur 0 = initCursor ∧
  WalkOk bytes srcBase endPtr cur len ∧
  (len 0).toNat = 32 ∧
  (len 3).toNat = 32 ∧
  u64Ok bytes (contentOff srcBase cur len 8) (len 8) vNumber ∧
  u64Ok bytes (contentOff srcBase cur len 9) (len 9) vGasLimit ∧
  u64Ok bytes (contentOff srcBase cur len 10) (len 10) vGasUsed ∧
  u64Ok bytes (contentOff srcBase cur len 11) (len 11) vTimestamp ∧
  u256Ok bytes (contentOff srcBase cur len 15) (len 15) baseFeeOut ∧
  u64Ok bytes (contentOff srcBase cur len 17) (len 17) vBlobGas ∧
  u64Ok bytes (contentOff srcBase cur len 18) (len 18) vExcessBlob

/-- The 144-byte output struct after a **successful** decode, each cell tied to
    the actual decoded field value at its docstring offset:
      +0   parent_hash (32-byte copy),   +32  state_root (32-byte copy),
      +64  number,   +72 timestamp,   +80 gas_limit,   +88 gas_used,
      +96  base_fee_per_gas (32-byte u256), +128 blob_gas_used, +136 excess_blob_gas. -/
def outputSuccess (outBase srcBase : Word) (bytes oldPH oldSR : List (BitVec 8))
    (cur len : Nat → Word)
    (vNumber vTimestamp vGasLimit vGasUsed vBlobGas vExcessBlob : Word)
    (baseFeeOut : List (BitVec 8)) : Assertion :=
  bytesRegion outBase (hashCopied bytes oldPH (contentOff srcBase cur len 0)) **
  bytesRegion (outBase + 32) (hashCopied bytes oldSR (contentOff srcBase cur len 3)) **
  ((outBase + 64) ↦ₘ vNumber) **
  ((outBase + 72) ↦ₘ vTimestamp) **
  ((outBase + 80) ↦ₘ vGasLimit) **
  ((outBase + 88) ↦ₘ vGasUsed) **
  bytesRegion (outBase + 96) baseFeeOut **
  ((outBase + 128) ↦ₘ vBlobGas) **
  ((outBase + 136) ↦ₘ vExcessBlob)

/-- The failure verdict of one walk step at field index `k`: either the cursor is
    already at/past the list end (status 2) or no canonical RLP item decodes at
    that cursor (statuses 3..6). -/
def walkStepFail (bytes : List (BitVec 8)) (endPtr cursor : Word) (off : Nat) : Prop :=
  ¬ BitVec.ult cursor endPtr = true ∨
  ¬ ∃ next l, rlpItemDecode bytes off cursor endPtr next l

/-- A header-decode **failure** outcome, matching the program's short-circuit
    dispatch: `rlp_walk_init` reject, a `rlp_walk_next` reject at some field, a
    wrong-length parent_hash/state_root, a u64 field reject, or the base_fee u256
    reject (in particular a missing field 15 — a pre-London header — surfaces as
    a `walkReject` at index 15).  Each arm carries the genuine prefix walk up to
    the failing stage plus that stage's failure witness (no decode-determinism). -/
inductive DecodeFailure (bytes : List (BitVec 8)) (srcBase endPtr initCursor : Word) : Prop
  | initReject :
      DecodeFailure bytes srcBase endPtr initCursor
  | walkReject (cur len : Nat → Word) (k : Nat) (hk : k < 19)
      (hc0 : cur 0 = initCursor)
      (hpre : WalkPrefix bytes srcBase endPtr cur len k)
      (hfail : walkStepFail bytes endPtr (cur k) (cur k - srcBase).toNat) :
      DecodeFailure bytes srcBase endPtr initCursor
  | lenReject0 (cur len : Nat → Word)
      (hc0 : cur 0 = initCursor)
      (hpre : WalkPrefix bytes srcBase endPtr cur len 1)
      (hlen : (len 0).toNat ≠ 32) :
      DecodeFailure bytes srcBase endPtr initCursor
  | lenReject3 (cur len : Nat → Word)
      (hc0 : cur 0 = initCursor)
      (hpre : WalkPrefix bytes srcBase endPtr cur len 4)
      (hlen : (len 3).toNat ≠ 32) :
      DecodeFailure bytes srcBase endPtr initCursor
  | u64Reject (cur len : Nat → Word) (i : Nat)
      (hi : i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 17 ∨ i = 18)
      (hc0 : cur 0 = initCursor)
      (hpre : WalkPrefix bytes srcBase endPtr cur len (i + 1))
      (hfail : u64Fail bytes (contentOff srcBase cur len i) (len i)) :
      DecodeFailure bytes srcBase endPtr initCursor
  | u256Reject (cur len : Nat → Word)
      (hc0 : cur 0 = initCursor)
      (hpre : WalkPrefix bytes srcBase endPtr cur len 16)
      (hfail : u256Fail bytes (contentOff srcBase cur len 15) (len 15)) :
      DecodeFailure bytes srcBase endPtr initCursor

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
