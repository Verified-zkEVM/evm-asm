/-
  Whole-program caller contract scaffolding for `withdrawalDecode_prog`
  (`Programs/Withdrawal.lean`, PR-K49, 60 instructions, entry
  `GuestAddrs.withdrawal_decode`).

  A withdrawal is the RLP list `[index, validator_index, address, amount]`.
  The accessor decodes it into a 48-byte output struct:

       0..  8  index           (u64 LE)   -- field 0, via rlp_field_to_u64_strict
       8.. 16  validator_index (u64 LE)   -- field 1, via rlp_field_to_u64_strict
      16.. 36  address         (20 B)     -- field 2, via rlp_list_nth_item + copy
      36.. 40  zero pad
      40.. 48  amount          (u64 LE)   -- field 3, via rlp_field_to_u64_strict

  Calling convention:
    a0 (input)  : withdrawal_rlp ptr        (saved into s0/x8)
    a1 (input)  : withdrawal_rlp byte length (saved into s1/x9)
    a2 (input)  : 48-byte output struct ptr  (saved into s2/x18)
    ra (input)  : return
    a0 (output) : 0 success / 1 parse fail (any field's RLP failure, or the
                  address length ≠ 20)

  Both u64 fields and the address field reuse the merged strict callees:
  `rlp_field_to_u64_strict` (fields 0/1/3) and `rlp_list_nth_item` (field 2).
  The latter's linked code is already a sub-union of `rlp_field_to_u64_strict`'s code, so
  the full linked closure here is `wdCode ∪ RlpFieldToU64StrictSAsm.code`, exactly as
  in `HeaderExtractNumberSpec`.

  This module hosts the code layout, disjointness/mono lemmas, the semantic
  decode model, and the caller-facing pre/post.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpFieldToU64StrictFlatSAsm
import EvmAsm.Codegen.Programs.Withdrawal
import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64StrictSAsm

/-! ## Code layout -/

/-- The accessor body's fixed guest base address. -/
abbrev WB : Word := (GuestAddrs.withdrawal_decode : Word)

theorem wd_length : withdrawalDecode_prog.length = 60 := by decide

/-- The wrapper's own re-emitted instructions at `withdrawal_decode`. -/
def wdCode : CodeReq := CodeReq.ofProg WB withdrawalDecode_prog

/-- The full linked closure: this accessor plus the strict `rlp_field_to_u64`
    selector (whose linked closure already contains `rlp_list_nth_item` and
    `rlp_content_to_u64`). -/
def fullCode : CodeReq := wdCode.union EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code

theorem wd_disjoint :
    wdCode.Disjoint EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code := by
  unfold wdCode EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code
  refine CodeReq.Disjoint.union_right ?_
    (CodeReq.Disjoint.union_right ?_ ?_)
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wrapperCode
      EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B WB
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wd_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64StrictSAsm.program_length]; decide
    · rw [wd_length, EvmAsm.Codegen.RlpFieldToU64StrictSAsm.program_length]; decide
  · unfold EvmAsm.Codegen.RlpListNthItemSAsm.code
      EvmAsm.Codegen.RlpListNthItemSAsm.B WB
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wd_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · rw [wd_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.contentCode
      rlp_content_to_u64_strict_code EvmAsm.Codegen.RlpFieldToU64StrictSAsm.C64B WB
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wd_length]; decide
    · rw [rlp_content_to_u64_strict_prog_length]; decide
    · rw [wd_length, rlp_content_to_u64_strict_prog_length]; decide

#print axioms wd_disjoint

/-- K34's linked code is subsumed by the accessor's full closure. -/
theorem k34_mono :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right wd_disjoint (fun _ _ h => h) a i hi

theorem wd_mono : ∀ a i, wdCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-- The strict `rlp_list_nth_item` subroutine (called for the address field) is
    a sub-union of K34's code, hence of the full closure. -/
theorem k20_mono :
    ∀ a i, EvmAsm.Codegen.RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  refine k34_mono a i ?_
  unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code
  exact CodeReq.mono_union_right EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wrapper_list_disjoint
    (CodeReq.union_mono_left) a i hi

#print axioms k34_mono
#print axioms k20_mono

/-! ## Semantic decode model

    Tied to the merged callee `Result`/`Success` relations.  The three u64
    fields (index/validator_index/amount) decode via K34's `Result` (status 0);
    the address field decodes via K20's `Success` and must be exactly 20 bytes.
    All four are indexed positions in the same strict RLP list. -/

open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- The genuine success verdict: every field decodes (u64 status 0) and the
    address field is exactly 20 content bytes at relative offset `o2`. -/
def Decoded (bytes : List (BitVec 8)) (listBase : Word) (listLen : Nat)
    (v0 v1 v3 : Word) (o2 l2 : Word) : Prop :=
  EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes listBase listLen 0 (0 : Word) v0 ∧
  EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes listBase listLen 1 (0 : Word) v1 ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2 ∧
  l2.toNat = 20 ∧
  EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes listBase listLen 3 (0 : Word) v3

/-- The 20 address content bytes copied forward from the input `bytes` (at the
    relative content offset `o2`) into the caller's old 20-byte address slot. -/
def addrCopied (bytes oldAddr : List (BitVec 8)) (o2 : Word) : List (BitVec 8) :=
  copyIntoRegion oldAddr bytes 0 o2.toNat 20

theorem addrCopied_length (bytes oldAddr : List (BitVec 8)) (o2 : Word)
    (hlen : oldAddr.length = 20) :
    (addrCopied bytes oldAddr o2).length = 20 := by
  unfold addrCopied; rw [copyIntoRegion_length]; exact hlen

/-- The 48-byte output struct after a **successful** decode, with each cell tied
    to the actual decoded field value:
      +0  = index (v0),  +8 = validator_index (v1),
      +16 = 20-byte address copy,  +36 = 4-byte pad (unchanged),
      +40 = amount (v3). -/
def outputSuccess (outBase v0 v1 v3 o2 : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) : Assertion :=
  (outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) **
  bytesRegion (outBase + 16) (addrCopied bytes oldAddr o2) **
  bytesRegion (outBase + 36) pad4 **
  ((outBase + 40) ↦ₘ v3)

/-- A withdrawal-decode **failure** outcome, matching the program's short-circuit
    dispatch (field 0 → field 1 → field 2 list → address length → field 3).
    Each arm names the *actual* failing stage via the merged callee semantics
    (no decode-determinism assumed). -/
inductive DecodeFailure (bytes : List (BitVec 8)) (listBase : Word)
    (listLen : Nat) : Prop
  | field0 (status v : Word) (hnz : status ≠ 0)
      (h : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes listBase listLen 0 status v) :
      DecodeFailure bytes listBase listLen
  | field1 (status v : Word) (hnz : status ≠ 0)
      (h : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes listBase listLen 1 status v) :
      DecodeFailure bytes listBase listLen
  | field2List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 2) :
      DecodeFailure bytes listBase listLen
  | field2Len (o2 l2 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2)
      (hlen : l2.toNat ≠ 20) :
      DecodeFailure bytes listBase listLen
  | field3 (status v : Word) (hnz : status ≠ 0)
      (h : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes listBase listLen 3 status v) :
      DecodeFailure bytes listBase listLen

end EvmAsm.Codegen.WithdrawalDecodeSpec
