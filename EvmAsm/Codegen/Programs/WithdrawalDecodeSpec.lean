/-
  Whole-program caller contract scaffolding for `withdrawalDecode_prog`
  (`Programs/Withdrawal.lean`, PR-K49, 60 instructions, entry
  `GuestAddrs.withdrawal_decode`).

  A withdrawal is the RLP list `[index, validator_index, address, amount]`.
  The accessor decodes it into a 48-byte output struct:

       0..  8  index           (u64 LE)   -- field 0, via rlp_field_to_u64
       8.. 16  validator_index (u64 LE)   -- field 1, via rlp_field_to_u64
      16.. 36  address         (20 B)     -- field 2, via rlp_list_nth_item + copy
      36.. 40  zero pad
      40.. 48  amount          (u64 LE)   -- field 3, via rlp_field_to_u64

  Calling convention:
    a0 (input)  : withdrawal_rlp ptr        (saved into s0/x8)
    a1 (input)  : withdrawal_rlp byte length (saved into s1/x9)
    a2 (input)  : 48-byte output struct ptr  (saved into s2/x18)
    ra (input)  : return
    a0 (output) : 0 success / 1 parse fail (any field's RLP failure, or the
                  address length ≠ 20)

  Both u64 fields and the address field reuse the merged strict callees:
  `rlp_field_to_u64` (fields 0/1/3) and `rlp_list_nth_item` (field 2).  The
  latter's linked code is already a sub-union of `rlp_field_to_u64`'s code, so
  the full linked closure here is `wdCode ∪ RlpFieldToU64SAsm.code`, exactly as
  in `HeaderExtractNumberSpec`.

  This module hosts the code layout, disjointness/mono lemmas, the semantic
  decode model, and the caller-facing pre/post.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpFieldToU64FlatSAsm
import EvmAsm.Codegen.Programs.Withdrawal

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64SAsm

/-! ## Code layout -/

/-- The accessor body's fixed guest base address. -/
abbrev WB : Word := (GuestAddrs.withdrawal_decode : Word)

theorem wd_length : withdrawalDecode_prog.length = 60 := by decide

/-- The wrapper's own re-emitted instructions at `withdrawal_decode`. -/
def wdCode : CodeReq := CodeReq.ofProg WB withdrawalDecode_prog

/-- The full linked closure: this accessor plus the strict `rlp_field_to_u64`
    selector (whose linked closure already contains `rlp_list_nth_item` and
    `rlp_content_to_u64`). -/
def fullCode : CodeReq := wdCode.union EvmAsm.Codegen.RlpFieldToU64SAsm.code

theorem wd_disjoint :
    wdCode.Disjoint EvmAsm.Codegen.RlpFieldToU64SAsm.code := by
  unfold wdCode EvmAsm.Codegen.RlpFieldToU64SAsm.code
  refine CodeReq.Disjoint.union_right ?_
    (CodeReq.Disjoint.union_right ?_ ?_)
  · unfold EvmAsm.Codegen.RlpFieldToU64SAsm.wrapperCode
      EvmAsm.Codegen.RlpFieldToU64SAsm.B WB
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wd_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
    · rw [wd_length, EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
  · unfold EvmAsm.Codegen.RlpListNthItemSAsm.code
      EvmAsm.Codegen.RlpListNthItemSAsm.B WB
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wd_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · rw [wd_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Codegen.RlpFieldToU64SAsm.contentCode
      rlp_content_to_u64_code EvmAsm.Codegen.RlpFieldToU64SAsm.C64B WB
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wd_length]; decide
    · rw [rlp_content_to_u64_prog_length]; decide
    · rw [wd_length, rlp_content_to_u64_prog_length]; decide

#print axioms wd_disjoint

/-- K34's linked code is subsumed by the accessor's full closure. -/
theorem k34_mono :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64SAsm.code a = some i → fullCode a = some i := by
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
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.code
  exact CodeReq.mono_union_right EvmAsm.Codegen.RlpFieldToU64SAsm.wrapper_list_disjoint
    (CodeReq.union_mono_left) a i hi

#print axioms k34_mono
#print axioms k20_mono

end EvmAsm.Codegen.WithdrawalDecodeSpec
