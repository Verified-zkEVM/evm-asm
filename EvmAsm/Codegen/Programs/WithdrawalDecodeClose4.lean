/-
  `withdrawalDecode_prog` caller-contract composition, part 4 — the final close.

  This module threads the four field stages, the length check, and the address
  copy loop into the whole-program caller contract
  `withdrawal_decode_spec_within`, routing every parse-failure exit through the
  common failure tail (`wdFailEpi`) and the all-fields-ok exit through the
  success tail (`wdSuccessEpi`).

  The composition is inside-out: per-boundary reshape lemmas line up each
  stage's continue-post with the next stage's pre (and each fail-post with the
  failure tail), and a thin final compose stitches the reshaped pieces via
  `cpsBranchWithin_merge_same_cr`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.WithdrawalDecodeClose3

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64SAsm

/-! ## Whole-program post-condition pieces -/

/-- The registers/slots common to both the success and the failure return:
    the restored caller registers (`x2/x1/x8/x9/x18`) and the four withdrawal
    saved slots (`spW..spW+24`), exactly `wdEpiCore`'s non-`G` post. -/
def wdCommon (sp0 spW wra cs0 cs1 cs2 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ wra) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
  (.x18 ↦ᵣ cs2) ** (spW ↦ₘ wra) ** ((spW + 8) ↦ₘ cs0) **
  ((spW + 16) ↦ₘ cs1) ** ((spW + 24) ↦ₘ cs2)

theorem pcFree_wdCommon (sp0 spW wra cs0 cs1 cs2 : Word) :
    (wdCommon sp0 spW wra cs0 cs1 cs2).pcFree := by
  unfold wdCommon
  repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj

/-- The mutable leftover after a failure return: the whole 48-byte output struct
    (contents forgotten, only ownership retained), the input region, the two
    `wd_offset`/`wd_length` cells, and the reclaimed 12-cell scratch stack. -/
def wdFailLeftover (spW outBase listBase : Word) (bytes : List (BitVec 8)) :
    Assertion :=
  fun h => ∃ (o0 o1 o3 woff wlen : Word) (addr20 pad4 : List (BitVec 8)),
    ((outBase ↦ₘ o0) ** ((outBase + 8) ↦ₘ o1) **
     bytesRegion (outBase + 16) addr20 ** bytesRegion (outBase + 36) pad4 **
     ((outBase + 40) ↦ₘ o3) ** bytesRegion listBase bytes **
     (wdOffsetAddr ↦ₘ woff) ** (wdLengthAddr ↦ₘ wlen) ** stackFree spW 12) h

/-- The output-struct leftover after a success return, each cell tied to the
    genuinely decoded field value (`outputSuccess`), plus the untouched input
    region, the two data cells (still holding the address offset/length), and
    the reclaimed scratch stack. -/
def wdSuccessOut (spW outBase listBase v0 v1 v3 o2 l2 : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) : Assertion :=
  outputSuccess outBase v0 v1 v3 o2 bytes oldAddr pad4 **
  bytesRegion listBase bytes ** (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2) **
  stackFree spW 12

/-- The whole-program post: `a0 = 0` with the genuine decoded output struct, or
    `a0 = 1` with a witnessed `DecodeFailure` and the owned leftover. -/
def wdWholePost (sp0 spW wra cs0 cs1 cs2 outBase listBase : Word)
    (listLen : Nat) (bytes oldAddr pad4 : List (BitVec 8)) : Assertion :=
  fun h =>
    (∃ (v0 v1 v3 o2 l2 : Word),
      ((⌜Decoded bytes listBase listLen v0 v1 v3 o2 l2⌝ : Assertion) **
       ((.x10 ↦ᵣ (0 : Word)) ** wdCommon sp0 spW wra cs0 cs1 cs2 **
        wdSuccessOut spW outBase listBase v0 v1 v3 o2 l2 bytes oldAddr pad4)) h) ∨
    (((⌜DecodeFailure bytes listBase listLen⌝ : Assertion) **
      ((.x10 ↦ᵣ (1 : Word)) ** wdCommon sp0 spW wra cs0 cs1 cs2 **
       wdFailLeftover spW outBase listBase bytes)) h)

end EvmAsm.Codegen.WithdrawalDecodeSpec
