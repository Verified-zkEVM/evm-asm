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

/-! ## Scratch-stack reconcile (K34 boundary)

    The whole-program pre owns `stackFree spW 12` (cells `spW-8 … spW-96`).  A
    K34 field call allocates its own frame at `newSp = spW - 32`, using the top
    cell `spW-8` framed off plus `frameSlotsOwn frame newSp` (3 cells
    `spW-16, spW-24, spW-32`) and `stackFree newSp 8` (cells `spW-40 … spW-96`).  These
    two shapes hold the same 12 owned cells. -/

/-- Assemble a K34 field call's reclaimed scratch back into `stackFree spW 12`. -/
theorem wdStack12_of_k34 (sp0 spW newSp : Word)
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12)) : ∀ h,
    (memOwn (spW - BitVec.ofNat 64 8) **
     frameSlotsOwn frame newSp ** stackFree newSp 8) h →
    stackFree spW 12 h := by
  intro h hp
  have hse : signExtend12 (-32 : BitVec 12) = (0xFFFFFFFFFFFFFFE0 : Word) := by decide
  subst hnewSp
  rw [hse] at hp
  simp only [frameSlotsOwn, frame, List.foldr, sepConj_emp_right',
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hp
  simp only [stackFree] at hp ⊢
  simp only [sepConj_emp_right', Nat.reduceMul, Nat.reduceAdd] at hp ⊢
  -- normalise every K34-frame cell address to the canonical `spW - N#64` form
  rw [show spW + (18446744073709551584 : Word) + (0 : Word)
        = spW - BitVec.ofNat 64 32 from by bv_omega,
      show spW + (18446744073709551584 : Word) + (8 : Word)
        = spW - BitVec.ofNat 64 24 from by bv_omega,
      show spW + (18446744073709551584 : Word) + (16 : Word)
        = spW - BitVec.ofNat 64 16 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 64
        = spW - BitVec.ofNat 64 96 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 56
        = spW - BitVec.ofNat 64 88 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 48
        = spW - BitVec.ofNat 64 80 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 40
        = spW - BitVec.ofNat 64 72 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 32
        = spW - BitVec.ofNat 64 64 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 24
        = spW - BitVec.ofNat 64 56 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 16
        = spW - BitVec.ofNat 64 48 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 8
        = spW - BitVec.ofNat 64 40 from by bv_omega] at hp
  xperm_hyp hp

#print axioms wdStack12_of_k34

end EvmAsm.Codegen.WithdrawalDecodeSpec
