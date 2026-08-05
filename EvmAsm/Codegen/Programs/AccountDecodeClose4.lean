/-
  `accountDecode_prog` caller-contract composition, part 4 — the whole-program
  post-condition model and the two generic edge reshapes.

  All four account fields decode via the same `rlp_list_nth_item` (K20) callee
  and share the outer frame (`spW = newSp = sp0 - 64`), so — unlike the
  withdrawal decoder — there is no K34↔K20 stack transform: ONE failure arm
  (`adFailArm`) and ONE continue reshape (`adContReshape`) cover every field
  boundary.

    * `adCommon`/`adScratch`/`adFailLeftover`/`adSuccessOut`/`adWholePost` —
      the whole-program success/failure outcome (mirrors `wdWholePost`).
    * `adFailArm` — the shared failure tail (`AB+504 → saved.ra`) landing the
      whole-program failure post from any reshaped fail pre.
    * `adContReshape` — a field's K20 continue post (`adK20ContPost`, with the
      three length-check temporaries exposed as values) reshaped into the
      length-check pre plus the ambient continue frame `adContFrame`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeClose3

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved savedVals listNthFrame savedFrame regsAt_listNthFrame
  Success Result)

/-! ## Whole-program post-condition pieces -/

/-- The registers/slots common to both the success and the failure return: the
    restored caller registers (`x1/x8/x9/x18/x19/x20/x21`) reloaded from their
    (untouched) frame slots and `sp := sp0`.  Exactly `adEpilogue`'s non-`F`
    post. -/
def adCommon (sp0 spW : Word) (saved : Saved) : Assertion :=
  ((.x2 : Reg) ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) ** savedFrame spW saved

theorem pcFree_adCommon (sp0 spW : Word) (saved : Saved) :
    (adCommon sp0 spW saved).pcFree := by
  unfold adCommon savedFrame
  rw [regsAt_listNthFrame]
  repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj

/-- The clobbered temporaries left owned on return, plus the zero register and
    the still-live `x15` (the `code_hash` output pointer `a5`, framed ambient
    from the prologue and never restored).  Common to both returns. -/
def adScratch (codeOut : Word) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
  regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x15 : Reg) ↦ᵣ codeOut)

theorem pcFree_adScratch (codeOut : Word) : (adScratch codeOut).pcFree := by
  unfold adScratch
  repeat' first | exact pcFree_regIs | exact pcFree_regOwn | apply pcFree_sepConj

/-- The mutable leftover after a failure return: the whole output struct
    (contents forgotten, ownership retained: the 8-byte nonce cell and the three
    32-byte regions), the input region, the two guest data cells, the clobbered
    temporaries, and the reclaimed 8-cell K20 scratch stack. -/
def adFailLeftover (spW nonceOut balanceOut rootOut codeOut listBase : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  fun h => ∃ (n roff rlen : Word) (bal root code : List (BitVec 8)),
    ((nonceOut ↦ₘ n) ** bytesRegion balanceOut bal ** bytesRegion rootOut root **
     bytesRegion codeOut code ** bytesRegion listBase bytes **
     (adOffsetAddr ↦ₘ roff) ** (adLengthAddr ↦ₘ rlen) ** stackFree spW 8 **
     adScratch codeOut) h

theorem pcFree_adFailLeftover (spW nonceOut balanceOut rootOut codeOut listBase : Word)
    (bytes : List (BitVec 8)) :
    (adFailLeftover spW nonceOut balanceOut rootOut codeOut listBase bytes).pcFree := by
  intro h hp
  obtain ⟨_, _, _, _, _, _, hbody⟩ := hp
  revert h hbody
  show Assertion.pcFree _
  repeat' first
    | exact pcFree_memIs | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
    | exact pcFree_adScratch _ | apply pcFree_sepConj

/-- The output-struct leftover after a success return: each cell tied to the
    genuinely decoded field value (`outputSuccess`), the untouched input region,
    the two guest data cells, the clobbered temporaries, and the reclaimed
    scratch stack. -/
def adSuccessOut (spW nonceOut balanceOut rootOut codeOut listBase o0 o1 o2 o3 : Word)
    (l0 l1 l2 l3 : Nat) (bytes oldRoot oldCode : List (BitVec 8)) : Assertion :=
  fun h => ∃ (roff rlen : Word),
    (outputSuccess nonceOut balanceOut rootOut codeOut o0 o1 o2 o3 l0 l1 l2 l3
       bytes oldRoot oldCode **
     bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ roff) ** (adLengthAddr ↦ₘ rlen) **
     stackFree spW 8 ** adScratch codeOut) h

/-- The whole-program post: `a0 = 0` with the genuine decoded output struct, or
    `a0 = 1` with a witnessed `DecodeFailure` and the owned leftover. -/
def adWholePost (sp0 spW : Word) (saved : Saved) (listBase : Word)
    (listLen : Nat) (bytes oldRoot oldCode : List (BitVec 8)) : Assertion :=
  fun h =>
    (∃ (o0 l0 o1 l1 o2 l2 o3 l3 : Word),
      ((⌜Decoded bytes listBase listLen o0 l0 o1 l1 o2 l2 o3 l3⌝ : Assertion) **
       (((.x10 : Reg) ↦ᵣ (0 : Word)) ** adCommon sp0 spW saved **
        adSuccessOut spW saved.s2 saved.s3 saved.s4 saved.s5 listBase o0 o1 o2 o3
          l0.toNat l1.toNat l2.toNat l3.toNat bytes oldRoot oldCode)) h) ∨
    (((⌜DecodeFailure bytes listBase listLen⌝ : Assertion) **
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** adCommon sp0 spW saved **
       adFailLeftover spW saved.s2 saved.s3 saved.s4 saved.s5 listBase bytes)) h)

/-! ## Failure-tail arm -/

set_option maxRecDepth 8000 in
/-- Generic fail arm: from a reshaped fail-pre — the restored-caller frame
    (`x2 ↦ spW`, `regsOwnAt` and the saved frame slots), the pure `⌜DecodeFailure⌝`
    and the owned leftover as the preserved footprint, and an owned `x10` — the
    failure tail (`AB+504 → saved.ra`) lands the whole-program failure post.
    Every fail edge (all four K20 dispatch fails and all four length-check fails)
    reduces to this after its own PRE reshape. -/
theorem adFailArm (sp0 spW : Word) (saved : Saved) (listBase : Word)
    (bytes oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin (1 + 9) (AB + 504) saved.ra fullCode
      (((((.x2 : Reg) ↦ᵣ spW) ** regsOwnAt listNthFrame ** savedFrame spW saved) **
        ((⌜DecodeFailure bytes listBase listLen⌝ : Assertion) **
         adFailLeftover spW saved.s2 saved.s3 saved.s4 saved.s5 listBase bytes)) **
       regOwn .x10)
      (adWholePost sp0 spW saved listBase listLen bytes oldRoot oldCode) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v10 => ?_)
  have hepi := adFailEpi sp0 spW v10 saved
    ((⌜DecodeFailure bytes listBase listLen⌝ : Assertion) **
      adFailLeftover spW saved.s2 saved.s3 saved.s4 saved.s5 listBase bytes)
    (pcFree_sepConj pcFree_pure (pcFree_adFailLeftover _ _ _ _ _ _ _)) hspW hret
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => Or.inr ?_) hepi
  -- hq : ((x10↦1) ** ((x2↦sp0) ** regsAt ** savedFrame) ** (⌜DF⌝ ** adFailLeftover)) h
  -- goal : (⌜DF⌝ ** ((x10↦1) ** adCommon ** adFailLeftover)) h
  unfold adCommon
  xperm_hyp hq

#print axioms adFailArm

/-! ## Continue-edge reshape (K20 boundary)

    A field's K20 dispatch continue exit (`adK20ContPost`, status `0`) keeps a
    genuine `Success` decode.  The reshape below exposes the length-check pre
    (the three temporaries `x5/x6/x7` and the `ad_length` cell) and folds
    everything else — the seven saved registers, the K20 scratch stack, the
    still-live status/temporaries, the input region and the `ad_offset` cell,
    together with the pinned field `Success` — into the ambient frame
    `adContFrame`, threaded unchanged through the length check. -/

/-- The ambient continue frame carried across a field's length check. -/
def adContFrame (spW listBase : Word) (index : Nat) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) (offset len v11 v12 : Word) : Assertion :=
  (⌜Success bytes listBase listLen index offset len⌝ : Assertion) **
  ((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8 **
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
  regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  (adOffsetAddr ↦ₘ offset)

theorem pcFree_adContFrame (spW listBase : Word) (index : Nat) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) (offset len v11 v12 : Word) :
    (adContFrame spW listBase index saved bytes listLen offset len v11 v12).pcFree := by
  unfold adContFrame
  rw [regsAt_listNthFrame]
  repeat' first
    | exact pcFree_pure | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_regOwn
    | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj

set_option maxRecDepth 8000 in
/-- CONT reshape: a field's `adK20ContPost` body (a status-`0` `Success` payload,
    with the three length-check temporaries `x5/x6/x7` already exposed as the
    fresh values `v5/v6/v7`) reshapes into the length-check pre plus the ambient
    continue frame.  Generic over the field index — every continue edge uses it. -/
theorem adContReshape (spW listBase : Word) (index : Nat) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) (offset len v11 v12 v5 v6 v7 : Word) : ∀ h,
    ((⌜Success bytes listBase listLen index offset len⌝ : Assertion) **
     ((((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x7 : Reg) ↦ᵣ v7) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len)))) h →
    ((((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      (adLengthAddr ↦ₘ len)) **
     adContFrame spW listBase index saved bytes listLen offset len v11 v12) h := by
  intro h hp
  unfold adContFrame
  xperm_hyp hp

#print axioms adContReshape

end EvmAsm.Codegen.AccountDecodeSpec
