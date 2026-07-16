/-
  `withdrawalDecode_prog` caller-contract composition, part 3.

  This module hosts the four post-call status dispatches ([13], [19], [28],
  [50]) and the final 4-way compose into `withdrawal_decode_spec_within`.

  Each field call returns the merged callee's `flatPost` / `flatReturnResult`
  disjunction.  A `BNE x10, x0` at the dispatch routes the status word: a
  nonzero status (RLP parse failure, or a K34 status ≠ 0) branches to the
  common failure tail (`WB+212`); status `0` continues.  The dispatches are
  modelled on `HeaderExtractNumberSpec.hdrEpilogue`'s `flatPost` case-split,
  adding the branch routing.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.WithdrawalDecodeClose2

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64SAsm

/-! ## K34 status-dispatch post-conditions

    A K34 field call (`rlp_field_to_u64`, fields 0/1/3) exposes `flatPost`, a
    disjunction of `flatSuccessReturned` (status = `wrapperStatus`, pinned by a
    `Result`) and `flatFailureReturned` (status = `1`, `Result … 1 0`).  After
    the `BNE x10, x0`:

    * the **continue** exit keeps the success payload with the status pinned to
      `0` (the genuine per-field decode); and
    * the **fail** exit keeps whichever payload witnessed a nonzero status —
      either a success payload with `wrapperStatus ≠ 0`, or the failure payload
      (`status = 1`).  Both retain the callee `Result`, so the compose can name
      the exact failing stage. -/

/-- Continue-exit post (status `0`) of a K34 field dispatch. -/
def k34ContPost (spW newSp listBase raRet : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 x5 ss ov,
    ((.x1 ↦ᵣ raRet) **
     (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
       savedFrame newSp outer) **
      successPayload newSp listBase offset len v12 x5 ss (0 : Word) ov saved
        bytes listLen index)) h

/-- Fail-exit post of a K34 field dispatch: either a success payload with a
    nonzero wrapper status, or the failure payload. -/
def k34FailPost (spW newSp listBase oldOffset oldLen raRet : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h =>
    (∃ offset len v12 x5 ss ws ov,
      ((⌜ws ≠ (0 : Word)⌝ : Assertion) **
       ((.x1 ↦ᵣ raRet) **
        (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
          savedFrame newSp outer) **
         successPayload newSp listBase offset len v12 x5 ss ws ov saved
           bytes listLen index))) h) ∨
    (∃ v11 v12,
      ((.x1 ↦ᵣ raRet) **
       (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
         savedFrame newSp outer) **
        failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
          listLen index)) h)

set_option maxRecDepth 8000 in
/-- Generic K34 post-call status dispatch: after a `flatPost`, the `BNE x10, x0`
    at `bnePc` routes a nonzero status to `failTarget` and status `0` to
    `contTarget`. -/
theorem k34Dispatch (spW newSp listBase oldOffset oldLen raRet : Word)
    (outer : Saved) (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (bnePc failTarget contTarget : Word) (boff : BitVec 13)
    (hmem : ∀ a i, CodeReq.singleton bnePc (.BNE .x10 .x0 boff) a = some i →
      fullCode a = some i)
    (hfail : bnePc + signExtend13 boff = failTarget)
    (hcont : bnePc + 4 = contTarget) :
    cpsBranchWithin 1 bnePc fullCode
      ((.x1 ↦ᵣ raRet) **
       flatPost spW newSp listBase oldOffset oldLen outer saved bytes listLen index)
      failTarget
        (k34FailPost spW newSp listBase oldOffset oldLen raRet outer saved bytes
          listLen index)
      contTarget
        (k34ContPost spW newSp listBase raRet outer saved bytes listLen index) := by
  -- Success arm.
  have hbrS : cpsBranchWithin 1 bnePc fullCode
      ((.x1 ↦ᵣ raRet) **
       flatSuccessReturned spW newSp listBase outer saved bytes listLen index)
      failTarget
        (k34FailPost spW newSp listBase oldOffset oldLen raRet outer saved bytes
          listLen index)
      contTarget
        (k34ContPost spW newSp listBase raRet outer saved bytes listLen index) := by
    refine cpsBranchWithin_weaken (P := fun h => ∃ offset len v12 x5 ss ws ov,
        ((.x1 ↦ᵣ raRet) **
         (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
           savedFrame newSp outer) **
          successPayload newSp listBase offset len v12 x5 ss ws ov saved
            bytes listLen index)) h)
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hx1, ⟨o, l, v12, x5, ss, ws, ov, hG⟩⟩ := hp
        exact ⟨o, l, v12, x5, ss, ws, ov, h1, h2, hd, hu, hx1, hG⟩)
      (fun _ hq => hq) (fun _ hq => hq) ?_
    refine cpsBranchWithin_exists_pre (fun offset => ?_)
    refine cpsBranchWithin_exists_pre (fun len => ?_)
    refine cpsBranchWithin_exists_pre (fun v12 => ?_)
    refine cpsBranchWithin_exists_pre (fun x5 => ?_)
    refine cpsBranchWithin_exists_pre (fun ss => ?_)
    refine cpsBranchWithin_exists_pre (fun ws => ?_)
    refine cpsBranchWithin_exists_pre (fun ov => ?_)
    -- The rest of the pre, besides x10 and x0.
    let REST : Assertion :=
      (.x1 ↦ᵣ raRet) **
      (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
        savedFrame newSp outer) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion listBase bytes **
        (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) **
        (.x21 ↦ᵣ saved.s5) ** stackFree newSp 8 ** (.x12 ↦ᵣ v12) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) ** (.x5 ↦ᵣ x5) **
        (.x11 ↦ᵣ ss) ** (saved.s1 ↦ₘ ov)) **
       ⌜Result bytes listBase listLen index ws ov⌝)
    have hbne := bne_spec_gen_within .x10 .x0 boff ws (0 : Word) bnePc
    rw [hfail, hcont] at hbne
    have hbneL := cpsBranchWithin_extend_code hmem hbne
    have hbneF := cpsBranchWithin_frameR REST (by unfold REST; pcf) hbneL
    refine cpsBranchWithin_weaken (fun h hp => by
        unfold REST
        unfold successPayload at hp
        xperm_hyp hp)
      (fun h hq => by
        -- taken: ws ≠ 0.
        refine Or.inl ⟨offset, len, v12, x5, ss, ws, ov, ?_⟩
        unfold REST at hq
        unfold successPayload
        xperm_hyp hq)
      (fun h hq => by
        -- not-taken: ws = 0.
        refine ⟨offset, len, v12, x5, ss, ov, ?_⟩
        unfold REST at hq
        have hz : ws = (0 : Word) := by
          obtain ⟨h1, h2, hd, hu, hA, hR⟩ := hq
          obtain ⟨h3, h4, hd2, hu2, hx10, hrest⟩ := hA
          exact ((sepConj_pure_right h4).1 hrest).2
        subst hz
        unfold successPayload
        obtain ⟨h1, h2, hd, hu, hA, hR⟩ := hq
        obtain ⟨h3, h4, hd2, hu2, hx10, hrest⟩ := hA
        have hx0 : ((.x0 : Reg) ↦ᵣ (0 : Word)) h4 := ((sepConj_pure_right h4).1 hrest).1
        have hq' : (((.x10 ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** _) h :=
          ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hx10, hx0⟩, hR⟩
        xperm_hyp hq')
      hbneF
  -- Failure arm.
  have hbrF : cpsBranchWithin 1 bnePc fullCode
      ((.x1 ↦ᵣ raRet) **
       flatFailureReturned spW newSp listBase oldOffset oldLen outer saved bytes
         listLen index)
      failTarget
        (k34FailPost spW newSp listBase oldOffset oldLen raRet outer saved bytes
          listLen index)
      contTarget
        (k34ContPost spW newSp listBase raRet outer saved bytes listLen index) := by
    refine cpsBranchWithin_weaken (P := fun h => ∃ v11 v12,
        ((.x1 ↦ᵣ raRet) **
         (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
           savedFrame newSp outer) **
          failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
            listLen index)) h)
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hx1, ⟨v11, v12, hG⟩⟩ := hp
        exact ⟨v11, v12, h1, h2, hd, hu, hx1, hG⟩)
      (fun _ hq => hq) (fun _ hq => hq) ?_
    refine cpsBranchWithin_exists_pre (fun v11 => ?_)
    refine cpsBranchWithin_exists_pre (fun v12 => ?_)
    let REST : Assertion :=
      (.x1 ↦ᵣ raRet) **
      (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
        savedFrame newSp outer) **
       (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
        (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree newSp 8 **
        bytesRegion listBase bytes ** (offsetCell ↦ₘ oldOffset) **
        (lengthCell ↦ₘ oldLen) ** (saved.s1 ↦ₘ (0 : Word))) **
       ⌜Result bytes listBase listLen index 1 0⌝)
    have hbne := bne_spec_gen_within .x10 .x0 boff (1 : Word) (0 : Word) bnePc
    rw [hfail, hcont] at hbne
    have hbneL := cpsBranchWithin_extend_code hmem hbne
    have hbneF := cpsBranchWithin_frameR REST (by unfold REST; pcf) hbneL
    refine cpsBranchWithin_weaken (fun h hp => by
        unfold REST
        unfold failurePayload at hp
        xperm_hyp hp)
      (fun h hq => by
        refine Or.inr ⟨v11, v12, ?_⟩
        unfold REST at hq
        unfold failurePayload
        obtain ⟨h1, h2, hd, hu, hA, hR⟩ := hq
        obtain ⟨h3, h4, hd2, hu2, hx10, hrest⟩ := hA
        have hx0 : ((.x0 : Reg) ↦ᵣ (0 : Word)) h4 := ((sepConj_pure_right h4).1 hrest).1
        have hq' : (((.x10 ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** _) h :=
          ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hx10, hx0⟩, hR⟩
        xperm_hyp hq')
      (fun h hq => by
        exfalso
        have hz : (1 : Word) = (0 : Word) := by
          obtain ⟨h1, h2, hd, hu, hA, hR⟩ := hq
          obtain ⟨h3, h4, hd2, hu2, hx10, hrest⟩ := hA
          exact ((sepConj_pure_right h4).1 hrest).2
        exact absurd hz (by decide))
      hbneF
  -- Combine the two arms over `flatPost`.
  have hor := cpsBranchWithin_pre_or hbrS hbrF
  refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq) hor
  unfold flatPost at hp
  exact sepConj_or_split h hp

#print axioms k34Dispatch

/-! ## K20 (field-2) status-dispatch post-conditions

    The address field is decoded by `rlp_list_nth_item` (K20), whose call
    adapter exposes `flatReturnResult`: a single existential over the returned
    `status`/`offset`/`length` with a pinned `Result`.  After the `BNE x10, x0`
    at [28]:

    * status `0` continues (`contTarget`), the selected content offset/length
      written to the `wd_offset`/`wd_length` cells and a `Success` pinned; and
    * a nonzero status (`1`) fails (`failTarget`), with the K20 `Failure`
      pinned. -/

open EvmAsm.Codegen.RlpListNthItemSAsm (listNthFrame savedVals regsAt_listNthFrame
  Success Failure flatReturnResult)

/-- Continue-exit post (status `0`) of the field-2 K20 dispatch. -/
def k20ContPost (spW listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    ((⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 offset
        len⌝ : Assertion) **
     ((((.x2 ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
       ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (wdOffsetAddr ↦ₘ offset) ** (wdLengthAddr ↦ₘ len))))) h

/-- Fail-exit post (nonzero status) of the field-2 K20 dispatch. -/
def k20FailPost (spW listBase oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    ((⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen 2 oldOffset
        oldLen status offset len ∧ status ≠ (0 : Word)⌝ : Assertion) **
     ((((.x2 ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
       ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (wdOffsetAddr ↦ₘ offset) ** (wdLengthAddr ↦ₘ len))))) h

set_option maxRecDepth 8000 in
/-- Field-2 (K20) post-call status dispatch at [28] (`WB+112`): route the
    `rlp_list_nth_item` status to the failure tail (`WB+212`) on nonzero, or to
    the length check (`WB+116`) on status `0`. -/
theorem k20Dispatch (spW listBase oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) :
    cpsBranchWithin 1 (WB + 112) fullCode
      (flatReturnResult spW listBase (2 : Word) wdOffsetAddr wdLengthAddr oldOffset
        oldLen saved bytes listLen 2)
      (WB + 212) (k20FailPost spW listBase oldOffset oldLen saved bytes listLen)
      (WB + 116) (k20ContPost spW listBase saved bytes listLen) := by
  have hmem : ∀ a i, CodeReq.singleton (WB + 112) (.BNE .x10 .x0 (100 : BitVec 13))
      a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 112) withdrawalDecode_prog 28
      (.BNE .x10 .x0 (100 : BitVec 13)) (by bv_omega) (by rw [wd_length]; decide)
      rfl (by rw [wd_length]; decide) a i hi)
  refine cpsBranchWithin_weaken (P := fun h => ∃ status offset len v11 v12,
      ((((.x2 ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
        ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
         (wdOffsetAddr ↦ₘ offset) ** (wdLengthAddr ↦ₘ len))) **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen 2 oldOffset
         oldLen status offset len⌝) h)
    (fun h hp => hp) (fun _ hq => hq) (fun _ hq => hq) ?_
  refine cpsBranchWithin_exists_pre (fun status => ?_)
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  let REST : Assertion :=
    (((.x2 ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
     (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes **
      (wdOffsetAddr ↦ₘ offset) ** (wdLengthAddr ↦ₘ len))) **
    ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen 2 oldOffset
      oldLen status offset len⌝
  have hbne := bne_spec_gen_within .x10 .x0 (100 : BitVec 13) status (0 : Word) (WB + 112)
  rw [show (WB + 112 : Word) + signExtend13 (100 : BitVec 13) = WB + 212 from by
      rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]; bv_omega,
    show (WB + 112 : Word) + 4 = WB + 116 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code hmem hbne
  have hbneF := cpsBranchWithin_frameR REST (by unfold REST; pcf) hbneL
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold REST
      xperm_hyp hp)
    (fun h hq => by
      -- taken: status ≠ 0.
      refine ⟨status, offset, len, v11, v12, ?_⟩
      unfold REST at hq
      obtain ⟨h1, h2, hd, hu, hA, hR⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hx10, hrest⟩ := hA
      have hne : status ≠ (0 : Word) := ((sepConj_pure_right h4).1 hrest).2
      have hx0 : ((.x0 : Reg) ↦ᵣ (0 : Word)) h4 := ((sepConj_pure_right h4).1 hrest).1
      have hbody := ((sepConj_pure_right h2).1 hR).1
      have hres := ((sepConj_pure_right h2).1 hR).2
      apply (sepConj_pure_left h).2
      refine ⟨⟨hres, hne⟩, ?_⟩
      have hq' : (((.x10 ↦ᵣ status) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** _) h :=
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hx10, hx0⟩, hbody⟩
      xperm_hyp hq')
    (fun h hq => by
      -- not-taken: status = 0.
      unfold REST at hq
      obtain ⟨h1, h2, hd, hu, hA, hR⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hx10, hrest⟩ := hA
      have hz : status = (0 : Word) := ((sepConj_pure_right h4).1 hrest).2
      have hx0 : ((.x0 : Reg) ↦ᵣ (0 : Word)) h4 := ((sepConj_pure_right h4).1 hrest).1
      have hres := ((sepConj_pure_right h2).1 hR).2
      have hbody := ((sepConj_pure_right h2).1 hR).1
      have hsucc : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2
          offset len := by
        rw [hz] at hres
        cases hres with
        | ok o l hok => exact hok
      refine ⟨offset, len, v11, v12, ?_⟩
      subst hz
      apply (sepConj_pure_left h).2
      refine ⟨hsucc, ?_⟩
      have hq' : (((.x10 ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** _) h :=
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hx10, hx0⟩, hbody⟩
      xperm_hyp hq')
    hbneF

#print axioms k20Dispatch

/-! ## Per-field stages: field call ;; status dispatch -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
/-- Field-0 stage [8]-[13] (`WB+32`): the field-0 K34 call composed with its
    status dispatch at [13].  Nonzero status → `WB+212`; status `0` → `WB+56`. -/
theorem wdField0Stage
    (spW newSp raIn listBase len outBase oldOut oldOffset oldLen old14
      s3 s4 s5 v10 v11 v12 v13 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let outer : Saved := { ra := WB + 52, s0 := listBase, s1 := len }
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outBase, s2 := outBase, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsBranchWithin (4 + (1 + n34) + 1) (WB + 32) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (outBase ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      (WB + 212)
        (k34FailPost spW newSp listBase oldOffset oldLen (WB + 52) outer saved bytes
          listLen 0)
      (WB + 56)
        (k34ContPost spW newSp listBase (WB + 52) outer saved bytes listLen 0) := by
  intro outer saved callSteps tailSteps n34
  have hcall := wdField0Call spW newSp raIn listBase len outBase oldOut oldOffset
    oldLen old14 s3 s4 s5 v10 v11 v12 v13 bytes listLen hnewSp hlenW hsalign hslack
    hover hvalid
  have hmem : ∀ a i, CodeReq.singleton (WB + 52) (.BNE .x10 .x0 (160 : BitVec 13))
      a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 52) withdrawalDecode_prog 13
      (.BNE .x10 .x0 (160 : BitVec 13)) (by bv_omega) (by rw [wd_length]; decide)
      rfl (by rw [wd_length]; decide) a i hi)
  have hdisp := k34Dispatch spW newSp listBase oldOffset oldLen (WB + 52) outer saved
    bytes listLen 0 (WB + 52) (WB + 212) (WB + 56) (160 : BitVec 13) hmem
    (by rw [show signExtend13 (160 : BitVec 13) = (160 : Word) from by decide]; bv_omega)
    (by bv_omega)
  exact cpsTripleWithin_seq_branch_same_cr hcall hdisp

#print axioms wdField0Stage

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
/-- Field-1 stage [14]-[19] (`WB+56`): field-1 K34 call + dispatch at [19].
    Nonzero status → `WB+212`; status `0` → `WB+80`. -/
theorem wdField1Stage
    (spW newSp raIn listBase len outBase oldOut oldOffset oldLen old14
      s3 s4 s5 v10 v11 v12 v13 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let outer : Saved := { ra := WB + 76, s0 := listBase, s1 := len }
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outBase + 8, s2 := outBase, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsBranchWithin (4 + (1 + n34) + 1) (WB + 56) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        ((outBase + 8) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      (WB + 212)
        (k34FailPost spW newSp listBase oldOffset oldLen (WB + 76) outer saved bytes
          listLen 1)
      (WB + 80)
        (k34ContPost spW newSp listBase (WB + 76) outer saved bytes listLen 1) := by
  intro outer saved callSteps tailSteps n34
  have hcall := wdField1Call spW newSp raIn listBase len outBase oldOut oldOffset
    oldLen old14 s3 s4 s5 v10 v11 v12 v13 bytes listLen hnewSp hlenW hsalign hslack
    hover hvalid
  have hmem : ∀ a i, CodeReq.singleton (WB + 76) (.BNE .x10 .x0 (136 : BitVec 13))
      a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 76) withdrawalDecode_prog 19
      (.BNE .x10 .x0 (136 : BitVec 13)) (by bv_omega) (by rw [wd_length]; decide)
      rfl (by rw [wd_length]; decide) a i hi)
  have hdisp := k34Dispatch spW newSp listBase oldOffset oldLen (WB + 76) outer saved
    bytes listLen 1 (WB + 76) (WB + 212) (WB + 80) (136 : BitVec 13) hmem
    (by rw [show signExtend13 (136 : BitVec 13) = (136 : Word) from by decide]; bv_omega)
    (by bv_omega)
  exact cpsTripleWithin_seq_branch_same_cr hcall hdisp

#print axioms wdField1Stage

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
/-- Field-3 stage [45]-[50] (`WB+180`): field-3 K34 call + dispatch at [50].
    Nonzero status → `WB+212`; status `0` → `WB+204`. -/
theorem wdField3Stage
    (spW newSp raIn listBase len outBase oldOut oldOffset oldLen old14
      s3 s4 s5 v10 v11 v12 v13 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let outer : Saved := { ra := WB + 200, s0 := listBase, s1 := len }
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outBase + 40, s2 := outBase, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsBranchWithin (4 + (1 + n34) + 1) (WB + 180) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        ((outBase + 40) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      (WB + 212)
        (k34FailPost spW newSp listBase oldOffset oldLen (WB + 200) outer saved bytes
          listLen 3)
      (WB + 204)
        (k34ContPost spW newSp listBase (WB + 200) outer saved bytes listLen 3) := by
  intro outer saved callSteps tailSteps n34
  have hcall := wdField3Call spW newSp raIn listBase len outBase oldOut oldOffset
    oldLen old14 s3 s4 s5 v10 v11 v12 v13 bytes listLen hnewSp hlenW hsalign hslack
    hover hvalid
  have hmem : ∀ a i, CodeReq.singleton (WB + 200) (.BNE .x10 .x0 (12 : BitVec 13))
      a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 200) withdrawalDecode_prog 50
      (.BNE .x10 .x0 (12 : BitVec 13)) (by bv_omega) (by rw [wd_length]; decide)
      rfl (by rw [wd_length]; decide) a i hi)
  have hdisp := k34Dispatch spW newSp listBase oldOffset oldLen (WB + 200) outer saved
    bytes listLen 3 (WB + 200) (WB + 212) (WB + 204) (12 : BitVec 13) hmem
    (by rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega)
    (by bv_omega)
  exact cpsTripleWithin_seq_branch_same_cr hcall hdisp

#print axioms wdField3Stage

open EvmAsm.Codegen.RlpListNthItemSAsm in
set_option maxRecDepth 8000 in
/-- Field-2 stage [20]-[28] (`WB+80`): field-2 K20 call + dispatch at [28].
    Nonzero status → `WB+212`; status `0` → `WB+116` (length check). -/
theorem wdField2Stage
    (spW raIn listBase len s2v s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := WB + 112, s0 := listBase, s1 := len, s2 := s2v, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (2 + 2)) + 6)) + 9
    cpsBranchWithin (7 + (1 + n20) + 1) (WB + 80) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (wdOffsetAddr ↦ₘ oldOffset) ** (wdLengthAddr ↦ₘ oldLen))
      (WB + 212) (k20FailPost spW listBase oldOffset oldLen saved bytes listLen)
      (WB + 116) (k20ContPost spW listBase saved bytes listLen) := by
  intro saved n20
  have hcall := wdField2Call spW raIn listBase len s2v s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hdisp := k20Dispatch spW listBase oldOffset oldLen saved bytes listLen
  exact cpsTripleWithin_seq_branch_same_cr hcall hdisp

#print axioms wdField2Stage

/-! ## Frame reshape helpers -/

/-- Generic: saved frame slots weaken to merely-owned slots. -/
private theorem frameSlotsSaved_own (fr : FrameDesc) (newSp : Word) (vals : Reg → Word) :
    ∀ h, frameSlotsSaved fr newSp vals h → frameSlotsOwn fr newSp h := by
  induction fr with
  | nil => intro h hp; simpa only [frameSlotsSaved_nil, frameSlotsOwn_nil] using hp
  | cons p rest ih =>
    intro h hp
    rw [frameSlotsSaved_cons] at hp
    rw [frameSlotsOwn_cons]
    exact sepConj_mono memIs_implies_memOwn ih h hp

/-- K34's saved frame weakens to the merely-owned frame slots (`frameSlotsOwn`),
    the shape each subsequent K34 field call requires. -/
theorem savedFrameK34_own (newSp : Word) (saved : Saved) :
    ∀ h, savedFrame newSp saved h → frameSlotsOwn frame newSp h := by
  intro h hp
  rw [← frameSlotsSaved_frame] at hp
  exact frameSlotsSaved_own frame newSp (savedVals saved) h hp

#print axioms savedFrameK34_own

end EvmAsm.Codegen.WithdrawalDecodeSpec
