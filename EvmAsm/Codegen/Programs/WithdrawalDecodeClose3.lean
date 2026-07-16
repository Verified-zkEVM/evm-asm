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

end EvmAsm.Codegen.WithdrawalDecodeSpec
