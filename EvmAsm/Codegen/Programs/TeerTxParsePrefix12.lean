/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix12

  PASS 6 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The `rlp_list_count_items`@169 dispatch GROUP (`teerB + 676 → {2856, 684}`).
  Chains the count CALL triple (`teer_count169_call_spec`) into the post-call
  `bne a0, 0` (`teer_count170_bne_spec`), routing the two-arm callee post

      (∃ cnt, countModel = some cnt ∧ (a0 = 0, out cell := cnt))
        ∨ (countModel = none ∧ ∃ st, a0 = st ≠ 0)

  — a success arm (a0 = 0, count written to `teer_auth_count`) and a parse
  failure arm (a0 = st ≠ 0).  The `bne a0, 0` routes the success arm to the
  fall-through `teerB + 684` (the count load into `x23`) and the failure arm to
  the far epilogue `teerB + 2856` (`teerFail`).

  Unlike the walk groups, the success arm's `countModel = some cnt` fact sits
  OUTSIDE the sepConj (a leading `∧`); it is bridged to the `⌜⌝`-form via
  `sepConj_pure_left` so the usual `xperm` machinery applies.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix11
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000 in
/-- **`rlp_list_count_items`@169 dispatch group** (`teerB + 676 → {2856, 684}`).
    Routes the count success arm (`a0 = 0`, `teer_auth_count := cnt`) to the
    fall-through and the parse-failure arm (`a0 = st ≠ 0`) to `teerFail`. -/
theorem teer_count169_group_spec (rc : RlpListCountItemsAssumed fullCode)
    (hrc : rc.entry = BitVec.ofNat 64 GuestAddrs.rlp_list_count_items)
    (listBase outPtr outOld t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listLen : Nat)
    (halign : listBase.toNat % 8 = 0)
    (hbound : listLen ≤ listBytes.length)
    (hover : listBase.toNat + listBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < listBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin ((1 + nRlpListCountItemsSteps) + 1) (teerB + 676) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ outPtr) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes ** (outPtr ↦ₘ outOld)))
      (teerB + 2856) teerFail
      (teerB + 684)
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           ∃ cnt, rc.countModel listBytes listLen = some cnt ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt)) h)))) := by
  have hcall := teer_count169_call_spec rc hrc listBase outPtr outOld t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn listBytes listLen halign hbound hover hvalid
  -- Success arm (a0 = 0 → fall).
  have hOkFam : ∀ cnt : Word,
      cpsBranchWithin 1 (teerB + 680) fullCode
        ((.x1 ↦ᵣ (teerB + 680)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
           (fun h => rc.countModel listBytes listLen = some cnt ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt)) h))))
        (teerB + 2856) teerFail (teerB + 684)
        ((.x1 ↦ᵣ (teerB + 680)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
           (fun h => ∃ cnt', rc.countModel listBytes listLen = some cnt' ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt')) h)))) := by
    intro cnt
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ (teerB + 680)) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 **
          bytesRegion listBase listBytes) **
        (outPtr ↦ₘ cnt) ** ⌜rc.countModel listBytes listLen = some cnt⌝)
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
          | exact pcFree_pure | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (teer_count170_bne_spec (0 : Word))
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ _ => trivial) (fun h hq => ?_) hbneF
    · -- pre: ∧-form → ⌜⌝-form, then xperm into the bne frame.
      have hp2 : ((.x1 ↦ᵣ (teerB + 680)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
           (⌜rc.countModel listBytes listLen = some cnt⌝ **
             ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt))))) h :=
        sepConj_mono_right (sepConj_mono_right
          (fun s hs => (sepConj_pure_left s).2 hs)) h hp
      xperm_hyp hp2
    · -- fall post: strip ⌜0=0⌝, rebuild ∧-form, inject ∃ cnt'.
      obtain ⟨hA, hB, hdAB, huAB, hbne, hF⟩ := hq
      obtain ⟨hA1, hA2, hdA, huA, hx10, hrest⟩ := hbne
      have hx0 : (.x0 ↦ᵣ (0 : Word)) hA2 := ((sepConj_pure_right hA2).1 hrest).1
      have hq' : (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x1 ↦ᵣ (teerB + 680)) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 **
              bytesRegion listBase listBytes) **
            (outPtr ↦ₘ cnt) ** ⌜rc.countModel listBytes listLen = some cnt⌝)) h :=
        ⟨hA, hB, hdAB, huAB, ⟨hA1, hA2, hdA, huA, hx10, hx0⟩, hF⟩
      have hq2 : ((.x1 ↦ᵣ (teerB + 680)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
           (⌜rc.countModel listBytes listLen = some cnt⌝ **
             ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt))))) h := by
        xperm_hyp hq'
      refine sepConj_mono_right (sepConj_mono_right (fun s hs => ?_)) h hq2
      exact ⟨cnt, (sepConj_pure_left s).1 hs⟩
  have hOkArm : cpsBranchWithin 1 (teerB + 680) fullCode
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h => ∃ cnt, rc.countModel listBytes listLen = some cnt ∧
           (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt)) h))))
      (teerB + 2856) teerFail (teerB + 684)
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h => ∃ cnt', rc.countModel listBytes listLen = some cnt' ∧
           (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt')) h)))) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_exists_pre (fun cnt => hOkFam cnt))
    obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hframe, hbody⟩ := hp
    obtain ⟨cnt, hcnt, hsep⟩ := hbody
    exact ⟨cnt, h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hframe, hcnt, hsep⟩
  -- Failure arm (a0 = st ≠ 0 → epilogue; fall unreachable).
  have hFailFam : ∀ st : Word,
      cpsBranchWithin 1 (teerB + 680) fullCode
        ((.x1 ↦ᵣ (teerB + 680)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
           ((.x10 ↦ᵣ st) ** memOwn outPtr ** ⌜st ≠ (0 : Word)⌝)))
        (teerB + 2856) teerFail (teerB + 684)
        ((.x1 ↦ᵣ (teerB + 680)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
           (fun h => ∃ cnt', rc.countModel listBytes listLen = some cnt' ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt')) h)))) := by
    intro st
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ (teerB + 680)) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 **
          bytesRegion listBase listBytes) **
        memOwn outPtr ** ⌜st ≠ (0 : Word)⌝)
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memOwn
          | exact pcFree_pure | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (teer_count170_bne_spec st)
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ _ => trivial) (fun h hq => ?_) hbneF
    exfalso
    obtain ⟨hA, hB, _, _, hbne, hF⟩ := hq
    obtain ⟨_, hC, _, _, _, hbne2⟩ := hbne
    have h0 : st = (0 : Word) := ((sepConj_pure_right hC).1 hbne2).2
    obtain ⟨_, _, _, _, _, hF1⟩ := hF
    obtain ⟨_, hI, _, _, _, hF2⟩ := hF1
    exact absurd h0 ((sepConj_pure_right hI).1 hF2).2
  have hFailArm : cpsBranchWithin 1 (teerB + 680) fullCode
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h => rc.countModel listBytes listLen = none ∧
           (∃ st, ((.x10 ↦ᵣ st) ** memOwn outPtr ** ⌜st ≠ (0 : Word)⌝) h))))
      (teerB + 2856) teerFail (teerB + 684)
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h => ∃ cnt', rc.countModel listBytes listLen = some cnt' ∧
           (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt')) h)))) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_exists_pre (fun st => hFailFam st))
    obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hframe, hbody⟩ := hp
    obtain ⟨_, st, hsep⟩ := hbody
    exact ⟨st, h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hframe, hsep⟩
  -- Recombine and sequence the call before the routed branch.
  have hbr : cpsBranchWithin 1 (teerB + 680) fullCode
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (∃ cnt, rc.countModel listBytes listLen = some cnt ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt)) h)) ∨
           (rc.countModel listBytes listLen = none ∧
             (∃ st, ((.x10 ↦ᵣ st) ** memOwn outPtr ** ⌜st ≠ (0 : Word)⌝) h)))))
      (teerB + 2856) teerFail (teerB + 684)
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h => ∃ cnt', rc.countModel listBytes listLen = some cnt' ∧
           (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt')) h)))) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pre_or hOkArm hFailArm)
    obtain ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hframe, hdisj⟩ := hp
    rcases hdisj with hok | hfl
    · exact Or.inl ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hframe, hok⟩
    · exact Or.inr ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hframe, hfl⟩
  exact cpsTripleWithin_seq_branch_same_cr hcall hbr

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
