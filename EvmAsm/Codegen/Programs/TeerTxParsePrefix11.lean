/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix11

  PASS 6 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The `rlp_walk_init` dispatch GROUP recipe — the 3-arm analogue of the
  `rlp_walk_next` group (module 10).  The `rlp_walk_init` callee post is the
  THREE-arm disjunction

      (short-list cursor, a2 = 0) ∨ (long-list cursor, a2 = 0)
        ∨ (∃ cur endp st, a2 = st ≠ 0)

  — TWO success arms (short/long RLP list header) both pinning `a2 = 0`, plus a
  parse-shape failure arm pinning `a2 = st ≠ 0`.  The post-call `bne a2, 0`
  therefore routes BOTH success arms to the fall-through (carrying the
  short/long disjunction forward) and the failure arm to the far epilogue
  `teerB + 2856` (`teerFail`).

  The site-abstract combinator `teer_walkinit_group_gen` (parameterised by the
  call / callee-return (mid) / fall PCs, the two success cursors `cur1`/`cur2`
  and the shared list end `endc`) takes the site's CALL triple and the
  post-call dispatch family and produces the routed group.  Instantiated at all
  three walk-init sites: 54 (inner-payload to/value walk), 110 (past-`to`
  re-init), 176 (authorization_list walk seeding the per-auth loop).

  The forward fall post keeps the short/long disjunction; pinning it to a single
  concrete cursor (the `bytesRegion` sub-range bridge) is deferred to the chain
  composition, where the per-walk concrete-RLP-structure hypotheses are in
  scope.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix10

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000 in
/-- **Site-abstract `rlp_walk_init` dispatch group.**  Chains the site's
    `rlp_walk_init` CALL triple (`hcall`, abstract pre `P`, 3-arm post) into the
    parse-shape `bne a2, 0` family (`hbneFam`, `midPC → {2856, fallPC}`), routing
    the two success arms (short/long list, `a2 = 0`) to `fallPC` (carrying the
    disjunction) and the parse-shape failure arm (`a2 = st ≠ 0`) to the far
    epilogue `teerB + 2856` (`teerFail`). -/
theorem teer_walkinit_group_gen
    (callPC midPC fallPC : Word)
    (P : Assertion)
    (listBase : Word) (listBytes : List (BitVec 8))
    (cur1 cur2 endc : Word)
    (hcall : cpsTripleWithin (1 + 81) callPC midPC fullCode P
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (∃ cur endp st : Word,
             (((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) **
                ⌜st ≠ (0 : Word)⌝) h))))))
    (hbneFam : ∀ a2 : Word,
      cpsBranchWithin 1 midPC fullCode
        ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)))
        (teerB + 2856) ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 ≠ (0 : Word)⌝)
        fallPC ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 = (0 : Word)⌝)) :
    cpsBranchWithin ((1 + 81) + 1) callPC fullCode P
      (teerB + 2856) teerFail
      fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h)))) := by
  -- Short-list success arm (a2 = 0 → fall, left disjunct).
  have hArm1 : cpsBranchWithin 1 midPC fullCode
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         ((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word)))))
      (teerB + 2856) teerFail fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h)))) := by
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ midPC) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** bytesRegion listBase listBytes) **
        (.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc))
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_pure
          | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (hbneFam (0 : Word))
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ _ => trivial) (fun h hq => ?_) hbneF
    obtain ⟨hA, hB, hdAB, huAB, hbne, hF⟩ := hq
    obtain ⟨hA1, hA2, hdA, huA, hx12, hrest⟩ := hbne
    have hx0 : (.x0 ↦ᵣ (0 : Word)) hA2 := ((sepConj_pure_right hA2).1 hrest).1
    have hq' : (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x1 ↦ᵣ midPC) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** bytesRegion listBase listBytes) **
          (.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc))) h :=
      ⟨hA, hB, hdAB, huAB, ⟨hA1, hA2, hdA, huA, hx12, hx0⟩, hF⟩
    have hq2 : ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         ((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))))) h := by
      xperm_hyp hq'
    exact sepConj_mono_right (sepConj_mono_right (fun _ hb => Or.inl hb)) h hq2
  -- Long-list success arm (a2 = 0 → fall, right disjunct).
  have hArm2 : cpsBranchWithin 1 midPC fullCode
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         ((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word)))))
      (teerB + 2856) teerFail fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h)))) := by
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ midPC) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** bytesRegion listBase listBytes) **
        (.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc))
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_pure
          | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (hbneFam (0 : Word))
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ _ => trivial) (fun h hq => ?_) hbneF
    obtain ⟨hA, hB, hdAB, huAB, hbne, hF⟩ := hq
    obtain ⟨hA1, hA2, hdA, huA, hx12, hrest⟩ := hbne
    have hx0 : (.x0 ↦ᵣ (0 : Word)) hA2 := ((sepConj_pure_right hA2).1 hrest).1
    have hq' : (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x1 ↦ᵣ midPC) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** bytesRegion listBase listBytes) **
          (.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc))) h :=
      ⟨hA, hB, hdAB, huAB, ⟨hA1, hA2, hdA, huA, hx12, hx0⟩, hF⟩
    have hq2 : ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         ((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))))) h := by
      xperm_hyp hq'
    exact sepConj_mono_right (sepConj_mono_right (fun _ hb => Or.inr hb)) h hq2
  -- Parse-shape failure arm (a2 = st ≠ 0 → epilogue; fall unreachable).
  have hFailFam : ∀ cur endp st : Word,
      cpsBranchWithin 1 midPC fullCode
        ((.x1 ↦ᵣ midPC) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
           ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) ** ⌜st ≠ (0 : Word)⌝)))
        (teerB + 2856) teerFail fallPC
        ((.x1 ↦ᵣ midPC) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase listBytes) **
           (fun h =>
             (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
             (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h)))) := by
    intro cur endp st
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ midPC) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** bytesRegion listBase listBytes) **
        (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** ⌜st ≠ (0 : Word)⌝)
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_pure
          | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (hbneFam st)
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ _ => trivial) (fun h hq => ?_) hbneF
    exfalso
    obtain ⟨hA, hB, _, _, hbne, hF⟩ := hq
    obtain ⟨_, hC, _, _, _, hbne2⟩ := hbne
    have h0 : st = (0 : Word) := ((sepConj_pure_right hC).1 hbne2).2
    obtain ⟨_, _, _, _, _, hF1⟩ := hF
    obtain ⟨_, _, _, _, _, hF2⟩ := hF1
    obtain ⟨_, hI, _, _, _, hF3⟩ := hF2
    exact absurd h0 ((sepConj_pure_right hI).1 hF3).2
  have hFailArm : cpsBranchWithin 1 midPC fullCode
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h => ∃ cur endp st : Word,
           ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) ** ⌜st ≠ (0 : Word)⌝) h)))
      (teerB + 2856) teerFail fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h)))) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_exists_pre (fun cur =>
        cpsBranchWithin_exists_pre (fun endp =>
          cpsBranchWithin_exists_pre (fun st => hFailFam cur endp st))))
    obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hr2, hfl⟩ := hp
    obtain ⟨cur, endp, st, hbody⟩ := hfl
    exact ⟨cur, endp, st, h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hr2, hbody⟩
  -- Recombine the three arms and sequence the call before the routed branch.
  have hbr : cpsBranchWithin 1 midPC fullCode
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (∃ cur endp st : Word,
             ((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) **
                ⌜st ≠ (0 : Word)⌝) h))))
      (teerB + 2856) teerFail fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ cur1) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ cur2) ** (.x11 ↦ᵣ endc) ** (.x12 ↦ᵣ (0 : Word))) h)))) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pre_or hArm1 (cpsBranchWithin_pre_or hArm2 hFailArm))
    obtain ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hframe, hdisj⟩ := hp
    rcases hdisj with ha1 | ha2 | haf
    · exact Or.inl ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hframe, ha1⟩
    · exact Or.inr (Or.inl ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hframe, ha2⟩)
    · exact Or.inr (Or.inr ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hframe, haf⟩)
  exact cpsTripleWithin_seq_branch_same_cr hcall hbr

/-! ## Walk-init dispatch groups — sites 54 / 110 / 176 -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_init`@54 dispatch group (`teerB + 216 → {2856, 224}`).
    Routes the short/long list success arms to the fall-through (carrying the
    disjunction) and the parse-shape failure arm to `teerFail`. -/
theorem teer_walkinit54_group_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    cpsBranchWithin ((1 + 81) + 1) (teerB + 216) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      (teerB + 2856) teerFail
      (teerB + 224)
      ((.x1 ↦ᵣ (teerB + 220)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word))) h)))) :=
  teer_walkinit_group_gen (teerB + 216) (teerB + 220) (teerB + 224) _
    listBase listBytes
    ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
    ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))
    ((listBase + BitVec.ofNat 64 listOff) + listLen)
    (teer_walkinit54_call_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn listBytes listOff halign hoff hover hvalid)
    teer_walkinit55_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_init`@110 dispatch group (`teerB + 440 → {2856, 448}`).
    Routes the short/long list success arms to the fall-through (carrying the
    disjunction) and the parse-shape failure arm to `teerFail`. -/
theorem teer_walkinit110_group_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    cpsBranchWithin ((1 + 81) + 1) (teerB + 440) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      (teerB + 2856) teerFail
      (teerB + 448)
      ((.x1 ↦ᵣ (teerB + 444)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word))) h)))) :=
  teer_walkinit_group_gen (teerB + 440) (teerB + 444) (teerB + 448) _
    listBase listBytes
    ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
    ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))
    ((listBase + BitVec.ofNat 64 listOff) + listLen)
    (teer_walkinit110_call_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn listBytes listOff halign hoff hover hvalid)
    teer_walkinit111_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_init`@176 dispatch group (`teerB + 704 → {2856, 712}`).
    Routes the short/long list success arms to the fall-through (carrying the
    disjunction) and the parse-shape failure arm to `teerFail`. -/
theorem teer_walkinit176_group_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    cpsBranchWithin ((1 + 81) + 1) (teerB + 704) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      (teerB + 2856) teerFail
      (teerB + 712)
      ((.x1 ↦ᵣ (teerB + 708)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word))) h)))) :=
  teer_walkinit_group_gen (teerB + 704) (teerB + 708) (teerB + 712) _
    listBase listBytes
    ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
    ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))
    ((listBase + BitVec.ofNat 64 listOff) + listLen)
    (teer_walkinit176_call_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn listBytes listOff halign hoff hover hvalid)
    teer_walkinit177_bne_spec

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
