/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix10

  PASS 6 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Generalises the disjunctive-routing recipe of `teer_walknext60_group_spec`
  (module 9) into a single site-abstract combinator `teer_walknext_group_gen`,
  parameterised by the call PC / callee-return (mid) PC / fall-through PC.  It
  takes the site's `rlp_walk_next` CALL triple (`teer_walknextNN_call_spec`, the
  abstract two-arm post `rlpWalkNextOk ∨ (∃ st, … a1 = st ≠ 0)`) and the site's
  post-call non-advance dispatch (`teer_walknext(NN+1)_bne_spec`), and produces
  the routed group `cpsBranchWithin ((1+87)+1) callPC → {far epilogue 2856
  teerFail, fallPC rlpWalkNextOk}`.

  The recipe is verbatim that of module 9: per-arm branch via
  `cpsBranchWithin_frameR` + `cpsBranchWithin_exists_pre`; recombine with
  `sepConj_or_split` / `cpsBranchWithin_pre_or`; sequence the call via
  `cpsTripleWithin_seq_branch_same_cr`.

  The combinator is then instantiated at every remaining `rlp_walk_next` site:
  the `to`/value walk (65 / 70 / 75 / 80 / 85 and past-`to` 97) and the
  authorization-list walk (116 / 121 / 126 / 131 / 136 / 141 / 146 / 151 / 156 /
  161).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix9

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000 in
/-- **Site-abstract `rlp_walk_next` dispatch group.**  Chains the site's
    `rlp_walk_next` CALL triple (`hcall`, `callPC → midPC`, abstract two-arm
    post) into the non-advance `bne a1, 0` family (`hbneFam`, `midPC →
    {2856, fallPC}`), routing the callee's `rlpWalkNextOk` success arm to
    `fallPC` and the non-advance failure arm to the far epilogue `teerB + 2856`
    (`teerFail`). -/
theorem teer_walknext_group_gen
    (callPC midPC fallPC : Word)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hcall : cpsTripleWithin (1 + 87) callPC midPC fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))))
    (hbneFam : ∀ a1 : Word,
      cpsBranchWithin 1 midPC fullCode
        ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
        (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
        fallPC ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝)) :
    cpsBranchWithin ((1 + 87) + 1) callPC fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) := by
  -- The success arm branch, one witness at a time (a1 = 0 pins the fall-through).
  have hOkFam : ∀ next len : Word,
      cpsBranchWithin 1 midPC fullCode
        ((.x1 ↦ᵣ midPC) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes) **
           ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
             ⌜EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
               (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝)))
        (teerB + 2856) teerFail fallPC
        ((.x1 ↦ᵣ midPC) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes) **
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff)) := by
    intro next len
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ midPC) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes) **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
        ⌜EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
          (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝)
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_pure
          | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (hbneFam (0 : Word))
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ _ => trivial) (fun h hq => ?_) hbneF
    -- strip the trivial ⌜0 = 0⌝ the `bne` fall exit adds (xperm keeps atoms).
    obtain ⟨hA, hB, hdAB, huAB, hbne, hF⟩ := hq
    obtain ⟨hA1, hA2, hdA, huA, hx11, hrest⟩ := hbne
    have hx0 : (.x0 ↦ᵣ (0 : Word)) hA2 := ((sepConj_pure_right hA2).1 hrest).1
    have hq' : (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x1 ↦ᵣ midPC) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes) **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
          ⌜EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
            (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝)) h :=
      ⟨hA, hB, hdAB, huAB, ⟨hA1, hA2, hdA, huA, hx11, hx0⟩, hF⟩
    have hq2 : ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
           ⌜EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
             (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝))) h := by
      xperm_hyp hq'
    exact sepConj_mono_right (sepConj_mono_right (fun _ hb => ⟨next, len, hb⟩)) h hq2
  have hOkArm : cpsBranchWithin 1 midPC fullCode
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff))
      (teerB + 2856) teerFail fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_exists_pre (fun next =>
        cpsBranchWithin_exists_pre (fun len => hOkFam next len)))
    obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hr2, hok⟩ := hp
    obtain ⟨next, len, hbody⟩ := hok
    exact ⟨next, len, h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hr2, hbody⟩
  -- The failure arm branch, one witness at a time (a1 = st ≠ 0 pins the epilogue).
  have hFailFam : ∀ st : Word,
      cpsBranchWithin 1 midPC fullCode
        ((.x1 ↦ᵣ midPC) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes) **
           ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
             (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝)))
        (teerB + 2856) teerFail fallPC
        ((.x1 ↦ᵣ midPC) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes) **
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff)) := by
    intro st
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ midPC) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ (0 : Word)) **
        ⌜st ≠ (0 : Word)⌝)
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_pure
          | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (hbneFam st)
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ _ => trivial) (fun h hq => ?_) hbneF
    -- ntaken is unreachable: the bne fall gives ⌜st = 0⌝, contradicting the
    -- framed ⌜st ≠ 0⌝.
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
          bytesRegion srcBase srcBytes) **
         (fun h => ∃ st, ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
           (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h)))
      (teerB + 2856) teerFail fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_exists_pre (fun st => hFailFam st))
    obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hr2, hfl⟩ := hp
    obtain ⟨st, hbody⟩ := hfl
    exact ⟨st, h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hr2, hbody⟩
  -- Recombine the two arms and sequence the call before the routed branch.
  have hbr : cpsBranchWithin 1 midPC fullCode
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st, ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
             (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))
      (teerB + 2856) teerFail fallPC
      ((.x1 ↦ᵣ midPC) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pre_or hOkArm hFailArm)
    exact sepConj_or_split h (sepConj_mono_right (fun h2 => sepConj_or_split h2) h hp)
  exact cpsTripleWithin_seq_branch_same_cr hcall hbr

/-! ## `to`/value walk GROUP — sites 65 / 70 / 75 / 80 / 85 and past-`to` 97 -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@65 dispatch group (`teerB + 260 → {2856, 268}`). -/
theorem teer_walknext65_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 260) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 268)
      ((.x1 ↦ᵣ (teerB + 264)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 260) (teerB + 264) (teerB + 268)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext65_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext66_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@70 dispatch group (`teerB + 280 → {2856, 288}`). -/
theorem teer_walknext70_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 280) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 288)
      ((.x1 ↦ᵣ (teerB + 284)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 280) (teerB + 284) (teerB + 288)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext70_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext71_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@75 dispatch group (`teerB + 300 → {2856, 308}`). -/
theorem teer_walknext75_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 300) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 308)
      ((.x1 ↦ᵣ (teerB + 304)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 300) (teerB + 304) (teerB + 308)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext75_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext76_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@80 dispatch group (`teerB + 320 → {2856, 328}`). -/
theorem teer_walknext80_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 320) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 328)
      ((.x1 ↦ᵣ (teerB + 324)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 320) (teerB + 324) (teerB + 328)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext80_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext81_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@85 dispatch group (`teerB + 340 → {2856, 348}`). -/
theorem teer_walknext85_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 340) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 348)
      ((.x1 ↦ᵣ (teerB + 344)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 340) (teerB + 344) (teerB + 348)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext85_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext86_bne_spec

set_option maxRecDepth 8000 in
/-- past-`to` `rlp_walk_next`@97 dispatch group (`teerB + 388 → {2856, 396}`). -/
theorem teer_walknext97_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 388) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 396)
      ((.x1 ↦ᵣ (teerB + 392)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 388) (teerB + 392) (teerB + 396)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext97_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext98_bne_spec

/-! ## authorization-list walk GROUP — sites 116 / 121 / … / 161 -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@116 dispatch group (`teerB + 464 → {2856, 472}`). -/
theorem teer_walknext116_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 464) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 472)
      ((.x1 ↦ᵣ (teerB + 468)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 464) (teerB + 468) (teerB + 472)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext116_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext117_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@121 dispatch group (`teerB + 484 → {2856, 492}`). -/
theorem teer_walknext121_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 484) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 492)
      ((.x1 ↦ᵣ (teerB + 488)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 484) (teerB + 488) (teerB + 492)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext121_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext122_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@126 dispatch group (`teerB + 504 → {2856, 512}`). -/
theorem teer_walknext126_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 504) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 512)
      ((.x1 ↦ᵣ (teerB + 508)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 504) (teerB + 508) (teerB + 512)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext126_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext127_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@131 dispatch group (`teerB + 524 → {2856, 532}`). -/
theorem teer_walknext131_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 524) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 532)
      ((.x1 ↦ᵣ (teerB + 528)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 524) (teerB + 528) (teerB + 532)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext131_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext132_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@136 dispatch group (`teerB + 544 → {2856, 552}`). -/
theorem teer_walknext136_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 544) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 552)
      ((.x1 ↦ᵣ (teerB + 548)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 544) (teerB + 548) (teerB + 552)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext136_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext137_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@141 dispatch group (`teerB + 564 → {2856, 572}`). -/
theorem teer_walknext141_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 564) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 572)
      ((.x1 ↦ᵣ (teerB + 568)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 564) (teerB + 568) (teerB + 572)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext141_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext142_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@146 dispatch group (`teerB + 584 → {2856, 592}`). -/
theorem teer_walknext146_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 584) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 592)
      ((.x1 ↦ᵣ (teerB + 588)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 584) (teerB + 588) (teerB + 592)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext146_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext147_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@151 dispatch group (`teerB + 604 → {2856, 612}`). -/
theorem teer_walknext151_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 604) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 612)
      ((.x1 ↦ᵣ (teerB + 608)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 604) (teerB + 608) (teerB + 612)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext151_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext152_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@156 dispatch group (`teerB + 624 → {2856, 632}`). -/
theorem teer_walknext156_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 624) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 632)
      ((.x1 ↦ᵣ (teerB + 628)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 624) (teerB + 628) (teerB + 632)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext156_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext157_bne_spec

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@161 dispatch group (`teerB + 644 → {2856, 652}`). -/
theorem teer_walknext161_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 644) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 652)
      ((.x1 ↦ᵣ (teerB + 648)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) :=
  teer_walknext_group_gen (teerB + 644) (teerB + 648) (teerB + 652)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    (teer_walknext161_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)
    teer_walknext162_bne_spec

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
