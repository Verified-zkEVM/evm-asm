/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix9

  PASS 6 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Establishes the DISJUNCTIVE-ROUTING recipe for the tx-parse walk chain: a
  single `rlp_walk_next` call GROUP (`call ;; bne a1, 0`) routed into a
  `cpsBranchWithin` whose not-taken exit carries the callee's success post
  (`rlpWalkNextOk`) and whose taken exit collapses the non-advance failure to
  the shared `teerFail` (far epilogue `teerB + 2856`).

  The callee post is the two-arm disjunction `rlpWalkNextOk ∨ (∃ st, … a1 = st ≠ 0)`;
  `rlpWalkNextOk` pins `a1 = 0`, so the post-call `bne a1, 0` deterministically
  routes the success arm to the fall-through and the failure arm to the far
  epilogue.  The routing is assembled with the confirmed machinery
  (`cpsBranchWithin_pre_or` / `sepConj_or_split` / `cpsBranchWithin_exists_pre`),
  then sequenced after the call via `cpsTripleWithin_seq_branch_same_cr`.

  Proven concretely at the first `to`/value walk site (instruction 60,
  `teerB + 240 → {2856, 248}`); the identical shape reused verbatim at every
  other `rlp_walk_next` site.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix8
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000 in
/-- **First `rlp_walk_next` dispatch** (`to`/value walk, instrs 60..61,
    `teerB + 240 → {2856, 248}`).  Chains `teer_walknext60_call_spec` into the
    non-advance `bne a1, 0` (`teer_walknext61_bne_spec`), routing the callee's
    `rlpWalkNextOk` success arm to `teerB + 248` and the non-advance failure
    arm to the far epilogue `teerB + 2856` (`teerFail`). -/
theorem teer_walknext60_group_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 240) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 248)
      ((.x1 ↦ᵣ (teerB + 244)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) := by
  have hcall := teer_walknext60_call_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid
  -- The success arm branch, one witness at a time (a1 = 0 pins the fall-through).
  have hOkFam : ∀ next len : Word,
      cpsBranchWithin 1 (teerB + 244) fullCode
        ((.x1 ↦ᵣ (teerB + 244)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes) **
           ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
             ⌜EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
               (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝)))
        (teerB + 2856) teerFail (teerB + 248)
        ((.x1 ↦ᵣ (teerB + 244)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes) **
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff)) := by
    intro next len
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ (teerB + 244)) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes) **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
        ⌜EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
          (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝)
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_pure
          | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (teer_walknext61_bne_spec (0 : Word))
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ _ => trivial) (fun h hq => ?_) hbneF
    -- strip the trivial ⌜0 = 0⌝ the `bne` fall exit adds (xperm keeps atoms).
    obtain ⟨hA, hB, hdAB, huAB, hbne, hF⟩ := hq
    obtain ⟨hA1, hA2, hdA, huA, hx11, hrest⟩ := hbne
    have hx0 : (.x0 ↦ᵣ (0 : Word)) hA2 := ((sepConj_pure_right hA2).1 hrest).1
    have hq' : (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x1 ↦ᵣ (teerB + 244)) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes) **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
          ⌜EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
            (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝)) h :=
      ⟨hA, hB, hdAB, huAB, ⟨hA1, hA2, hdA, huA, hx11, hx0⟩, hF⟩
    have hq2 : ((.x1 ↦ᵣ (teerB + 244)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
           ⌜EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
             (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝))) h := by
      xperm_hyp hq'
    exact sepConj_mono_right (sepConj_mono_right (fun _ hb => ⟨next, len, hb⟩)) h hq2
  have hOkArm : cpsBranchWithin 1 (teerB + 244) fullCode
      ((.x1 ↦ᵣ (teerB + 244)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff))
      (teerB + 2856) teerFail (teerB + 248)
      ((.x1 ↦ᵣ (teerB + 244)) **
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
      cpsBranchWithin 1 (teerB + 244) fullCode
        ((.x1 ↦ᵣ (teerB + 244)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes) **
           ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
             (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝)))
        (teerB + 2856) teerFail (teerB + 248)
        ((.x1 ↦ᵣ (teerB + 244)) **
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes) **
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff)) := by
    intro st
    have hbneF := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ (teerB + 244)) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ (0 : Word)) **
        ⌜st ≠ (0 : Word)⌝)
      (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_pure
          | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
      (teer_walknext61_bne_spec st)
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
  have hFailArm : cpsBranchWithin 1 (teerB + 244) fullCode
      ((.x1 ↦ᵣ (teerB + 244)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h => ∃ st, ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
           (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h)))
      (teerB + 2856) teerFail (teerB + 248)
      ((.x1 ↦ᵣ (teerB + 244)) **
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
  have hbr244 : cpsBranchWithin 1 (teerB + 244) fullCode
      ((.x1 ↦ᵣ (teerB + 244)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st, ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
             (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))
      (teerB + 2856) teerFail (teerB + 248)
      ((.x1 ↦ᵣ (teerB + 244)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
           srcBytes srcOff)) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pre_or hOkArm hFailArm)
    exact sepConj_or_split h (sepConj_mono_right (fun h2 => sepConj_or_split h2) h hp)
  exact cpsTripleWithin_seq_branch_same_cr hcall hbr244

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
