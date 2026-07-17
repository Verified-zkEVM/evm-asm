/-
  `withdrawalDecode_prog` caller-contract composition, part 5 — the CONT side
  and the whole-program close.

  Close4 finished every parse-failure exit (`wdK34FailArm`, `wdK20FailArm`,
  `wdFailArm`).  This module supplies the mirror image on the continue side:

    * `wdContReshape` — the cont analog of `wdK34FailPre`: a K34 field call's
      `k34ContPost` (status `0`, success payload) reshaped into the shared
      register/frame bundle each downstream stage consumes, weakening the saved
      frame (`savedFrame → frameSlotsOwn`) and keeping the freshly-written output
      cell together with the pinned field `Result`.
    * the merge-chain backbone stitching the four field stages, the length
      check and the copy loop into a single `WB+32 → raIn` triple; and
    * the top-level `withdrawal_decode_spec_within = wdPrologue ;; backbone`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.WithdrawalDecodeClose4

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64SAsm

/-! ## CONT-side reshape (K34 boundary)

    A K34 field call's continue exit (`k34ContPost`, status `0`) keeps a success
    payload with a genuine field decode.  The reshape below lines that payload up
    with the shared field-stage register/frame layout: the saved frame weakens to
    the merely-owned slots (`savedFrameK34_own`), and the payload's temporaries
    reappear as the next stage's `regIs`/`regOwn` cells.  The freshly-written
    output cell (`saved.s1 ↦ ov`) and the pinned per-field `Result` are carried
    forward so the whole-program success post can assemble `Decoded`. -/

/-- The shared cont-boundary bundle: the register/frame state a downstream field
    stage consumes, together with the just-written output cell and the pinned
    field `Result`.  The saved frame has already been weakened to `frameSlotsOwn`
    and the scratch stack retained as `stackFree newSp 8`. -/
def wdContBundle (spW newSp listBase raRet offset len v12 x5 ss ov : Word)
    (outer : Saved) (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  (.x1 ↦ᵣ raRet) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
  frameSlotsOwn frame newSp ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** stackFree newSp 8 **
  (.x5 ↦ᵣ x5) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ ss) ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) ** (saved.s1 ↦ₘ ov) **
  (⌜Result bytes listBase listLen index (0 : Word) ov⌝ : Assertion)

set_option maxRecDepth 8000 in
/-- CONT reshape: a K34 field call's peeled `k34ContPost` body (a status-`0`
    success payload) reshapes into `wdContBundle`.  Weaken the saved frame to
    `frameSlotsOwn` and permute; the field `Result`, the written output cell
    `saved.s1 ↦ ov` and the temporaries all carry through unchanged.  Generic
    over the field index — the backbone instantiates it at boundaries 0→1, 1→2,
    2→3. -/
theorem wdContReshape (spW newSp listBase raRet offset len v12 x5 ss ov : Word)
    (outer : Saved) (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    ((.x1 ↦ᵣ raRet) **
     (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
       savedFrame newSp outer) **
      successPayload newSp listBase offset len v12 x5 ss (0 : Word) ov saved
        bytes listLen index)) h →
    wdContBundle spW newSp listBase raRet offset len v12 x5 ss ov outer saved bytes
      listLen index h := by
  intro h hp
  unfold successPayload at hp
  have hp2 := sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (savedFrameK34_own newSp outer))))) h hp
  unfold wdContBundle
  xperm_hyp hp2

#print axioms wdContReshape

/-! ## Field-3 continue: the success-content tie

    Field 3's continue exit (`WB+204`) is the all-fields-decoded success path.
    The upstream field decode facts (fields 0/1 `Result`, the field-2 `Success`
    with length `20`) arrive as hypotheses; combined with field 3's own pinned
    `Result` they assemble `Decoded`, and the written output cells assemble
    `outputSuccess`.  The success tail (`wdSuccessEpi`, `WB+204 → raIn`) then
    stores `a0 := 0` and returns, landing the whole-program success post. -/

set_option maxRecDepth 8000 in
/-- Field-3 continue → success return: from `k34ContPost` (index 3, framed over
    the reclaimed top cell, the four saved slots, the already-written
    field-0/1/address output cells, the address data cells) plus the upstream
    decode facts, run the success tail to the whole-program success post. -/
theorem wdField3ContEpi
    (sp0 spW newSp raIn listBase len outBase v0 v1 o2 l2
      s0Old s1Old s2Old s3 s4 s5 : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hf0 : Result bytes listBase listLen 0 (0 : Word) v0)
    (hf1 : Result bytes listBase listLen 1 (0 : Word) v1)
    (hf2 : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2)
    (hl2 : l2.toNat = 20) :
    let outer3 : Saved := { ra := WB + 200, s0 := listBase, s1 := len }
    let saved3 : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outBase + 40, s2 := outBase, s3 := s3,
        s4 := s4, s5 := s5 }
    cpsTripleWithin 8 (WB + 204) raIn fullCode
      (k34ContPost spW newSp listBase (WB + 200) outer3 saved3 bytes listLen 3 **
       (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
        ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) (addrCopied bytes oldAddr o2) **
        bytesRegion (outBase + 36) pad4 ** (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2)))
      (wdWholePost sp0 spW raIn s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
  intro outer3 saved3
  refine cpsTripleWithin_weaken (P := fun h => ∃ offset len' v12 x5 ss ov,
      (((.x1 ↦ᵣ (WB + 200)) **
        (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer3.s0) ** (.x9 ↦ᵣ outer3.s1) **
          savedFrame newSp outer3) **
         successPayload newSp listBase offset len' v12 x5 ss (0 : Word) ov saved3
           bytes listLen 3)) **
       (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
        ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) (addrCopied bytes oldAddr o2) **
        bytesRegion (outBase + 36) pad4 ** (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2))) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hk, hacc⟩ := hp
      unfold k34ContPost at hk
      obtain ⟨offset, len', v12, x5, ss, ov, hbody⟩ := hk
      exact ⟨offset, len', v12, x5, ss, ov, h1, h2, hd, hu, hbody, hacc⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun offset => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len' => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun v12 => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun x5 => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun ss => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun ov => ?_)
  -- G0: the untouched footprint threaded through `wdSuccessEpi`.
  set G0 : Assertion :=
    (⌜Result bytes listBase listLen 3 (0 : Word) ov⌝ : Assertion) **
    (outputSuccess outBase v0 v1 ov o2 bytes oldAddr pad4 ** bytesRegion listBase bytes **
     (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2) ** (offsetCell ↦ₘ offset) **
     (lengthCell ↦ₘ len') ** stackFree spW 12 ** wdScratch s3 s4 s5) with hG0def
  have hG0 : G0.pcFree := by
    rw [hG0def]; unfold outputSuccess wdScratch
    repeat' first
      | exact pcFree_pure | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_regOwn
      | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _ | apply pcFree_sepConj
  have hepi := wdSuccessEpi sp0 spW raIn s0Old s1Old s2Old (WB + 200) listBase len outBase
    (0 : Word) G0 hG0 hspW hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hepi
  · -- pre reshape: (bodyCore ** accum) → wdSuccessEpi pre
    unfold successPayload at hp
    simp only [show (outer3.s0 : Word) = listBase from rfl,
      show (outer3.s1 : Word) = len from rfl,
      show (saved3.s1 : Word) = outBase + 40 from rfl,
      show (saved3.s2 : Word) = outBase from rfl, show (saved3.s3 : Word) = s3 from rfl,
      show (saved3.s4 : Word) = s4 from rfl, show (saved3.s5 : Word) = s5 from rfl] at hp
    have hgR : ((.x10 ↦ᵣ (0 : Word)) **
        ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ (WB + 200)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
         (.x18 ↦ᵣ outBase) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
         ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old)) **
        (⌜Result bytes listBase listLen 3 (0 : Word) ov⌝ : Assertion) **
        ((outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) **
         bytesRegion (outBase + 16) (addrCopied bytes oldAddr o2) **
         bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ ov)) **
        bytesRegion listBase bytes ** (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2) **
        (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len') **
        (memOwn (spW - BitVec.ofNat 64 8) ** savedFrame newSp outer3 **
         stackFree newSp 8) **
        ((.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x5 ↦ᵣ x5) ** regOwn .x6 **
         regOwn .x7 ** (.x11 ↦ᵣ ss) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         (.x0 ↦ᵣ (0 : Word)))) h := by
      xperm_hyp hp
    rw [hG0def]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (fun _ hx => hx)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (wdStack12_of_k34_saved spW newSp outer3 hnewSp)
              (wdScratch_of_regs s3 s4 s5 x5 ss v12))))))))))
      h hgR
  · -- post reshape: wdSuccessEpi post → whole-program success
    rw [hG0def] at hq
    have hf3 : Result bytes listBase listLen 3 (0 : Word) ov := by
      obtain ⟨_, _, _, _, _, hR⟩ := hq
      obtain ⟨_, _, _, _, _, hG0'⟩ := hR
      exact ((sepConj_pure_left _).1 hG0').1
    refine Or.inl ⟨v0, v1, ov, o2, l2,
      (sepConj_pure_left h).2 ⟨⟨hf0, hf1, hf2, hl2, hf3⟩, ?_⟩⟩
    exact sepConj_mono_right (sepConj_mono (fun _ hx => hx)
      (fun h' hg0 => ⟨offset, len', ((sepConj_pure_left h').1 hg0).2⟩)) h hq

#print axioms wdField3ContEpi

/-! ## Field-3 backbone merge

    Merge the field-3 stage's two exits: the parse-fail edge routes through
    `wdK34FailArm 3` (constructor `DecodeFailure.field3`), the continue edge
    through `wdField3ContEpi` (the success tie).  Both land the whole-program
    post; the four saved slots, the reclaimed top cell and the upstream output
    cells are framed ambient across both. -/

set_option maxRecDepth 8000 in
/-- The field-3 backbone: field-3 stage `WB+180 → raIn`, both exits landing
    `wdWholePost`.  The accumulator carries fields 0/1 output cells, the address
    copy, pad, the address data cells, the saved slots and the reclaimed top
    cell; the upstream decode facts arrive as hypotheses. -/
theorem wdBBField3
    (sp0 spW newSp raEntry raSaved listBase len outBase oldOut oldOffset oldLen old14
      s3 s4 s5 v10 v11 v12 v13 v0 v1 o2 l2 s0Old s1Old s2Old : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hf0 : Result bytes listBase listLen 0 (0 : Word) v0)
    (hf1 : Result bytes listBase listLen 1 (0 : Word) v1)
    (hf2 : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2)
    (hl2 : l2.toNat = 20) :
    let callSteps := 1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsTripleWithin ((4 + (1 + n34) + 1) + 8) (WB + 180) raSaved fullCode
      ((((.x1 : Reg) ↦ᵣ raEntry) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        ((outBase + 40) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen)) **
       (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
        ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) (addrCopied bytes oldAddr o2) **
        bytesRegion (outBase + 36) pad4 ** (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2)))
      (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
  intro callSteps tailSteps n34
  have hstage := wdField3Stage spW newSp raEntry listBase len outBase oldOut oldOffset
    oldLen old14 s3 s4 s5 v10 v11 v12 v13 bytes listLen hnewSp hlenW hsalign hslack hover
    hvalid
  have hbr := cpsBranchWithin_frameR
    (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
     ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
     ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) (addrCopied bytes oldAddr o2) **
     bytesRegion (outBase + 36) pad4 ** (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2))
    (by repeat' first
        | exact pcFree_memOwn | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hstage
  have h_t := cpsTripleWithin_mono_nSteps (show (7 : Nat) ≤ 8 from by omega)
    (wdK34FailArm sp0 spW newSp raSaved listBase oldOffset oldLen (WB + 200) s0Old s1Old
      s2Old { ra := WB + 200, s0 := listBase, s1 := len }
      { ra := B + 48, s0 := listBase, s1 := outBase + 40, s2 := outBase, s3 := s3,
        s4 := s4, s5 := s5 } bytes oldAddr pad4 listLen 3
      ((outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) **
       bytesRegion (outBase + 16) (addrCopied bytes oldAddr o2) **
       bytesRegion (outBase + 36) pad4 ** (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2))
      hspW hnewSp hret
      (fun status v hnz hres => DecodeFailure.field3 status v hnz hres)
      (fun roff rlen ov h hp => by
        refine ⟨v0, v1, ov, o2, l2, roff, rlen, addrCopied bytes oldAddr o2, pad4, ?_⟩
        xperm_hyp hp))
  have h_f := wdField3ContEpi sp0 spW newSp raSaved listBase len outBase v0 v1 o2 l2
    s0Old s1Old s2Old s3 s4 s5 bytes oldAddr pad4 listLen hspW hnewSp hret hf0 hf1 hf2 hl2
  exact cpsBranchWithin_merge_same_cr hbr h_t h_f

#print axioms wdBBField3

end EvmAsm.Codegen.WithdrawalDecodeSpec
