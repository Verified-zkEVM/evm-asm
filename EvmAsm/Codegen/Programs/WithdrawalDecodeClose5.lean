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
import EvmAsm.Rv64.RLP.WalkItemDeterminism

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64StrictSAsm
open EvmAsm.Evm64.Terminating (copyIntoRegion)

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
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
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
    oldLen old14 s3 s4 s5 v10 v11 v12 v13 bytes listLen hnewSp hlenW hsalign hbytes hnowrap hover
    hvalid hnz
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

/-! ## Field-2 content bound

    The address copy loop reads 20 source bytes at the selected content offset
    `o2`.  A K20 `Success` pins a `StrictNthItem` decode chain whose final item's
    content span stays within the declared list length; combined with the input
    slack this bounds the source read `o2.toNat + 20 ≤ bytes.length`. -/

open EvmAsm.Codegen.RlpListNthItemSAsm in
/-- The selected item's content span (offset + length) fits inside the declared
    list window `endOff`.  Induction on the `StrictNthItem` chain: each
    non-final decode strictly advances the cursor but stays `≤ endOff`
    (`rlpItemDecode_advance`), and the final decode's content span is bounded by
    `rlpItemDecode_field0_content_span`. -/
theorem strictNthItem_content_le {bytes : List (BitVec 8)} {base : Word}
    {endOff : Nat} : ∀ {index cursorOff : Nat} {next len : Word},
    StrictNthItem bytes base (base + BitVec.ofNat 64 endOff) index cursorOff next len →
    cursorOff ≤ endOff →
    base.toNat + endOff + 9 < 2 ^ 64 →
    (next - len - base).toNat + len.toNat ≤ endOff := by
  intro index cursorOff next len h
  induction h with
  | zero off n l hitem =>
      intro hcursor hover
      exact (EvmAsm.Rv64.RLP.rlpItemDecode_field0_content_span hitem hcursor hover).2.2
  | succ idx off n l fn fl hitem hrest ih =>
      intro hcursor hover
      have hadv := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance
        hitem hcursor hover
      exact ih hadv.2.2 hover

#print axioms strictNthItem_content_le

open EvmAsm.Codegen.RlpListNthItemSAsm in
/-- From a K20 `Success` (index 2), the selected content offset plus length fits
    inside the declared list length. -/
theorem wdSuccessContentBound (bytes : List (BitVec 8)) (listBase : Word)
    (listLen : Nat) (offset len' : Word)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hsucc : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 offset len') :
    offset.toNat + len'.toNat ≤ listLen := by
  obtain ⟨cursorOff, endPtr, next, hpay, hnth, hoff⟩ := hsucc
  have hend := hpay.end_eq
  have hcur := hpay.cursor_le
  subst hend
  subst hoff
  exact strictNthItem_content_le hnth hcur hnowrap

#print axioms wdSuccessContentBound

/-! ## Field-2 middle segment (`WB+116 → raIn`)

    The K20 continue exit reshapes into the length check `WB+116`; a `len ≠ 20`
    edge is the `field2Len` failure, and the `len = 20` edge copies the 20 address
    bytes (`wdCopySetup ;; wdCopyLoop`) and hands off to the field-3 backbone. -/

/-- Introduce EIGHT owned registers' values at once (trailing `regOwn` chain). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn8
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 r4 r5 r6 r7 r8 : Reg}
    {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5 v6 v7 v8, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) **
       (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7) ** (r8 ↦ᵣ v8)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7 ** regOwn r8) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, k1, k2, d0, u0, hPP, hRb⟩ := hPR
  obtain ⟨k3, k4, d1, u1, hP3, hO1⟩ := hPP
  obtain ⟨a1, b1, e1, f1, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨a2, b2, e2, f2, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨a3, b3, e3, f3, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨a4, b4, e4, f4, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨a5, b5, e5, f5, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨a6, b6, e6, f6, ⟨v6, hv6⟩, hO7⟩ := hO6
  obtain ⟨a7, b7, e7, f7, ⟨v7, hv7⟩, ⟨v8, hv8⟩⟩ := hO7
  exact h v1 v2 v3 v4 v5 v6 v7 v8 R hR s hcr
    ⟨hp, hcompat, k1, k2, d0, u0,
      ⟨k3, k4, d1, u1, hP3,
        a1, b1, e1, f1, hv1, a2, b2, e2, f2, hv2, a3, b3, e3, f3, hv3,
        a4, b4, e4, f4, hv4, a5, b5, e5, f5, hv5, a6, b6, e6, f6, hv6,
        a7, b7, e7, f7, hv7, hv8⟩, hRb⟩ hpc

/-- All clobbered temporaries (as concrete `regIs` cells) weaken into
    `wdScratch`; `x31` arrives already owned. -/
theorem wdScratch_of_regIs (s3 s4 s5 v5 v6 v7 v11 v12 v13 v14 v28 v29 v30 : Word) : ∀ h,
    ((.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
     (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word))) h →
    wdScratch s3 s4 s5 h := by
  intro h hp
  unfold wdScratch
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
    (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono (regIs_implies_regOwn .x12) (sepConj_mono (regIs_implies_regOwn .x13)
    (sepConj_mono (regIs_implies_regOwn .x14) (sepConj_mono (regIs_implies_regOwn .x28)
    (sepConj_mono (regIs_implies_regOwn .x29)
      (sepConj_mono_left (regIs_implies_regOwn .x30))))))))))))) h hp

/-- `pcFree` discharge covering `wdStackK20Deep`/`wdScratch` frames. -/
local macro "pcfw" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_pure
    | exact pcFree_stackFree _ _
    | exact pcFree_wdStackK20Deep _
    | exact pcFree_wdScratch _ _ _
    | exact pcFree_frameSlotsOwn _ _
    | apply pcFree_sepConj)

set_option maxRecDepth 8000 in
/-- Field-2 continue → whole-program post (`WB+116 → raIn`): reshape the K20
    continue payload into the length check, then either fail on `len ≠ 20`
    (`field2Len`) or copy the 20 address bytes and run the field-3 backbone. -/
theorem wdField2ContEpi
    (sp0 spW newSp raIn listBase len outBase v0 v1 oldOut oldOffset oldLen
      s0Old s1Old s2Old s3 s4 s5 : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (houtalign : outBase.toNat % 8 = 0)
    (houtover : outBase.toNat + 48 < 2 ^ 64)
    (haddrlen : oldAddr.length = 20)
    (houtvalid : ∀ k, k < 20 →
      isValidByteAccess ((outBase + 16) + BitVec.ofNat 64 k) = true)
    (hf0 : Result bytes listBase listLen 0 (0 : Word) v0)
    (hf1 : Result bytes listBase listLen 1 (0 : Word) v1) :
    let saved2 : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := WB + 112, s0 := listBase, s1 := len, s2 := outBase, s3 := s3, s4 := s4,
        s5 := s5 }
    cpsTripleWithin (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8)))
      (WB + 116) raIn fullCode
      (k20ContPost spW listBase saved2 bytes listLen **
       (wdStackK20Deep spW ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
        ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
        bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
        (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen)))
      (wdWholePost sp0 spW raIn s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
  intro saved2
  -- (1) Expose the K20 continue existentials + `Success` + eight owned temporaries.
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ offset len' v11 v12,
      ((⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 offset
          len'⌝ : Assertion) **
       (((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ (WB + 112)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
         (.x18 ↦ᵣ outBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
         stackFree spW 8 ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x0 ↦ᵣ (0 : Word)) ** regOwn .x31 ** bytesRegion listBase bytes **
         (wdOffsetAddr ↦ₘ offset) ** (wdLengthAddr ↦ₘ len') ** (spW ↦ₘ raIn) **
         ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) **
         (outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
         bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
         wdStackK20Deep spW ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hk, hacc⟩ := hp
      obtain ⟨offset, len', v11, v12, hbody⟩ := hk
      refine ⟨offset, len', v11, v12, ?_⟩
      obtain ⟨hsucc, hbig⟩ := (sepConj_pure_left h1).1 hbody
      refine (sepConj_pure_left h).2 ⟨hsucc, ?_⟩
      have hcomb :
          ((((.x2 ↦ᵣ spW) ** regsAt EvmAsm.Codegen.RlpListNthItemSAsm.listNthFrame
              (EvmAsm.Codegen.RlpListNthItemSAsm.savedVals saved2) ** stackFree spW 8) **
            ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
             (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
             regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
             (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
             (wdOffsetAddr ↦ₘ offset) ** (wdLengthAddr ↦ₘ len'))) **
           (wdStackK20Deep spW ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
            ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
            ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
            bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
            (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))) h :=
        ⟨h1, h2, hd, hu, hbig, hacc⟩
      rw [EvmAsm.Codegen.RlpListNthItemSAsm.regsAt_listNthFrame] at hcomb
      simp only [show (saved2.ra : Word) = WB + 112 from rfl,
        show (saved2.s0 : Word) = listBase from rfl, show (saved2.s1 : Word) = len from rfl,
        show (saved2.s2 : Word) = outBase from rfl, show (saved2.s3 : Word) = s3 from rfl,
        show (saved2.s4 : Word) = s4 from rfl, show (saved2.s5 : Word) = s5 from rfl] at hcomb
      xperm_hyp hcomb)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun offset => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len' => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun v11 => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun v12 => ?_)
  refine cpsTripleWithin_pure_pre (fun hsucc => ?_)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn8 (fun v5 v6 v7 v13 v14 v28 v29 v30 => ?_)
  -- (2) The length-check branch, framed by the untouched footprint `FL`.
  have hbr := cpsBranchWithin_frameR
    ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ (WB + 112)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
     (.x18 ↦ᵣ outBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
     stackFree spW 8 ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x0 ↦ᵣ (0 : Word)) ** regOwn .x31 ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes **
     (wdOffsetAddr ↦ₘ offset) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
     ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
     ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
     bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) ** wdStackK20Deep spW **
     (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
    (by pcfw) (wdLenCheck v5 v6 v7 len')
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsBranchWithin_merge_same_cr hbr ?fail ?cont)
  case cont =>
    -- len = 20: copy setup ;; copy loop ;; field-3 backbone.
    have hoffnorm : (BitVec.ofNat 64 offset.toNat : Word) = offset := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine cpsTripleWithin_weaken
      (P := (⌜len' = (20 : Word)⌝ : Assertion) **
        (((.x6 ↦ᵣ len') ** (.x7 ↦ᵣ (20 : Word))) ** (.x5 ↦ᵣ wdLengthAddr) **
         (wdLengthAddr ↦ₘ len') **
         ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ (WB + 112)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
          (.x18 ↦ᵣ outBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
          stackFree spW 8 ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x0 ↦ᵣ (0 : Word)) ** regOwn .x31 ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes **
          (wdOffsetAddr ↦ₘ offset) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
          ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
          ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
          bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
          wdStackK20Deep spW ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))))
      (fun h hp => by
        have hleneq : len' = (20 : Word) := by
          have hp2 := hp
          obtain ⟨cp, _, _, _, hcp, _⟩ := hp2
          obtain ⟨gg, _, _, _, hgrp, _⟩ := hcp
          obtain ⟨a, b, _, _, _, hg3⟩ := hgrp
          exact ((sepConj_pure_right b).1 hg3).2
        refine (sepConj_pure_left h).2 ⟨hleneq, ?_⟩
        have hp' : ((((.x6 ↦ᵣ len') ** (.x7 ↦ᵣ (20 : Word))) ** (.x5 ↦ᵣ wdLengthAddr) **
            (wdLengthAddr ↦ₘ len')) **
           ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ (WB + 112)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
            (.x18 ↦ᵣ outBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
            stackFree spW 8 ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
            (.x0 ↦ᵣ (0 : Word)) ** regOwn .x31 ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
            (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes **
            (wdOffsetAddr ↦ₘ offset) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
            ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
            ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
            bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
            wdStackK20Deep spW ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))) h :=
          sepConj_mono_left
            (fun h'' hcp => sepConj_mono_left sepConj_strip_pure_end2 h'' hcp) h hp
        xperm_hyp hp')
      (fun _ hq => hq) ?_
    refine cpsTripleWithin_pure_pre (fun hleneq => ?_)
    -- copy setup [34]-[38].
    have hcs := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ len') ** (.x7 ↦ᵣ (20 : Word)) ** (wdLengthAddr ↦ₘ len') ** (.x2 ↦ᵣ spW) **
       (.x1 ↦ᵣ (WB + 112)) ** (.x9 ↦ᵣ len) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x31 ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ v14) ** (.x30 ↦ᵣ v30) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
       stackFree spW 8 ** bytesRegion listBase bytes ** (spW ↦ₘ raIn) **
       ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) **
       (outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
       bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) ** wdStackK20Deep spW **
       (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      (by pcfw) (wdCopySetup wdLengthAddr v28 v29 listBase outBase offset)
    -- copy loop [39]-[44].
    have hcl := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ wdOffsetAddr) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outBase) **
       (wdOffsetAddr ↦ₘ offset) ** (.x7 ↦ᵣ (20 : Word)) ** (wdLengthAddr ↦ₘ len') **
       (.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ (WB + 112)) ** (.x9 ↦ᵣ len) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x31 ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 ** (spW ↦ₘ raIn) **
       ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) **
       (outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 36) pad4 **
       ((outBase + 40) ↦ₘ oldOut) ** wdStackK20Deep spW ** (offsetCell ↦ₘ oldOffset) **
       (lengthCell ↦ₘ oldLen))
      (by pcfw)
      (wdCopyLoop listBase (outBase + 16) v30 bytes oldAddr offset.toNat 0 0 19 hsalign
        (by bv_omega)
        (by have := wdSuccessContentBound bytes listBase listLen offset len' hnowrap hsucc
            rw [hleneq] at this; simp only [show (20 : Word).toNat = 20 from by decide] at this
            omega)
        (by omega) hover (by bv_omega) hvalid
        (by intro k hk; rw [haddrlen] at hk; exact houtvalid k hk))
    -- field-3 backbone [45]-[59].
    have hbb := wdBBField3 sp0 spW newSp (WB + 112) raIn listBase len outBase oldOut oldOffset
      oldLen v14 s3 s4 s5 (0 : Word) v11 v12 v13 v0 v1 offset len' s0Old s1Old s2Old bytes
      oldAddr pad4 listLen hnewSp hspW hret hlenW hsalign hbytes hnowrap hover hvalid hnz hf0 hf1 hsucc
      (by rw [hleneq]; decide)
    -- bridge 1: copy-setup post → copy-loop pre.
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        rw [show (BitVec.ofNat 64 (19 + 1) : Word) = len' from by rw [hleneq]; decide,
          show listBase + BitVec.ofNat 64 (offset.toNat + 0) = listBase + offset from by
            rw [Nat.add_zero, hoffnorm],
          show (outBase + 16) + BitVec.ofNat 64 (0 + 0) = outBase + 16 from by bv_omega,
          show copyIntoRegion oldAddr bytes 0 offset.toNat 0 = oldAddr from rfl]
        xperm_hyp hp)
      hcs hcl
    -- bridge 2: copy-loop post → field-3 backbone pre.
    have s2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp1 : ((regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
            bytesRegion (outBase + 16) (addrCopied bytes oldAddr offset)) **
           ((.x5 ↦ᵣ wdOffsetAddr) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outBase) **
            (wdOffsetAddr ↦ₘ offset) ** (.x7 ↦ᵣ (20 : Word)) ** (wdLengthAddr ↦ₘ len') **
            (.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ (WB + 112)) ** (.x9 ↦ᵣ len) ** (.x10 ↦ᵣ (0 : Word)) **
            (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x31 ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
            (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** stackFree spW 8 ** (spW ↦ₘ raIn) **
            ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) **
            (outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 36) pad4 **
            ((outBase + 40) ↦ₘ oldOut) ** wdStackK20Deep spW ** (offsetCell ↦ₘ oldOffset) **
            (lengthCell ↦ₘ oldLen))) h := by
          refine sepConj_mono_left ?_ h hp
          intro h' hcl'
          exact sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x28)
            (sepConj_mono_left (regIs_implies_regOwn .x29))) h' hcl'
        have hg : (((stackFree spW 8 ** wdStackK20Deep spW) **
            ((.x5 ↦ᵣ wdOffsetAddr) ** (.x7 ↦ᵣ (20 : Word))) **
            ((.x1 ↦ᵣ (WB + 112)) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
             (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
             (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** regOwn .x6 ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
             (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
             (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes ** ((outBase + 40) ↦ₘ oldOut) **
             (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen) ** (spW ↦ₘ raIn) **
             ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) **
             (outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) **
             bytesRegion (outBase + 16) (addrCopied bytes oldAddr offset) **
             bytesRegion (outBase + 36) pad4 ** (wdOffsetAddr ↦ₘ offset) **
             (wdLengthAddr ↦ₘ len'))) h) := by
          xperm_hyp hp1
        have hg2 : (((memOwn (spW - BitVec.ofNat 64 8) ** frameSlotsOwn frame newSp **
            stackFree newSp 8) ** (regOwn .x5 ** regOwn .x7) **
            ((.x1 ↦ᵣ (WB + 112)) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
             (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
             (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** regOwn .x6 ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
             (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
             (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes ** ((outBase + 40) ↦ₘ oldOut) **
             (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen) ** (spW ↦ₘ raIn) **
             ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) **
             (outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) **
             bytesRegion (outBase + 16) (addrCopied bytes oldAddr offset) **
             bytesRegion (outBase + 36) pad4 ** (wdOffsetAddr ↦ₘ offset) **
             (wdLengthAddr ↦ₘ len'))) h) := by
          refine sepConj_mono ?_ (sepConj_mono ?_ (fun _ x => x)) h hg
          · intro h' hs
            exact wdStack12_to_k34 spW newSp hnewSp h'
              (wdStack12_of_k20 spW h' (by xperm_hyp hs))
          · intro h' hr
            exact sepConj_mono (regIs_implies_regOwn .x5) (regIs_implies_regOwn .x7) h' hr
        xperm_hyp hg2)
      s1 hbb
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq) s2
  case fail =>
    -- len ≠ 20: `field2Len` failure through the failure tail.
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (Nat.le_trans (by norm_num) (Nat.le_add_right _ _))
        (wdFailArm sp0 spW raIn s0Old s1Old s2Old (WB + 112) listBase len outBase
          outBase listBase s3 s4 s5 bytes oldAddr pad4 listLen hspW hret))
    have hne : len' ≠ (20 : Word) := by
      have hp2 := hp
      obtain ⟨fp, fl, _, _, hfp, _⟩ := hp2
      obtain ⟨g1, g2, _, _, hgrp, _⟩ := hfp
      obtain ⟨a, b, _, _, _, hg3⟩ := hgrp
      exact ((sepConj_pure_right b).1 hg3).2
    have hne20 : len'.toNat ≠ 20 := by
      intro heq; exact hne (by apply BitVec.eq_of_toNat_eq; rw [heq]; decide)
    have hDF : DecodeFailure bytes listBase listLen :=
      DecodeFailure.field2Len offset len' hsucc hne20
    have hp' := sepConj_mono_left (sepConj_mono_left sepConj_strip_pure_end2) h hp
    have hg : (((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ (WB + 112)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) **
        ((spW + 24) ↦ₘ s2Old) **
        (((.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x5 ↦ᵣ wdLengthAddr) **
          (.x6 ↦ᵣ len') ** (.x7 ↦ᵣ (20 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) **
         ((wdStackK20Deep spW ** stackFree spW 8) ** (outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) **
          bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
          ((outBase + 40) ↦ₘ oldOut) ** bytesRegion listBase bytes ** (wdOffsetAddr ↦ₘ offset) **
          (wdLengthAddr ↦ₘ len') ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen)))) **
       (.x10 ↦ᵣ (0 : Word))) h := by
      xperm_hyp hp'
    refine sepConj_mono ?_ (regIs_implies_regOwn .x10) h hg
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right ?_))))))))
    intro h' hgg
    refine (sepConj_pure_left h').2 ⟨hDF, ?_⟩
    refine ⟨v0, v1, oldOut, offset, len', oldOffset, oldLen, oldAddr, pad4, ?_⟩
    have hgg2 : (wdScratch s3 s4 s5 ** stackFree spW 12 ** (outBase ↦ₘ v0) **
        ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
        bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
        bytesRegion listBase bytes ** (wdOffsetAddr ↦ₘ offset) ** (wdLengthAddr ↦ₘ len') **
        (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen)) h' := by
      refine sepConj_mono (wdScratch_of_regIs s3 s4 s5 wdLengthAddr len' (20 : Word) v11 v12
        v13 v14 v28 v29 v30) (sepConj_mono_left (wdStack12_of_k20 spW)) h' hgg
    xperm_hyp hgg2

#print axioms wdField2ContEpi

/-! ## Field-2 backbone merge

    Merge the field-2 (K20) stage's two exits: the parse-fail edge routes through
    `wdK20FailArm` (constructor `DecodeFailure.field2List`), the continue edge
    through `wdField2ContEpi` (length check + address copy + field-3 backbone).
    Both land the whole-program post; the reclaimed deep scratch, the prologue
    slots, the already-written field-0/1 output cells, the address/pad cells and
    the `wd_offset`/`wd_length`/K34-scratch data cells are framed ambient across
    both. -/

set_option maxRecDepth 8000 in
/-- The field-2 backbone: field-2 stage `WB+80 → raIn`, both exits landing
    `wdWholePost`.  The upstream field-0/1 decode facts arrive as hypotheses;
    the accumulator carries the deep scratch cells, the saved slots, the reclaimed
    top cell (as `wdStackK20Deep`), the field-0/1 output cells and the data
    cells. -/
theorem wdBBField2
    (sp0 spW newSp raEntry raSaved listBase len outBase s3 s4 s5 v10 v11 v12 v13 v14
      v0 v1 s0Old s1Old s2Old oldOut wOldOff wOldLen oldOffset34 oldLen34 : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (houtalign : outBase.toNat % 8 = 0)
    (houtover : outBase.toNat + 48 < 2 ^ 64)
    (haddrlen : oldAddr.length = 20)
    (houtvalid : ∀ k, k < 20 →
      isValidByteAccess ((outBase + 16) + BitVec.ofNat 64 k) = true)
    (hf0 : Result bytes listBase listLen 0 (0 : Word) v0)
    (hf1 : Result bytes listBase listLen 1 (0 : Word) v1) :
    cpsTripleWithin ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
        (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8))))
      (WB + 80) raSaved fullCode
      ((((.x1 : Reg) ↦ᵣ raEntry) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen)) **
       (wdStackK20Deep spW ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
        ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
        bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
        (offsetCell ↦ₘ oldOffset34) ** (lengthCell ↦ₘ oldLen34)))
      (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
  have hstage := wdField2Stage spW raEntry listBase len outBase s3 s4 s5 wOldOff wOldLen
    v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hbytes hnowrap hover hvalid hnz
  have hbr := cpsBranchWithin_frameR
    (wdStackK20Deep spW ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
     ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
     ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
     bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
     (offsetCell ↦ₘ oldOffset34) ** (lengthCell ↦ₘ oldLen34))
    (by pcfw) hstage
  -- fail edge → DecodeFailure.field2List via wdK20FailArm
  have h_t : cpsTripleWithin (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8)))
      (WB + 212) raSaved fullCode
      (k20FailPost spW listBase wOldOff wOldLen
        { ra := WB + 112, s0 := listBase, s1 := len, s2 := outBase, s3 := s3, s4 := s4,
          s5 := s5 } bytes listLen **
       (wdStackK20Deep spW ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
        ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
        bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
        (offsetCell ↦ₘ oldOffset34) ** (lengthCell ↦ₘ oldLen34)))
      (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
    have harm : cpsTripleWithin 7 (WB + 212) raSaved fullCode
        (k20FailPost spW listBase wOldOff wOldLen
          { ra := WB + 112, s0 := listBase, s1 := len, s2 := outBase, s3 := s3, s4 := s4,
            s5 := s5 } bytes listLen **
         (wdStackK20Deep spW ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
          ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
          ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
          bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
          (offsetCell ↦ₘ oldOffset34) ** (lengthCell ↦ₘ oldLen34)))
        (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
          oldAddr pad4) := cpsTripleWithin_weaken
      (fun h hp => sepConj_mono_right
        (fun h' hf => by simp only [wdStackK20Deep] at hf ⊢; xperm_hyp hf) h hp)
      (fun _ hq => hq)
      (wdK20FailArm sp0 spW raSaved listBase wOldOff wOldLen outBase s0Old s1Old s2Old
        { ra := WB + 112, s0 := listBase, s1 := len, s2 := outBase, s3 := s3, s4 := s4,
          s5 := s5 } bytes oldAddr pad4 listLen
        ((outBase ↦ₘ v0) ** ((outBase + 8) ↦ₘ v1) ** bytesRegion (outBase + 16) oldAddr **
         bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut) **
         (offsetCell ↦ₘ oldOffset34) ** (lengthCell ↦ₘ oldLen34))
        hspW hret
        (fun offset len h hp => by
          refine ⟨v0, v1, oldOut, offset, len, oldOffset34, oldLen34, oldAddr, pad4, ?_⟩
          xperm_hyp hp))
    exact cpsTripleWithin_mono_nSteps (by omega) harm
  -- continue edge → length check + copy + field-3 backbone
  have h_f := wdField2ContEpi sp0 spW newSp raSaved listBase len outBase v0 v1 oldOut
    oldOffset34 oldLen34 s0Old s1Old s2Old s3 s4 s5 bytes oldAddr pad4 listLen hspW hnewSp
    hret hlenW hsalign hbytes hnowrap hover hvalid hnz houtalign houtover haddrlen houtvalid hf0 hf1
  exact cpsBranchWithin_merge_same_cr hbr h_t h_f

#print axioms wdBBField2

/-! ## Field-1 backbone merge

    Merge the field-1 (K34) stage's two exits: the parse-fail edge routes through
    `wdK34FailArm ... 1` (`DecodeFailure.field1`), the continue edge reshapes the
    K34 continue payload (`wdContReshape`), pins the field-1 `Result`, rebuilds
    the K34→K20 stack discipline and hands off to the field-2 backbone. -/

set_option maxRecDepth 8000 in
/-- The field-1 backbone: field-1 stage `WB+56 → raIn`, both exits landing
    `wdWholePost`.  The upstream field-0 decode fact `hf0` arrives as a hypothesis;
    field-1's own decode fact is pinned from the continue payload and threaded to
    the field-2 backbone. -/
theorem wdBBField1
    (sp0 spW newSp raEntry raSaved listBase len outBase oldOut1 oldOffset1 oldLen1 old14
      s3 s4 s5 v10 v11 v12 v13 v0 s0Old s1Old s2Old oldOut2 wOldOff wOldLen : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (houtalign : outBase.toNat % 8 = 0)
    (houtover : outBase.toNat + 48 < 2 ^ 64)
    (haddrlen : oldAddr.length = 20)
    (houtvalid : ∀ k, k < 20 →
      isValidByteAccess ((outBase + 16) + BitVec.ofNat 64 k) = true)
    (hf0 : Result bytes listBase listLen 0 (0 : Word) v0) :
    cpsTripleWithin ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
        ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
        (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8)))))
      (WB + 56) raSaved fullCode
      ((((.x1 : Reg) ↦ᵣ raEntry) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        ((outBase + 8) ↦ₘ oldOut1) ** (offsetCell ↦ₘ oldOffset1) ** (lengthCell ↦ₘ oldLen1)) **
       (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
        bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
        ((outBase + 40) ↦ₘ oldOut2) ** (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen)))
      (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
  have hstage := wdField1Stage spW newSp raEntry listBase len outBase oldOut1 oldOffset1
    oldLen1 old14 s3 s4 s5 v10 v11 v12 v13 bytes listLen hnewSp hlenW hsalign hbytes hnowrap hover
    hvalid hnz
  have hbr := cpsBranchWithin_frameR
    (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
     ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
     bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
     ((outBase + 40) ↦ₘ oldOut2) ** (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen))
    (by pcfw) hstage
  -- fail edge → DecodeFailure.field1 via wdK34FailArm
  have harm := wdK34FailArm sp0 spW newSp raSaved listBase oldOffset1 oldLen1 (WB + 76)
    s0Old s1Old s2Old { ra := WB + 76, s0 := listBase, s1 := len }
    { ra := B + 48, s0 := listBase, s1 := outBase + 8, s2 := outBase, s3 := s3, s4 := s4,
      s5 := s5 } bytes oldAddr pad4 listLen 1
    ((outBase ↦ₘ v0) ** bytesRegion (outBase + 16) oldAddr **
     bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut2) **
     (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen))
    hspW hnewSp hret
    (fun status v hnz hres => DecodeFailure.field1 status v hnz hres)
    (fun roff rlen ov' h hp => by
      refine ⟨v0, ov', oldOut2, wOldOff, wOldLen, roff, rlen, oldAddr, pad4, ?_⟩
      xperm_hyp hp)
  have h_t := cpsTripleWithin_mono_nSteps
    (show (7 : Nat) ≤ ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
        (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8)))) from by omega)
    harm
  -- continue edge → field-1 Result pinned, K34→K20 reshape, field-2 backbone
  have h_f : cpsTripleWithin ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
      (5 + (5 + (6 * (19 + 1)) +
      ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8))))
      (WB + 80) raSaved fullCode
      (k34ContPost spW newSp listBase (WB + 76) { ra := WB + 76, s0 := listBase, s1 := len }
        { ra := B + 48, s0 := listBase, s1 := outBase + 8, s2 := outBase, s3 := s3, s4 := s4,
          s5 := s5 } bytes listLen 1 **
       (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
        bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
        ((outBase + 40) ↦ₘ oldOut2) ** (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen)))
      (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
    -- expose the K34 continue existentials + pin the field-1 `Result`
    refine cpsTripleWithin_weaken
      (P := fun h => ∃ offset len' v12' x5' ss' ov,
        ((⌜Result bytes listBase listLen 1 (0 : Word) ov⌝ : Assertion) **
         (((.x1 ↦ᵣ (WB + 76)) **
           (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
             savedFrame newSp { ra := WB + 76, s0 := listBase, s1 := len }) **
            successPayload newSp listBase offset len' v12' x5' ss' (0 : Word) ov
              { ra := B + 48, s0 := listBase, s1 := outBase + 8, s2 := outBase, s3 := s3,
                s4 := s4, s5 := s5 } bytes listLen 1)) **
          (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
           ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
           bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
           ((outBase + 40) ↦ₘ oldOut2) ** (wdOffsetAddr ↦ₘ wOldOff) **
           (wdLengthAddr ↦ₘ wOldLen)))) h)
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hk, hacc⟩ := hp
        obtain ⟨offset, len', v12', x5', ss', ov, hbody⟩ := hk
        refine ⟨offset, len', v12', x5', ss', ov, ?_⟩
        have hRes : Result bytes listBase listLen 1 (0 : Word) ov := by
          obtain ⟨_, _, _, _, _, hbody2⟩ := hbody
          obtain ⟨_, _, _, _, _, hspp⟩ := hbody2
          unfold successPayload at hspp
          exact ((sepConj_pure_right _).1 hspp).2
        exact (sepConj_pure_left h).2 ⟨hRes, h1, h2, hd, hu, hbody, hacc⟩)
      (fun _ hq => hq) ?_
    refine cpsTripleWithin_exists_pre_gen (fun offset => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len' => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun v12' => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun x5' => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun ss' => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun ov => ?_)
    refine cpsTripleWithin_pure_pre (fun hf1 => ?_)
    -- reshape (K34 continue payload + accumulator) into (stack/x5-isolated form) ** regOwn x13 ** regOwn x14
    refine cpsTripleWithin_weaken
      (P := ((memOwn (spW - BitVec.ofNat 64 8) ** frameSlotsOwn frame newSp **
          stackFree newSp 8) ** (.x5 ↦ᵣ x5') ** (.x1 ↦ᵣ (WB + 76)) **
          (⌜Result bytes listBase listLen 1 (0 : Word) ov⌝ : Assertion) **
          (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
          (.x18 ↦ᵣ outBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ ss') ** (.x12 ↦ᵣ v12') ** regOwn .x6 **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes ** (wdOffsetAddr ↦ₘ wOldOff) **
          (wdLengthAddr ↦ₘ wOldLen) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
          ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ v0) **
          ((outBase + 8) ↦ₘ ov) ** bytesRegion (outBase + 16) oldAddr **
          bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut2) **
          (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len')) **
         regOwn .x13 ** regOwn .x14)
      (fun h hp => by
        have hcb := sepConj_mono_left
          (wdContReshape spW newSp listBase (WB + 76) offset len' v12' x5' ss' ov
            { ra := WB + 76, s0 := listBase, s1 := len }
            { ra := B + 48, s0 := listBase, s1 := outBase + 8, s2 := outBase, s3 := s3,
              s4 := s4, s5 := s5 } bytes listLen 1) h hp
        unfold wdContBundle at hcb
        xperm_hyp hcb)
      (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v13' v14' => ?_)
    refine cpsTripleWithin_weaken
      (fun h hp => by
        have hp0 := sepConj_mono_left sepConj_strip_pure_depth3 h hp
        have hg2 := sepConj_mono_left (sepConj_mono
          (fun h' hs => wdStack12_to_k20 spW h' (wdStack12_of_k34 spW newSp hnewSp h' hs))
          (sepConj_mono_left (regIs_implies_regOwn .x5))) h hp0
        xperm_hyp hg2)
      (fun _ hq => hq)
      (wdBBField2 sp0 spW newSp (WB + 76) raSaved listBase len outBase s3 s4 s5
        (0 : Word) ss' v12' v13' v14' v0 ov s0Old s1Old s2Old oldOut2 wOldOff wOldLen offset
        len' bytes oldAddr pad4 listLen hnewSp hspW hret hlenW hsalign hbytes hnowrap hover hvalid hnz
        houtalign houtover haddrlen houtvalid hf0 hf1)
  exact cpsBranchWithin_merge_same_cr hbr h_t h_f

#print axioms wdBBField1

/-! ## Field-0 backbone merge

    Merge the field-0 (K34) stage's two exits: the parse-fail edge routes through
    `wdK34FailArm ... 0` (`DecodeFailure.field0`), the continue edge reshapes the
    K34 continue payload (`wdContReshape`), pins the field-0 `Result`, and hands
    off directly to the field-1 backbone (K34→K34: the frame passes through with
    no stack transform).  This is the entry backbone; no upstream decode facts
    arrive. -/

set_option maxRecDepth 8000 in
/-- The field-0 backbone: field-0 stage `WB+32 → raIn`, both exits landing
    `wdWholePost`.  Field-0's own decode fact is pinned from the continue payload
    and threaded to the field-1 backbone. -/
theorem wdBBField0
    (sp0 spW newSp raEntry raSaved listBase len outBase oldOut0 oldOffset0 oldLen0 old14
      s3 s4 s5 v10 v11 v12 v13 fld1Out oldOut2 wOldOff wOldLen s0Old s1Old s2Old : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (houtalign : outBase.toNat % 8 = 0)
    (houtover : outBase.toNat + 48 < 2 ^ 64)
    (haddrlen : oldAddr.length = 20)
    (houtvalid : ∀ k, k < 20 →
      isValidByteAccess ((outBase + 16) + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
        ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
        (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8))))))
      (WB + 32) raSaved fullCode
      ((((.x1 : Reg) ↦ᵣ raEntry) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (outBase ↦ₘ oldOut0) ** (offsetCell ↦ₘ oldOffset0) ** (lengthCell ↦ₘ oldLen0)) **
       (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** ((outBase + 8) ↦ₘ fld1Out) **
        bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
        ((outBase + 40) ↦ₘ oldOut2) ** (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen)))
      (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
  have hstage := wdField0Stage spW newSp raEntry listBase len outBase oldOut0 oldOffset0
    oldLen0 old14 s3 s4 s5 v10 v11 v12 v13 bytes listLen hnewSp hlenW hsalign hbytes hnowrap hover
    hvalid hnz
  have hbr := cpsBranchWithin_frameR
    (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
     ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** ((outBase + 8) ↦ₘ fld1Out) **
     bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
     ((outBase + 40) ↦ₘ oldOut2) ** (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen))
    (by pcfw) hstage
  -- fail edge → DecodeFailure.field0 via wdK34FailArm
  have harm := wdK34FailArm sp0 spW newSp raSaved listBase oldOffset0 oldLen0 (WB + 52)
    s0Old s1Old s2Old { ra := WB + 52, s0 := listBase, s1 := len }
    { ra := B + 48, s0 := listBase, s1 := outBase, s2 := outBase, s3 := s3, s4 := s4,
      s5 := s5 } bytes oldAddr pad4 listLen 0
    (((outBase + 8) ↦ₘ fld1Out) ** bytesRegion (outBase + 16) oldAddr **
     bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut2) **
     (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen))
    hspW hnewSp hret
    (fun status v hnz hres => DecodeFailure.field0 status v hnz hres)
    (fun roff rlen ov' h hp => by
      refine ⟨ov', fld1Out, oldOut2, wOldOff, wOldLen, roff, rlen, oldAddr, pad4, ?_⟩
      xperm_hyp hp)
  have h_t := cpsTripleWithin_mono_nSteps
    (show (7 : Nat) ≤ ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
        ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
        (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8))))) from by omega)
    harm
  -- continue edge → field-0 Result pinned, K34→K34 passthrough, field-1 backbone
  have h_f : cpsTripleWithin ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9))) +
      ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
      ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
      (5 + (5 + (6 * (19 + 1)) +
      ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8)))))
      (WB + 56) raSaved fullCode
      (k34ContPost spW newSp listBase (WB + 52) { ra := WB + 52, s0 := listBase, s1 := len }
        { ra := B + 48, s0 := listBase, s1 := outBase, s2 := outBase, s3 := s3, s4 := s4,
          s5 := s5 } bytes listLen 0 **
       (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** ((outBase + 8) ↦ₘ fld1Out) **
        bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
        ((outBase + 40) ↦ₘ oldOut2) ** (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen)))
      (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
    refine cpsTripleWithin_weaken
      (P := fun h => ∃ offset len' v12' x5' ss' ov,
        ((⌜Result bytes listBase listLen 0 (0 : Word) ov⌝ : Assertion) **
         (((.x1 ↦ᵣ (WB + 52)) **
           (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
             savedFrame newSp { ra := WB + 52, s0 := listBase, s1 := len }) **
            successPayload newSp listBase offset len' v12' x5' ss' (0 : Word) ov
              { ra := B + 48, s0 := listBase, s1 := outBase, s2 := outBase, s3 := s3,
                s4 := s4, s5 := s5 } bytes listLen 0)) **
          (memOwn (spW - BitVec.ofNat 64 8) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
           ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** ((outBase + 8) ↦ₘ fld1Out) **
           bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
           ((outBase + 40) ↦ₘ oldOut2) ** (wdOffsetAddr ↦ₘ wOldOff) **
           (wdLengthAddr ↦ₘ wOldLen)))) h)
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hk, hacc⟩ := hp
        obtain ⟨offset, len', v12', x5', ss', ov, hbody⟩ := hk
        refine ⟨offset, len', v12', x5', ss', ov, ?_⟩
        have hRes : Result bytes listBase listLen 0 (0 : Word) ov := by
          obtain ⟨_, _, _, _, _, hbody2⟩ := hbody
          obtain ⟨_, _, _, _, _, hspp⟩ := hbody2
          unfold successPayload at hspp
          exact ((sepConj_pure_right _).1 hspp).2
        exact (sepConj_pure_left h).2 ⟨hRes, h1, h2, hd, hu, hbody, hacc⟩)
      (fun _ hq => hq) ?_
    refine cpsTripleWithin_exists_pre_gen (fun offset => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len' => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun v12' => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun x5' => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun ss' => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun ov => ?_)
    refine cpsTripleWithin_pure_pre (fun hf0 => ?_)
    refine cpsTripleWithin_weaken
      (P := ((memOwn (spW - BitVec.ofNat 64 8) ** frameSlotsOwn frame newSp **
          stackFree newSp 8) ** (.x5 ↦ᵣ x5') ** (.x1 ↦ᵣ (WB + 52)) **
          (⌜Result bytes listBase listLen 0 (0 : Word) ov⌝ : Assertion) **
          (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
          (.x18 ↦ᵣ outBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ ss') ** (.x12 ↦ᵣ v12') ** regOwn .x6 **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes ** (wdOffsetAddr ↦ₘ wOldOff) **
          (wdLengthAddr ↦ₘ wOldLen) ** (spW ↦ₘ raSaved) ** ((spW + 8) ↦ₘ s0Old) **
          ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old) ** (outBase ↦ₘ ov) **
          ((outBase + 8) ↦ₘ fld1Out) ** bytesRegion (outBase + 16) oldAddr **
          bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut2) **
          (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len')) **
         regOwn .x13 ** regOwn .x14)
      (fun h hp => by
        have hcb := sepConj_mono_left
          (wdContReshape spW newSp listBase (WB + 52) offset len' v12' x5' ss' ov
            { ra := WB + 52, s0 := listBase, s1 := len }
            { ra := B + 48, s0 := listBase, s1 := outBase, s2 := outBase, s3 := s3,
              s4 := s4, s5 := s5 } bytes listLen 0) h hp
        unfold wdContBundle at hcb
        xperm_hyp hcb)
      (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v13' v14' => ?_)
    refine cpsTripleWithin_weaken
      (fun h hp => by
        have hp0 := sepConj_mono_left sepConj_strip_pure_depth3 h hp
        have hg2 := sepConj_mono_left
          (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x5))) h hp0
        xperm_hyp hg2)
      (fun _ hq => hq)
      (wdBBField1 sp0 spW newSp (WB + 52) raSaved listBase len outBase fld1Out offset len'
        v14' s3 s4 s5 (0 : Word) ss' v12' v13' ov s0Old s1Old s2Old oldOut2 wOldOff wOldLen
        bytes oldAddr pad4 listLen hnewSp hspW hret hlenW hsalign hbytes hnowrap hover hvalid hnz
        houtalign houtover haddrlen houtvalid hf0)
  exact cpsBranchWithin_merge_same_cr hbr h_t h_f

#print axioms wdBBField0

/-! ## Whole-program caller contract

    `withdrawal_decode_spec_within = wdPrologue ;; wdBBField0`.  The prologue
    ([0]-[7]) allocates the frame and loads `s0/s1/s2`; the field-0 backbone
    ([8]-[59]) decodes all four fields and returns.  The caller-facing precondition
    owns the 12-cell scratch (`stackFree spW 12`, carved into the field-0 K34
    frame via `wdStack12_to_k34`), the four save slots, the 48-byte output struct,
    the RLP input, and the two guest data-cell pairs. -/

set_option maxRecDepth 8000 in
/-- Whole-program caller contract for `withdrawalDecode_prog`: decode the RLP
    withdrawal at `listBase` into the 48-byte output struct at `outBase`,
    returning `a0 = 0` with a genuine `Decoded` verdict or `a0 = 1` with a
    witnessed `DecodeFailure`. -/
theorem withdrawal_decode_spec_within
    (sp0 spW newSp raSaved s0Old s1Old s2Old listBase len outBase v13 v14 oldOut0
      oldOffset0 oldLen0 fld1Out oldOut2 wOldOff wOldLen s3 s4 s5 : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (houtalign : outBase.toNat % 8 = 0)
    (houtover : outBase.toNat + 48 < 2 ^ 64)
    (haddrlen : oldAddr.length = 20)
    (houtvalid : ∀ k, k < 20 →
      isValidByteAccess ((outBase + 16) + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (8 +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
        ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
        (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8)))))))
      WB raSaved fullCode
      (stackFree spW 12 ** (.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raSaved) ** (.x8 ↦ᵣ s0Old) **
       (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ len) **
       (.x12 ↦ᵣ outBase) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x19 ↦ᵣ s3) **
       (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
       memOwn spW ** memOwn (spW + 8) ** memOwn (spW + 16) ** memOwn (spW + 24) **
       bytesRegion listBase bytes ** (outBase ↦ₘ oldOut0) ** ((outBase + 8) ↦ₘ fld1Out) **
       bytesRegion (outBase + 16) oldAddr ** bytesRegion (outBase + 36) pad4 **
       ((outBase + 40) ↦ₘ oldOut2) ** (offsetCell ↦ₘ oldOffset0) ** (lengthCell ↦ₘ oldLen0) **
       (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen))
      (wdWholePost sp0 spW raSaved s0Old s1Old s2Old outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
  have hbb := wdBBField0 sp0 spW newSp raSaved raSaved listBase len outBase oldOut0
    oldOffset0 oldLen0 v14 s3 s4 s5 listBase len outBase v13 fld1Out oldOut2 wOldOff wOldLen
    s0Old s1Old s2Old bytes oldAddr pad4 listLen hnewSp hspW hret hlenW hsalign hbytes hnowrap hover
    hvalid hnz houtalign houtover haddrlen houtvalid
  have hpro := wdPrologue sp0 spW raSaved s0Old s1Old s2Old listBase len outBase
    ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** frameSlotsOwn frame newSp ** stackFree newSp 8 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
     (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes ** (outBase ↦ₘ oldOut0) **
     (offsetCell ↦ₘ oldOffset0) ** (lengthCell ↦ₘ oldLen0) ** memOwn (spW - BitVec.ofNat 64 8) **
     ((outBase + 8) ↦ₘ fld1Out) ** bytesRegion (outBase + 16) oldAddr **
     bytesRegion (outBase + 36) pad4 ** ((outBase + 40) ↦ₘ oldOut2) **
     (wdOffsetAddr ↦ₘ wOldOff) ** (wdLengthAddr ↦ₘ wOldLen)) (by pcfw) hspW
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun h hq => by xperm_hyp hq) hpro hbb
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) hcomp
  have hp2 := sepConj_mono_left (wdStack12_to_k34 spW newSp hnewSp) h hp
  xperm_hyp hp2

#print axioms withdrawal_decode_spec_within


/-! ## Anti-vacuity cover (#12476)

    Withdrawals use short-form list geometry (`|bytes| = 1 + listLen`), not
    header-concat. The old `hslack` was unsatisfiable on that exact-fit shape.
    Cover instantiates `withdrawal_decode_spec_within`'s real binders, including
    the output-window premises (`houtalign`/`houtover`/`haddrlen`/`houtvalid`). -/

/-- Short-form exact-fit cover with a disjoint 8-aligned output window. -/
example :
    let listLen := 1
    let bytes : List (BitVec 8) := List.replicate 2 (0 : BitVec 8)
    let listBase : Word := BitVec.ofNat 64 MEM_START
    let outBase : Word := BitVec.ofNat 64 0x1000
    let oldAddr : List (BitVec 8) := List.replicate 20 (0 : BitVec 8)
    (listBase.toNat % 8 = 0) ∧
    (listLen ≤ bytes.length) ∧
    (listBase.toNat + listLen + 9 < 2 ^ 64) ∧
    (listBase.toNat + bytes.length < 2 ^ 64) ∧
    (0 < bytes.length) ∧
    (∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) ∧
    (outBase.toNat % 8 = 0) ∧
    (outBase.toNat + 48 < 2 ^ 64) ∧
    (oldAddr.length = 20) ∧
    (∀ k, k < 20 →
      isValidByteAccess ((outBase + 16) + BitVec.ofNat 64 k) = true) := by
  refine ⟨?hsalign, ?hbytes, ?hnowrap, ?hover, ?hnz, ?hvalid,
    ?houtalign, ?houtover, ?haddrlen, ?houtvalid⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro k hk
    have hk2 : k < 2 := by simpa using hk
    have hsum :
        (BitVec.ofNat 64 MEM_START + BitVec.ofNat 64 k).toNat = 32 + k := by
      simp only [MEM_START]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 32 + k < 2 ^ 64)]
    simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    refine Or.inl (Or.inl ?_)
    constructor
    · rw [hsum]; change 32 ≤ 32 + k; omega
    · rw [hsum]; change 32 + k ≤ 0x78000000; omega
  · decide
  · decide
  · decide
  · intro k hk
    have hbase : BitVec.ofNat 64 0x1000 + (16 : Word) = BitVec.ofNat 64 0x1010 := by
      decide
    have hsum :
        ((BitVec.ofNat 64 0x1000 + (16 : Word)) + BitVec.ofNat 64 k).toNat =
          0x1010 + k := by
      have hk64 : k < 2 ^ 64 := by omega
      rw [hbase, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x1010 < 2 ^ 64),
        Nat.mod_eq_of_lt hk64,
        Nat.mod_eq_of_lt (by omega : 0x1010 + k < 2 ^ 64)]
    simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    refine Or.inl (Or.inl ?_)
    constructor
    · rw [hsum]; change 32 ≤ 0x1010 + k; omega
    · rw [hsum]; change 0x1010 + k ≤ 0x78000000; omega

end EvmAsm.Codegen.WithdrawalDecodeSpec
