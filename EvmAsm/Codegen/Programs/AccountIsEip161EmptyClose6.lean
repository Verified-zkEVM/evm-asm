/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose6

  Field-1 (balance) and field-0 (nonce) OK-paths and the top-level whole-program
  assembly for the K137 contract `account_is_eip161_empty_spec_within`
  (`AccountFields.lean`).

  Builds on the field-3 subtree (`AccountIsEip161EmptyClose5.lean`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose5

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells. -/
local macro "pcfR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | unfold aieSlots
    | unfold savedFrame)

/-- `k`-th instruction membership into the full closure `fullCode`. -/
local macro "aieFC" k:term ", " A:term ", " ins:term : term =>
  `((fun a i hi => aie_mono a i
      (CodeReq.ofProg_mem_at AB $A accountIsEip161Empty_prog $k $ins (by bv_omega)
        (by rw [aie_prog_length]; omega) rfl (by rw [aie_prog_length]; norm_num) a i hi)))

/-- Peel a leading existential out of the left operand of a separating
    conjunction (local copy). -/
private theorem aieSepConj_exists_left' {α : Sort _} {F : α → Assertion} {R : Assertion} :
    ∀ h, ((fun hp => ∃ a, F a hp) ** R) h → ∃ a, (F a ** R) h := by
  rintro h ⟨h1, h2, hd, hu, ⟨a, hF⟩, hR⟩
  exact ⟨a, h1, h2, hd, hu, hF, hR⟩

/-- Introduce TWO owned registers' values at once (trailing `regOwn` chain). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn2
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 : Reg} {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, ⟨v2, hv2⟩⟩ := hO1
  exact h v1 v2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, hv2⟩, hRb⟩ hpc

/-! ## Field-1 (balance) size-check head ([45]-[49], `AB+180 → {AB+396, AB+200}`) -/

set_option maxRecDepth 8000 in
theorem aieField1SizeHead (v5 v6 v7 len : Word) :
    cpsBranchWithin 5 (AB + 180) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (LenA ↦ₘ len))
      (AB + 396)
        ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
          (LenA ↦ₘ len) ** ⌜BitVec.ult (32 : Word) len⌝)
      (AB + 200)
        ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
          (LenA ↦ₘ len) ** ⌜¬ BitVec.ult (32 : Word) len⌝) := by
  -- [45-46] la x5 = aie_length
  have hau45 := CodeReq.ofProg_mem_at AB (AB + 180) accountIsEip161Empty_prog 45
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 180))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had46 := CodeReq.ofProg_mem_at AB (AB + 184) accountIsEip161Empty_prog 46
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.aie_length
      (GuestAddrs.account_is_eip161_empty + 180))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h46 := EvmAsm.Rv64.la_materialize_within .x5 v5 (AB + 180) LenA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau45 a i hi))
    (fun a i hi => aie_mono a i (had46 a i hi))
  have f46 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (LenA ↦ₘ len)) (by pcfR) h46
  -- [47] LD x6 x5 0
  have h47 := ld_spec_gen_within .x6 .x5 LenA v6 len (0 : BitVec 12) (AB + 188) (by decide)
  rw [show LenA + signExtend12 (0 : BitVec 12) = LenA from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h47
  have e47 := cpsTripleWithin_extend_code (aieFC 47, (AB + 188), (.LD .x6 .x5 (0 : BitVec 12))) h47
  have f47 := cpsTripleWithin_frameR ((.x7 ↦ᵣ v7)) (by pcfR) e47
  -- [48] LI x7 32
  have h48 := li_spec_gen_within .x7 v7 (32 : Word) (AB + 192) (by decide)
  have e48 := cpsTripleWithin_extend_code (aieFC 48, (AB + 192), (.LI .x7 (32 : Word))) h48
  have f48 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (LenA ↦ₘ len)) (by pcfR) e48
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f46 f47
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f48
  -- [49] BLTU x7 x6 : 32 < len → AB+396 ; ¬ → AB+200
  have hbltu := bltu_spec_gen_within .x7 .x6 (200 : BitVec 13) (32 : Word) len (AB + 196)
  rw [show (AB + 196 : Word) + signExtend13 (200 : BitVec 13) = AB + 396 from by
      rw [show signExtend13 (200 : BitVec 13) = (200 : Word) from by decide]; bv_omega,
    show (AB + 196 : Word) + 4 = AB + 200 from by bv_omega] at hbltu
  have ebltu := cpsBranchWithin_extend_code
    (aieFC 49, (AB + 196), (.BLTU .x7 .x6 (200 : BitVec 13))) hbltu
  have fbltu := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ LenA) ** (LenA ↦ₘ len)) (by pcfR) ebltu
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_chunked hp) s2 fbltu
  refine cpsBranchWithin_mono_nSteps (by omega)
    (cpsBranchWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) (fun _ hp => by xperm_chunked hp) hbr)

#print axioms aieField1SizeHead

/-! ## Field-1 (balance) content-pointer setup ([50]-[53], `AB+200 → AB+216`) -/

set_option maxRecDepth 8000 in
theorem aieField1PtrSetup (v5 accBase v28 offset : Word) :
    cpsTripleWithin 4 (AB + 200) (AB + 216) fullCode
      ((.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ v28) ** (OffA ↦ₘ offset))
      ((.x5 ↦ᵣ OffA) ** (.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ (accBase + offset)) ** (OffA ↦ₘ offset)) := by
  -- [50-51] la x5 = aie_offset
  have hau50 := CodeReq.ofProg_mem_at AB (AB + 200) accountIsEip161Empty_prog 50
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 200))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have had51 := CodeReq.ofProg_mem_at AB (AB + 204) accountIsEip161Empty_prog 51
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.aie_offset
      (GuestAddrs.account_is_eip161_empty + 200))) (by bv_omega)
    (by rw [aie_prog_length]; norm_num) rfl (by rw [aie_prog_length]; norm_num)
  have h51 := EvmAsm.Rv64.la_materialize_within .x5 v5 (AB + 200) OffA (by decide)
    (by decide) (fun a i hi => aie_mono a i (hau50 a i hi))
    (fun a i hi => aie_mono a i (had51 a i hi))
  have f51 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ accBase) ** (.x28 ↦ᵣ v28) ** (OffA ↦ₘ offset)) (by pcfR) h51
  -- [52] LD x28 x5 0
  have h52 := ld_spec_gen_within .x28 .x5 OffA v28 offset (0 : BitVec 12) (AB + 208) (by decide)
  rw [show OffA + signExtend12 (0 : BitVec 12) = OffA from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h52
  have e52 := cpsTripleWithin_extend_code (aieFC 52, (AB + 208), (.LD .x28 .x5 (0 : BitVec 12))) h52
  have f52 := cpsTripleWithin_frameR ((.x8 ↦ᵣ accBase)) (by pcfR) e52
  -- [53] ADD x28 x8 x28
  have h53 := add_spec_gen_rd_eq_rs2_within .x28 .x8 accBase offset (AB + 212) (by decide)
  have e53 := cpsTripleWithin_extend_code (aieFC 53, (AB + 212), (.ADD .x28 .x8 .x28)) h53
  have f53 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ OffA) ** (OffA ↦ₘ offset)) (by pcfR) e53
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f51 f52
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f53
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s2)

#print axioms aieField1PtrSetup

/-! ## Generic field body frame + a0=1 size-fail continuation -/

/-- The frame carried around a field body, generic over the per-call return
    address `retA` (`aieF3Frame` is the `retA = AB+272` instance). -/
def aieFldFrame (retA spA newSp accBase lenW outPtr raIn c8 c9 c18 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (offset v11 v12 : Word) : Assertion :=
  (.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion accBase bytes ** (OffA ↦ₘ offset) **
  savedFrame newSp (mkSaved retA accBase lenW outPtr s3 s4 s5) **
  aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)) **
  bytesRegion ECB aieEmptyCodeHashBytes

set_option maxRecDepth 8000 in
/-- The a0=1 (parse/size-fail) continuation for the nonce/balance size checks
    (`AB+396 → raIn`): from the size-head-pass state, set `a0 = 1` and fold into
    the abstract return post.  Generic over the pure branch condition `P`. -/
theorem aieSizeFail1Cont
    (sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) (offset len v11 v12 : Word) (P : Prop)
    (hspA : spA = sp0 + signExtend12 (-40 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 8 (AB + 396) raIn fullCode
      (((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (LenA ↦ₘ len) ** ⌜P⌝) **
        aieFldFrame retA spA newSp accBase lenW outPtr raIn c8 c9 c18 s3 s4 s5 bytes offset v11 v12)
      (aiePost sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen) := by
  have hepi := aieRetFail sp0 spA raIn c8 c9 c18 retA accBase lenW outPtr (0 : Word)
    ((outPtr ↦ₘ (0 : Word)) ** aieJunk newSp accBase bytes)
    (pcFree_sepConj pcFree_memIs (pcFree_aieJunk _ _ _)) hspA hret
  refine cpsTripleWithin_weaken (fun h hst => ?_) (fun h hq => ?_) hepi
  · have hst1 := sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (fun h3 hpf => ((sepConj_pure_right h3).1 hpf).1)))) h hst
    have hst2 : ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ spA) ** aieSlots spA raIn c8 c9 c18 **
        (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) **
        aieResMixedSizeFail newSp accBase outPtr bytes LenA len (32 : Word) v11 v12 s3 s4 s5
          offset len retA accBase lenW outPtr s3 s4 s5) h := by
      unfold aieFldFrame savedFrame at hst1
      simp only [mkSaved] at hst1
      unfold aieResMixedSizeFail
      xperm_chunked hst1
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (aieResMixedSizeFail_to_junk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))))))) h hst2
  · exact aiePost_intro sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen 1 0
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h hq

#print axioms aieSizeFail1Cont

set_option maxRecDepth 8000 in
/-- Downgrade the saved-frame cells to the owned frame slots (`frameSlotsOwn`),
    the shape the next K20 call's precondition (`aieMidPre`) expects. -/
theorem savedFrame_to_frameSlotsOwn (newSp : Word) (saved : Saved) : ∀ h,
    savedFrame newSp saved h → frameSlotsOwn listNthFrame newSp h := by
  intro h hp
  have h2 := savedFrame_to_memOwns newSp saved h hp
  unfold frameSlotsOwn listNthFrame
  simp only [List.foldr_cons, List.foldr_nil]
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
      show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
      show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
      show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
      show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide,
      show newSp + (0 : Word) = newSp from by bv_omega]
  rw [sepConj_emp_right']
  exact h2

#print axioms savedFrame_to_frameSlotsOwn

/-- The K20-call footprint (`aieMidPre`) residual as it emerges from the previous
    field's all-zero loop exit: `x5`/`x6`/`x7` still `regIs`, the frame still
    `savedFrame`. -/
def aieMidResidual (spA newSp accBase lenW outPtr raIn c8 c9 c18 v1 v10 v11 v12 v13 v14
    w5 w6 w7 outv oldOff oldLen retA s3 s4 s5 : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) **
  (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x1 ↦ᵣ v1) ** (.x10 ↦ᵣ v10) **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
  (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion accBase bytes ** savedFrame newSp (mkSaved retA accBase lenW outPtr s3 s4 s5) **
  (outPtr ↦ₘ outv) ** (OffA ↦ₘ oldOff) ** (LenA ↦ₘ oldLen) ** aieSlots spA raIn c8 c9 c18

set_option maxRecDepth 8000 in
theorem aieMidResidual_to_aieMidPre (spA newSp accBase lenW outPtr raIn c8 c9 c18
    v1 v10 v11 v12 v13 v14 w5 w6 w7 outv oldOff oldLen retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) : ∀ h,
    aieMidResidual spA newSp accBase lenW outPtr raIn c8 c9 c18 v1 v10 v11 v12 v13 v14
      w5 w6 w7 outv oldOff oldLen retA s3 s4 s5 bytes h →
    aieMidPre spA newSp accBase lenW outPtr raIn c8 c9 c18 v1 v10 v11 v12 v13 v14
      outv oldOff oldLen s3 s4 s5 bytes h := by
  intro h hp
  unfold aieMidResidual at hp
  unfold aieMidPre
  refine sepConj_mono (fun _ h => h) ?_ h hp
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (regIs_implies_regOwn .x5) ?_
  refine sepConj_mono (regIs_implies_regOwn .x6) ?_
  refine sepConj_mono (regIs_implies_regOwn .x7) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (savedFrame_to_frameSlotsOwn newSp
    (mkSaved retA accBase lenW outPtr s3 s4 s5)) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  exact fun _ h => h

#print axioms aieMidResidual_to_aieMidPre

/-! ## Field-1 (balance) content continuation (`AB+200 → raIn`) -/

set_option maxRecDepth 8000 in
/-- Field-1 balance content continuation: materialise the content cursor, run the
    all-zero byte scan, and on a fully-zero balance continue into the field-3
    subtree (`aieField3Cont`); on the first nonzero byte return not-empty.  Threads
    the field-0 facts and supplies field-1's own facts to the field-3 model tie. -/
theorem aieField1ContentCont
    (sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) (offset len v11 v12 : Word) (o0 l0 : Word)
    (hspA : spA = sp0 + signExtend12 (-40 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hnewSp : newSp = spA + signExtend12 (-64 : BitVec 12))
    (hlistLenW : lenW = BitVec.ofNat 64 listLen)
    (halign : accBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true)
    (hoverL : accBase.toNat + listLen + 9 < 2 ^ 64)
    (hbound : ∀ o next len', o ≤ listLen →
      EvmAsm.Rv64.RLP.rlpItemDecode bytes o (accBase + BitVec.ofNat 64 o)
        (accBase + BitVec.ofNat 64 listLen) next len' →
      (next - len' - accBase).toNat + len'.toNat ≤ bytes.length)
    (hS1 : Success bytes accBase listLen 1 offset len)
    (hS0 : Success bytes accBase listLen 0 o0 l0) (hl0 : l0.toNat ≤ 8)
    (hz0 : ∀ k, k < l0.toNat → bytes.getD (o0.toNat + k) 0 = 0) :
    cpsTripleWithin 1100 (AB + 200) raIn fullCode
      (((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (LenA ↦ₘ len) **
          ⌜¬ BitVec.ult (32 : Word) len⌝) **
        aieFldFrame (AB + 176) spA newSp accBase lenW outPtr raIn c8 c9 c18 s3 s4 s5
          bytes offset v11 v12)
      (aiePost sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_pure hp) (fun _ hq => hq)
    (cpsTripleWithin_pure_pre (P := ¬ BitVec.ult (32 : Word) len)
      (H := ((.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (LenA ↦ₘ len)) **
        aieFldFrame (AB + 176) spA newSp accBase lenW outPtr raIn c8 c9 c18 s3 s4 s5
          bytes offset v11 v12)
      (fun hnu => ?_))
  have hle : len.toNat ≤ 32 := by
    have h32 : ((32 : Word)).toNat = 32 := by decide
    by_contra hc
    exact hnu (by simp only [BitVec.ult, decide_eq_true_eq]; omega)
  have hspan : offset.toNat + len.toNat ≤ bytes.length :=
    aieSpanBound bytes accBase listLen 1 offset len hoverL hbound hS1
  by_cases hz : ∀ k, k < len.toNat → bytes.getD (offset.toNat + k) 0 = 0
  · -- ALL-ZERO balance → continue into field 3
    refine cpsTripleWithin_weaken (fun h hp => by unfold aieFldFrame at hp; xperm_chunked hp)
      (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn4
        (P := (.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (LenA ↦ₘ len) **
          (.x1 ↦ᵣ (AB + 176)) ** (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes ** (OffA ↦ₘ offset) **
          savedFrame newSp (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) **
          aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)) **
          bytesRegion ECB aieEmptyCodeHashBytes)
        (r1 := .x13) (r2 := .x14) (r3 := .x28) (r4 := .x29) (fun v13 v14 v28 v29 => ?_))
    have hptr := aieField1PtrSetup LenA accBase v28 offset
    have hptrF := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ len) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
      (by pcfR) hptr
    have hloop := aieBalAllZero accBase bytes offset.toNat len.toNat 0 v29
      halign (by omega) hover hvalid (fun k hk => by
        rw [show offset.toNat + 0 + k = offset.toNat + k from by omega]; exact hz k hk)
    rw [show (BitVec.ofNat 64 len.toNat : Word) = len from (word_eq_ofNat_toNat len).symm,
        show accBase + BitVec.ofNat 64 (offset.toNat + 0) = accBase + offset from by
          rw [Nat.add_zero]; rw [← word_eq_ofNat_toNat offset]] at hloop
    have hloopC := cpsTripleWithin_extend_code aie_mono hloop
    have hloopF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ OffA) ** (.x8 ↦ᵣ accBase) ** (OffA ↦ₘ offset)) (by pcfR) hloopC
    have hT0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hptrF hloopF
    have hT := cpsTripleWithin_frameR
      ((.x7 ↦ᵣ (32 : Word)) ** (.x1 ↦ᵣ (AB + 176)) ** (.x2 ↦ᵣ spA) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        regOwn .x30 ** regOwn .x31 ** (LenA ↦ₘ len) **
        savedFrame newSp (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) **
        aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)) **
        bytesRegion ECB aieEmptyCodeHashBytes) (by pcfR) hT0
    have hcont := aieField3Cont sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18
      (AB + 176) (0 : Word) v11 v12 v13 v14 s3 s4 s5 bytes listLen offset len o0 l0 offset len
      hspA hret hnewSp hlistLenW halign hslack hover hvalid hoverL hbound
      hS0 hl0 hz0 hS1 hle hz
    have hfull := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
        have hp2 : (aieMidResidual spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 176)
            (0 : Word) v11 v12 v13 v14 OffA (0 : Word) (32 : Word) (0 : Word) offset len
            (AB + 176) s3 s4 s5 bytes ** bytesRegion ECB aieEmptyCodeHashBytes) h := by
          unfold aieMidResidual; xperm_chunked hp
        exact sepConj_mono_left (aieMidResidual_to_aieMidPre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _) h hp2)
      hT hcont
    refine cpsTripleWithin_mono_nSteps ?_
      (cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ hq => hq) hfull)
    omega
  · -- NONZERO balance byte → not-empty
    obtain ⟨j, hj, hjz, hjnz⟩ := first_mismatch
      (P := fun k => bytes.getD (offset.toNat + k) 0 = 0) (n := len.toNat) hz
    refine cpsTripleWithin_weaken (fun h hp => by unfold aieFldFrame at hp; xperm_chunked hp)
      (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn2
        (P := (.x5 ↦ᵣ LenA) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (LenA ↦ₘ len) **
          (.x1 ↦ᵣ (AB + 176)) ** (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
          regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes ** (OffA ↦ₘ offset) **
          savedFrame newSp (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) **
          aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)) **
          bytesRegion ECB aieEmptyCodeHashBytes)
        (r1 := .x28) (r2 := .x29) (fun v28 v29 => ?_))
    have hptr := aieField1PtrSetup LenA accBase v28 offset
    have hptrF := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ len) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
      (by pcfR) hptr
    have hloop := aieBalNonEmpty accBase bytes offset.toNat len.toNat 0 j v29
      halign (by omega) hover hvalid hj (fun k hk => by
        rw [show offset.toNat + 0 + k = offset.toNat + k from by omega]; exact hjz k hk)
      (by rw [show offset.toNat + 0 + j = offset.toNat + j from by omega]; exact hjnz)
    rw [show (BitVec.ofNat 64 len.toNat : Word) = len from (word_eq_ofNat_toNat len).symm,
        show accBase + BitVec.ofNat 64 (offset.toNat + 0) = accBase + offset from by
          rw [Nat.add_zero]; rw [← word_eq_ofNat_toNat offset]] at hloop
    have hloopC := cpsTripleWithin_extend_code aie_mono hloop
    have hloopF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ OffA) ** (.x8 ↦ᵣ accBase) ** (OffA ↦ₘ offset)) (by pcfR) hloopC
    have hT0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hptrF hloopF
    have hT := cpsTripleWithin_frameR
      ((.x7 ↦ᵣ (32 : Word)) ** (.x1 ↦ᵣ (AB + 176)) ** (.x2 ↦ᵣ spA) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
        regOwn .x30 ** regOwn .x31 ** (LenA ↦ₘ len) **
        savedFrame newSp (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) **
        aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)) **
        bytesRegion ECB aieEmptyCodeHashBytes) (by pcfR) hT0
    have hepi := aieRetNotEmpty sp0 spA raIn c8 c9 c18 (AB + 176) accBase lenW outPtr
      (0 : Word) (0 : Word) (aieJunkNoX0 newSp accBase bytes)
      (pcFree_aieJunkNoX0 _ _ _) hspA hret
    have hfull := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
        have hp2 : ((.x1 ↦ᵣ (AB + 176)) ** (.x2 ↦ᵣ spA) ** aieSlots spA raIn c8 c9 c18 **
            (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (0 : Word)) **
            aieResMixedNoX0 newSp accBase bytes OffA (32 : Word) v11 v12 s3 s4 s5 offset len
              (AB + 176) accBase lenW outPtr s3 s4 s5) h := by
          unfold savedFrame at hp
          simp only [mkSaved] at hp
          unfold aieResMixedNoX0; xperm_chunked hp
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right
              (aieResMixedNoX0_to_aieJunkNoX0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))))))))) h hp2)
      hT hepi
    refine cpsTripleWithin_mono_nSteps ?_
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun h hq => aieNotEmptyPost_to_aiePost sp0 spA raIn c8 c9 c18 newSp accBase outPtr
          bytes listLen h hq) hfull)
    omega

#print axioms aieField1ContentCont

/-! ## Field-1 (balance) OK path (`AB+180 → raIn`) -/

set_option maxRecDepth 8000 in
/-- Field-1 OK path: from the successful K20 return at `AB+180`, run the balance
    size check and all-zero scan, continuing into the field-3 subtree.  Threads
    the field-0 facts. -/
theorem aieField1OK
    (sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) (o0 l0 : Word)
    (hspA : spA = sp0 + signExtend12 (-40 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hnewSp : newSp = spA + signExtend12 (-64 : BitVec 12))
    (hlistLenW : lenW = BitVec.ofNat 64 listLen)
    (halign : accBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true)
    (hoverL : accBase.toNat + listLen + 9 < 2 ^ 64)
    (hbound : ∀ o next len', o ≤ listLen →
      EvmAsm.Rv64.RLP.rlpItemDecode bytes o (accBase + BitVec.ofNat 64 o)
        (accBase + BitVec.ofNat 64 listLen) next len' →
      (next - len' - accBase).toNat + len'.toNat ≤ bytes.length)
    (hS0 : Success bytes accBase listLen 0 o0 l0) (hl0 : l0.toNat ≤ 8)
    (hz0 : ∀ k, k < l0.toNat → bytes.getD (o0.toNat + k) 0 = 0) :
    cpsTripleWithin 1105 (AB + 180) raIn fullCode
      (aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 176) s3 s4 s5
          bytes (0 : Word) listLen 1 **
        bytesRegion ECB aieEmptyCodeHashBytes)
      (aiePost sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen) := by
  have key : cpsTripleWithin 1105 (AB + 180) raIn fullCode
      (fun h => ∃ offset len v11 v12,
        ((aieCallCore spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 176) s3 s4 s5
            bytes (0 : Word) (0 : Word) offset len v11 v12 **
          ⌜Success bytes accBase listLen 1 offset len⌝) **
          bytesRegion ECB aieEmptyCodeHashBytes) h)
      (aiePost sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen) := by
    refine cpsTripleWithin_exists_assertion (fun offset => ?_)
    refine cpsTripleWithin_exists_assertion (fun len => ?_)
    refine cpsTripleWithin_exists_assertion (fun v11 => ?_)
    refine cpsTripleWithin_exists_assertion (fun v12 => ?_)
    rw [show ((aieCallCore spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 176) s3 s4 s5
            bytes (0 : Word) (0 : Word) offset len v11 v12 **
          ⌜Success bytes accBase listLen 1 offset len⌝) **
          bytesRegion ECB aieEmptyCodeHashBytes)
        = (⌜Success bytes accBase listLen 1 offset len⌝ **
          (aieCallCore spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 176) s3 s4 s5
            bytes (0 : Word) (0 : Word) offset len v11 v12 **
          bytesRegion ECB aieEmptyCodeHashBytes)) from by
          rw [sepConj_assoc', sepConj_left_comm']]
    refine cpsTripleWithin_pure_pre (fun hS1 => ?_)
    refine cpsTripleWithin_weaken (fun h hp => by unfold aieCallCore at hp; xperm_chunked hp)
      (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn3
        (P := (.x1 ↦ᵣ (AB + 176)) ** (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion accBase bytes ** (OffA ↦ₘ offset) ** (LenA ↦ₘ len) **
          savedFrame newSp (mkSaved (AB + 176) accBase lenW outPtr s3 s4 s5) **
          aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ (0 : Word)) **
          bytesRegion ECB aieEmptyCodeHashBytes)
        (r1 := .x5) (r2 := .x6) (r3 := .x7) (fun v5 v6 v7 => ?_))
    have hbr := cpsBranchWithin_frameR
      (aieFldFrame (AB + 176) spA newSp accBase lenW outPtr raIn c8 c9 c18 s3 s4 s5
        bytes offset v11 v12)
      (by pcfR) (aieField1SizeHead v5 v6 v7 len)
    have hsf := aieSizeFail1Cont sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 (AB + 176)
      s3 s4 s5 bytes listLen offset len v11 v12 (BitVec.ult (32 : Word) len) hspA hret
    have hcc := aieField1ContentCont sp0 spA newSp raIn accBase lenW outPtr c8 c9 c18 s3 s4 s5
      bytes listLen offset len v11 v12 o0 l0 hspA hret hnewSp hlistLenW halign hslack hover
      hvalid hoverL hbound hS1 hS0 hl0 hz0
    have hmerge := cpsBranchWithin_merge_same_cr hbr
      (cpsTripleWithin_mono_nSteps (by omega) hsf) hcc
    exact cpsTripleWithin_weaken (fun h hp => by unfold aieFldFrame; xperm_chunked hp)
      (fun _ hq => hq) hmerge
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) key
  unfold aieSelected at hp
  obtain ⟨offset, hp⟩ := aieSepConj_exists_left' h hp
  obtain ⟨len, hp⟩ := aieSepConj_exists_left' h hp
  obtain ⟨v11, hp⟩ := aieSepConj_exists_left' h hp
  obtain ⟨v12, hp⟩ := aieSepConj_exists_left' h hp
  exact ⟨offset, len, v11, v12, hp⟩

#print axioms aieField1OK

end EvmAsm.Codegen.AccountIsEip161EmptySpec
