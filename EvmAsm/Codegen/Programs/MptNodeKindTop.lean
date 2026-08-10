/-
  Body compose + ABI-frame wrap for `mpt_node_kind` (#11799 dep).

  Posts `MptNodeKindResult` (operational, arity-exact). No input-domain gate
  → registry `.proven` once the top triple lands.
-/

import EvmAsm.Codegen.Programs.MptNodeKindBody
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptNodeKindSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! ## Body-exit ambient (regsOwnAt frame + kind in a0) -/

/-- Shared ambient after every arm reaches the epilogue join (pc 48).
    Frame regs + scratch temps are owned (values dead — epi restores).
    BSS cells keep final written values (count / path off / path len). -/
def bodyExitAmb (newSp : Word) (ks : KindSaved) (kindW : Word)
    (listBase : Word) (bytes : List (BitVec 8))
    (countW offW lenW : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) ** kindSavedFrame newSp ks ** regsOwnAt kindFrame **
  (.x10 ↦ᵣ kindW) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion listBase bytes **
  (MnkCount ↦ₘ countW) ** (MnkPathOff ↦ₘ offW) ** (MnkPathLen ↦ₘ lenW) **
  stackFree newSp 8

theorem bodyExitAmb_pcFree (newSp : Word) (ks : KindSaved) (kindW : Word)
    (listBase : Word) (bytes : List (BitVec 8))
    (countW offW lenW : Word) :
    (bodyExitAmb newSp ks kindW listBase bytes countW offW lenW).pcFree := by
  unfold bodyExitAmb kindSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
    | exact pcFree_regsOwnAt _ | apply pcFree_sepConj

theorem regsOwnAt_kindFrame :
    regsOwnAt kindFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9) := by
  simp [kindFrame, regsOwnAt, sepConj_emp_right']

/-- Body post: ambient + pure operational result. -/
def bodyPost (newSp : Word) (ks : KindSaved) (kind : Nat)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word) : Assertion :=
  bodyExitAmb newSp ks (BitVec.ofNat 64 kind) listBase bytes countW offW lenW **
  ⌜MptNodeKindResult bytes listBase listLen oldCount oldOff oldLen kind⌝

private theorem kindW_one : BitVec.ofNat 64 1 = (1 : Word) := rfl
private theorem kindW_two : BitVec.ofNat 64 2 = (2 : Word) := rfl
private theorem kindW_three : BitVec.ofNat 64 3 = (3 : Word) := rfl

private theorem hpKind_ext (b : BitVec 8) (h : b.toNat / 16 < 2) :
    hpKind b = 1 := by unfold hpKind; simp [h]
private theorem hpKind_leaf (b : BitVec 8) (hlo : 2 ≤ b.toNat / 16)
    (hhi : b.toNat / 16 < 4) : hpKind b = 2 := by
  unfold hpKind; simp [Nat.not_lt.mpr hlo, hhi]
private theorem hpKind_fail (b : BitVec 8) (h : 4 ≤ b.toNat / 16) :
    hpKind b = 3 := by
  unfold hpKind
  have h2 : ¬ b.toNat / 16 < 2 := Nat.not_lt.mpr (Nat.le_trans (by decide : (2:Nat) ≤ 4) h)
  have h4 : ¬ b.toNat / 16 < 4 := Nat.not_lt.mpr h
  simp [h2, h4]

/-! ## HP nibble classify → kind at epi -/

/-- Existential post as Assertion for nibble classify. -/
def hpClassifyPost (b : BitVec 8) (F : Assertion) : Assertion :=
  fun h => ∃ x30v : Word,
    ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ x30v) **
      (.x10 ↦ᵣ (BitVec.ofNat 64 (hpKind b))) ** F) h

/-- From nibble-prep post (pc37): case on high nibble → kind at pc48.
    Fuel upper bound 5 (leaf/fail arms). -/
theorem hp_classify_nibble
    (b : BitVec 8) (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (pc 37) (pc 48) fullCode
      ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (2 : Word)) **
        (.x10 ↦ᵣ v10) ** F)
      (hpClassifyPost b F) := by
  by_cases h2 : b.toNat / 16 < 2
  · have hk := hpKind_ext b h2
    have h := hp_ext_from_nibble b v10 h2 F hF
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h)
    refine ⟨(2 : Word), ?_⟩
    simp only [hk, kindW_one] at hq ⊢
    xperm_chunked hq
  · by_cases h4 : b.toNat / 16 < 4
    · have hlo : 2 ≤ b.toNat / 16 := Nat.not_lt.mp h2
      have hk := hpKind_leaf b hlo h4
      have h := hp_leaf_from_nibble b v10 hlo h4 F hF
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h
      refine ⟨(4 : Word), ?_⟩
      simp only [hk, kindW_two] at hq ⊢
      xperm_chunked hq
    · have hge : 4 ≤ b.toNat / 16 := Nat.not_lt.mp h4
      have hk := hpKind_fail b hge
      have h := hp_fail_from_nibble b v10 hge F hF
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h
      refine ⟨(4 : Word), ?_⟩
      simp only [hk, kindW_three] at hq ⊢
      xperm_chunked hq

/-- Non-empty path: nempty + prep + classify (pc32→pc48). Fuel 1+4+5 = 10. -/
theorem hp_nempty_classify
    (listBase pathOff pathLen : Word) (bytes : List (BitVec 8)) (b : BitVec 8)
    (v10 v28 v29 v30 : Word)
    (hne : pathLen ≠ (0 : Word))
    (halign : listBase.toNat % 8 = 0)
    (hi : pathOff.toNat < bytes.length)
    (hb : bytes[pathOff.toNat]'hi = b)
    (hover : listBase.toNat + pathOff.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 pathOff.toNat) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 10 (pc 32) (pc 48) fullCode
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        bytesRegion listBase bytes ** F)
      (fun h => ∃ x28v x30v : Word,
        ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 (hpKind b))) **
          (.x28 ↦ᵣ x28v) **
          (.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) **
          (.x30 ↦ᵣ x30v) **
          bytesRegion listBase bytes ** F) h) := by
  have h0 := hp_nempty_entry pathOff pathLen hne
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      bytesRegion listBase bytes ** F)
    (by pcf; try exact hF; try exact bytesRegion_pcFree _ _)
  have h1 := hp_nibble_prep listBase pathOff bytes b v28 v29 v30
    halign hi hb hover hvalid
    ((.x7 ↦ᵣ pathLen) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF)
  have h2 := hp_classify_nibble b v10
    ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + pathOff)) **
      bytesRegion listBase bytes ** F)
    (by pcf; try exact hF; try exact bytesRegion_pcFree _ _)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h0 h1
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01 h2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      obtain ⟨x30v, hq'⟩ := hq
      exact ⟨listBase + pathOff, x30v, by xperm_chunked hq'⟩) c012

/-- Empty path fail from pc32. -/
theorem hp_empty_to_kind3
    (listBase pathOff : Word) (v10 v28 v29 v30 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 32) (pc 48) fullCode
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** F)
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (3 : Word)) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** F) := by
  have h := hp_empty_fail pathOff v10
    ((.x8 ↦ᵣ listBase) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** F)
    (by pcf; try exact hF)
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) h

/-- HP path from after load: empty→3 or nempty→hpKind. Fuel 10. -/
def hpAfterLoadPost (listBase pathOff pathLen : Word)
    (bytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  fun h => ∃ kind : Nat, ∃ x28v x29v x30v : Word,
    (((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (BitVec.ofNat 64 kind)) **
      (.x28 ↦ᵣ x28v) ** (.x29 ↦ᵣ x29v) ** (.x30 ↦ᵣ x30v) **
      bytesRegion listBase bytes ** F) **
    ⌜(pathLen = (0 : Word) ∧ kind = 3) ∨
      (pathLen ≠ (0 : Word) ∧ ∃ b, bytes[pathOff.toNat]? = some b ∧
        kind = hpKind b)⌝) h

theorem hp_after_load
    (listBase pathOff pathLen : Word) (bytes : List (BitVec 8))
    (v10 v28 v29 v30 : Word)
    (halign : listBase.toNat % 8 = 0)
    (hover_base : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid_all : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hb_opt : pathLen = (0 : Word) ∨
      (pathLen ≠ (0 : Word) ∧ ∃ b, bytes[pathOff.toNat]? = some b))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 10 (pc 32) (pc 48) fullCode
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        bytesRegion listBase bytes ** F)
      (hpAfterLoadPost listBase pathOff pathLen bytes F) := by
  cases hb_opt with
  | inl hz =>
    subst hz
    have h := hp_empty_to_kind3 listBase pathOff v10 v28 v29 v30
      (bytesRegion listBase bytes ** F)
      (by pcf; try exact hF; try exact bytesRegion_pcFree _ _)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => ?_) h)
    refine ⟨3, v28, v29, v30, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
    simp only [kindW_three]
    xperm_chunked hq
  | inr hne_ex =>
    obtain ⟨hne, b, hbopt⟩ := hne_ex
    have hi : pathOff.toNat < bytes.length :=
      (List.getElem?_eq_some_iff.mp hbopt).1
    have hb : bytes[pathOff.toNat]'hi = b :=
      Option.some.inj (List.getElem?_eq_getElem hi ▸ hbopt)
    have hover : listBase.toNat + pathOff.toNat < 2 ^ 64 := by omega
    have hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 pathOff.toNat) = true :=
      hvalid_all _ hi
    have h := hp_nempty_classify listBase pathOff pathLen bytes b v10 v28 v29 v30
      hne halign hi hb hover hvalid F hF
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h
    obtain ⟨x28v, x30v, hq'⟩ := hq
    refine ⟨hpKind b, x28v, (b.zeroExtend 64) >>> 4, x30v, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, Or.inr ⟨hne, b, hbopt, rfl⟩⟩
    xperm_chunked hq'

/-! ## Nth post-call peel + HP outcome -/

/-- Peel nth `callReturnResult` into a concrete status/offset/len arm. -/
theorem cpsTripleWithin_nthReturn_pre
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (nSaved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (h : ∀ status offset len v11 v12,
        RlpListNthItemSAsm.Result bytes listBase listLen 0 oldOffset oldLen
          status offset len →
        cpsTripleWithin N (pc 25) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
              RlpListNthItemSAsm.savedRegTail nSaved) **
             ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q) :
    cpsTripleWithin N (pc 25) ret fullCode
      (((.x1 ↦ᵣ X) **
        RlpListNthItemSAsm.callReturnResult sp0 listBase (0 : Word)
          offsetPtr lenPtr oldOffset oldLen nSaved bytes listLen 0) ** F) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, s1, s2, hd12, hu12, hP, hRs⟩ := hPR
  obtain ⟨t1, t2, hdt, hut, hXcRR, hFt⟩ := hP
  obtain ⟨u1, u2, hdu, huu, hX, hcRR⟩ := hXcRR
  unfold RlpListNthItemSAsm.callReturnResult at hcRR
  obtain ⟨status, offset, len, v11, v12, hBig⟩ := hcRR
  have hspl := (sepConj_pure_right u2).1 hBig
  exact h status offset len v11 v12 hspl.2 R hR s hcr
    ⟨hp, hcompat, s1, s2, hd12, hu12,
      ⟨t1, t2, hdt, hut, ⟨u1, u2, hdu, huu, hX, hspl.1⟩, hFt⟩, hRs⟩ hpc

/-- Nth fail (status=1) → kind 3 at epi. Fuel 2. -/
theorem nth_fail_to_kind3
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 25) (pc 48) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (3 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) :=
  nth_fail_arm F hF

/-- Re-export Body.of_forall3 for local peels (right-assoc trailing owns). -/
private theorem of_forall3
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 : Reg}
    {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, ⟨v3, hv3⟩⟩ := hO2
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, ⟨g2, g3, d2, u2, hv1, ⟨g4, g5, d3, u3, hv2, hv3⟩⟩⟩, hRb⟩ hpc

/-! HP after-load with x28/x29/x30 as owns (peel via of_forall3). -/
set_option maxRecDepth 8000 in
theorem hp_after_load_owns
    (listBase pathOff pathLen : Word) (bytes : List (BitVec 8))
    (v10 : Word)
    (halign : listBase.toNat % 8 = 0)
    (hover_base : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid_all : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hb_opt : pathLen = (0 : Word) ∨
      (pathLen ≠ (0 : Word) ∧ ∃ b, bytes[pathOff.toNat]? = some b))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 10 (pc 32) (pc 48) fullCode
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion listBase bytes ** F)
      (hpAfterLoadPost listBase pathOff pathLen bytes F) := by
  -- Reassoc so owns are trailing for of_forall3
  let P : Assertion :=
    (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
      bytesRegion listBase bytes ** F
  have hpeel : cpsTripleWithin 10 (pc 32) (pc 48) fullCode
      (P ** regOwn .x28 ** regOwn .x29 ** regOwn .x30)
      (hpAfterLoadPost listBase pathOff pathLen bytes F) := by
    refine of_forall3 (r1 := .x28) (r2 := .x29) (r3 := .x30) (fun v28 v29 v30 => ?_)
    have h := hp_after_load listBase pathOff pathLen bytes v10 v28 v29 v30
      halign hover_base hvalid_all hb_opt F hF
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [P] at hp ⊢; xperm_chunked hp)
      (fun _ hq => hq) h
  exact cpsTripleWithin_weaken
    (fun _ hp => by simp only [P] at hp ⊢; xperm_chunked hp)
    (fun _ hq => hq) hpeel

/-- Extra ambient in hpAfterLoadPost's F (not in its core). -/
def nthOkHpFrame (v11 v12 : Word) (pathOff pathLen : Word) (F : Assertion) : Assertion :=
  (.x5 ↦ᵣ MnkPathLen) **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** regOwn .x31 **
  (MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen) ** F

theorem nthOkHpFrame_pcFree (v11 v12 : Word) (pathOff pathLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    (nthOkHpFrame v11 v12 pathOff pathLen F).pcFree := by
  unfold nthOkHpFrame
  repeat' first
    | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | apply pcFree_sepConj

/-! Nth ok → HP load → classify. Fuel 1+6+10 = 17.
    Post = hpAfterLoadPost with frame ambient (x5/path cells/temps). -/
theorem nth_ok_to_hp
    (listBase pathOff pathLen : Word) (bytes : List (BitVec 8))
    (v11 v12 : Word)
    (halign : listBase.toNat % 8 = 0)
    (hover_base : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid_all : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hb_opt : pathLen = (0 : Word) ∨
      (pathLen ≠ (0 : Word) ∧ ∃ b : BitVec 8, bytes[pathOff.toNat]? = some b))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 17 (pc 25) (pc 48) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ listBase) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion listBase bytes **
        (MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen) ** F)
      (hpAfterLoadPost listBase pathOff pathLen bytes
        (nthOkHpFrame v11 v12 pathOff pathLen F)) := by
  have hnt := nth_ok_entry
    ((.x8 ↦ᵣ listBase) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes **
      (MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen) ** F)
    (by pcf; try exact hF; try exact bytesRegion_pcFree _ _)
  have hload := hp_load_block pathOff pathLen
  have hloadF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x8 ↦ᵣ listBase) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes ** F)
    (by pcf; try exact hF; try exact bytesRegion_pcFree _ _) hload
  have hafter := hp_after_load_owns listBase pathOff pathLen bytes (0 : Word)
    halign hover_base hvalid_all hb_opt
    (nthOkHpFrame v11 v12 pathOff pathLen F)
    (nthOkHpFrame_pcFree v11 v12 pathOff pathLen F hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hnt hloadF
  -- Bridge load-post → hafter-pre: unfold frame so path cells/x5 are visible atoms.
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [nthOkHpFrame] at hp ⊢; xperm_chunked hp)
    c01 hafter
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => hq) c012)

/-! ## Nth outcome → bodyPost (kind + MptNodeKindResult) -/

/-- Buffer coherence: a successful nth path item is empty or has a first byte.
    Dischargeable from `Success` + slack (pure lemma deferred). -/
def PathByteOk (bytes : List (BitVec 8)) (listBase : Word) (listLen : Nat)
    (oldOff oldLen : Word) : Prop :=
  ∀ off len,
    RlpListNthItemSAsm.Result bytes listBase listLen 0 oldOff oldLen
      (0 : Word) off len →
    len = (0 : Word) ∨
      (len ≠ (0 : Word) ∧ ∃ b : BitVec 8, bytes[off.toNat]? = some b)

/-- Caller ambient around nth return (frame + count + stack; no path cells).
    `x1` still holds the nth-return PC; converted to own at bodyPost. -/
def nthCallerAmb (newSp : Word) (ks : KindSaved) (countW : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) ** kindSavedFrame newSp ks **
  (.x1 ↦ᵣ (pc 25)) **
  regOwn .x8 ** regOwn .x9 **
  regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
  (MnkCount ↦ₘ countW) ** stackFree newSp 8

theorem nthCallerAmb_pcFree (newSp : Word) (ks : KindSaved) (countW : Word) :
    (nthCallerAmb newSp ks countW).pcFree := by
  unfold nthCallerAmb kindSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _ | apply pcFree_sepConj

/-- Peeled nth-return ambient (matches `cpsTripleWithin_nthReturn_pre` arm pre). -/
def nthPeelAmb (newSp : Word) (nSaved : RlpListNthItemSAsm.Saved)
    (ks : KindSaved) (status offset len v11 v12 countW : Word)
    (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  ((.x1 ↦ᵣ (pc 25)) **
    (((.x2 ↦ᵣ newSp) ** stackFree newSp 8 **
      RlpListNthItemSAsm.savedRegTail nSaved) **
     ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
      (MnkPathOff ↦ₘ offset) ** (MnkPathLen ↦ₘ len)))) **
  kindSavedFrame newSp ks ** (MnkCount ↦ₘ countW)

/-! Drop savedRegTail to owns, keep x1 concrete; result matches nth_fail_to_kind3 frame. -/
private theorem nthPeel_drop_saved_fail
    (newSp : Word) (nSaved : RlpListNthItemSAsm.Saved) (ks : KindSaved)
    (v11 v12 countW oldOff oldLen : Word)
    (listBase : Word) (bytes : List (BitVec 8)) (h : PartialState)
    (hp : (nthPeelAmb newSp nSaved ks (1 : Word) oldOff oldLen v11 v12 countW
      listBase bytes) h) :
    ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes **
      (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
      nthCallerAmb newSp ks countW) h := by
  simp only [nthPeelAmb, RlpListNthItemSAsm.savedRegTail, kindSavedFrame,
    nthCallerAmb] at hp ⊢
  have hx :
      ((.x8 ↦ᵣ nSaved.s0) ** (.x9 ↦ᵣ nSaved.s1) **
        (.x18 ↦ᵣ nSaved.s2) ** (.x19 ↦ᵣ nSaved.s3) **
        (.x20 ↦ᵣ nSaved.s4) ** (.x21 ↦ᵣ nSaved.s5) **
        ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes **
          (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
          (.x2 ↦ᵣ newSp) **
          ((newSp ↦ₘ ks.ra) ** ((newSp + 8) ↦ₘ ks.s0) ** ((newSp + 16) ↦ₘ ks.s1)) **
          (.x1 ↦ᵣ (pc 25)) **
          (MnkCount ↦ₘ countW) ** stackFree newSp 8)) h := by
    xperm_chunked hp
  have d1 := sepConj_mono (regIs_implies_regOwn (v := nSaved.s0) .x8)
    (fun _ x => x) h hx
  have d2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := nSaved.s1) .x9) (fun _ x => x)) h d1
  have d3 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := nSaved.s2) .x18) (fun _ x => x))) h d2
  have d4 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := nSaved.s3) .x19) (fun _ x => x)))) h d3
  have d5 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := nSaved.s4) .x20) (fun _ x => x))))) h d4
  have d6 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn (v := nSaved.s5) .x21)
          (fun _ x => x)))))) h d5
  xperm_chunked d6

/-! Nth fail peel ambient → bodyPost kind 3 + `.nthFail`. Fuel 2. -/
set_option maxRecDepth 8000 in
theorem nth_fail_outcome
    (newSp : Word) (ks : KindSaved)
    (nSaved : RlpListNthItemSAsm.Saved)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen countW : Word)
    (v11 v12 : Word)
    (hc : RlpListCountItemsSAsm.Result bytes listBase listLen (0 : Word)
      (BitVec.ofNat 64 2))
    (hn : RlpListNthItemSAsm.Result bytes listBase listLen 0 oldOff oldLen
      (1 : Word) oldOff oldLen) :
    cpsTripleWithin 2 (pc 25) (pc 48) fullCode
      (nthPeelAmb newSp nSaved ks (1 : Word) oldOff oldLen v11 v12 countW
        listBase bytes)
      (bodyPost newSp ks 3 listBase bytes listLen oldCount oldOff oldLen
        countW oldOff oldLen) := by
  have hfail := nth_fail_to_kind3
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes **
      (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
      nthCallerAmb newSp ks countW)
    (by pcf)
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := nthPeel_drop_saved_fail newSp nSaved ks v11 v12 countW
        oldOff oldLen listBase bytes h hp
      xperm_chunked hp')
    (fun h hq => ?post) hfail
  simp only [nthCallerAmb, kindSavedFrame] at hq
  have hx :
      ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x1 ↦ᵣ (pc 25)) **
        ((.x10 ↦ᵣ (3 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes **
          (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
          (.x2 ↦ᵣ newSp) **
          ((newSp ↦ₘ ks.ra) ** ((newSp + 8) ↦ₘ ks.s0) ** ((newSp + 16) ↦ₘ ks.s1)) **
          regOwn .x8 ** regOwn .x9 **
          regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
          (MnkCount ↦ₘ countW) ** stackFree newSp 8)) h := by
    xperm_chunked hq
  have hx1 := sepConj_mono (regIs_implies_regOwn (v := v11) .x11) (fun _ x => x) h hx
  have hx2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := v12) .x12) (fun _ x => x)) h hx1
  have hx3 := sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := pc 25) .x1) (fun _ x => x))) h hx2
  unfold bodyPost
  refine (sepConj_pure_right _).2 ⟨?_, .nthFail hc hn⟩
  simp only [bodyExitAmb, kindSavedFrame, regsOwnAt_kindFrame, kindW_three] at hx3 ⊢
  xperm_chunked hx3

/-- Ambient for nth-ok path after dropping non-x8 saved regs. -/
def nthOkCallerF (newSp : Word) (ks : KindSaved) (countW : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) ** kindSavedFrame newSp ks **
  (.x1 ↦ᵣ (pc 25)) **
  regOwn .x9 **
  regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
  (MnkCount ↦ₘ countW) ** stackFree newSp 8

theorem nthOkCallerF_pcFree (newSp : Word) (ks : KindSaved) (countW : Word) :
    (nthOkCallerF newSp ks countW).pcFree := by
  unfold nthOkCallerF kindSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _ | apply pcFree_sepConj

/-! Drop peel ambient (with s0=listBase) into nth_ok_to_hp pre. -/
private theorem nthPeel_drop_saved_ok
    (newSp : Word) (nSaved : RlpListNthItemSAsm.Saved) (ks : KindSaved)
    (v11 v12 countW pathOff pathLen : Word)
    (listBase : Word) (bytes : List (BitVec 8))
    (hs0 : nSaved.s0 = listBase) (h : PartialState)
    (hp : (nthPeelAmb newSp nSaved ks (0 : Word) pathOff pathLen v11 v12 countW
      listBase bytes) h) :
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x8 ↦ᵣ listBase) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes **
      (MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen) **
      nthOkCallerF newSp ks countW) h := by
  simp only [nthPeelAmb, RlpListNthItemSAsm.savedRegTail, kindSavedFrame,
    nthOkCallerF, hs0] at hp ⊢
  have hx :
      ((.x9 ↦ᵣ nSaved.s1) **
        (.x18 ↦ᵣ nSaved.s2) ** (.x19 ↦ᵣ nSaved.s3) **
        (.x20 ↦ᵣ nSaved.s4) ** (.x21 ↦ᵣ nSaved.s5) **
        ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ listBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes **
          (MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen) **
          (.x2 ↦ᵣ newSp) **
          ((newSp ↦ₘ ks.ra) ** ((newSp + 8) ↦ₘ ks.s0) ** ((newSp + 16) ↦ₘ ks.s1)) **
          (.x1 ↦ᵣ (pc 25)) **
          (MnkCount ↦ₘ countW) ** stackFree newSp 8)) h := by
    xperm_chunked hp
  have d1 := sepConj_mono (regIs_implies_regOwn (v := nSaved.s1) .x9)
    (fun _ x => x) h hx
  have d2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := nSaved.s2) .x18) (fun _ x => x)) h d1
  have d3 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := nSaved.s3) .x19) (fun _ x => x))) h d2
  have d4 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := nSaved.s4) .x20) (fun _ x => x)))) h d3
  have d5 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := nSaved.s5) .x21) (fun _ x => x))))) h d4
  xperm_chunked d5

/-! Nth ok peel ambient → HP → bodyPost + `.emptyPath` / `.path`. Fuel 17. -/
set_option maxRecDepth 8000 in
theorem nth_ok_outcome
    (newSp : Word) (ks : KindSaved)
    (nSaved : RlpListNthItemSAsm.Saved)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen countW : Word)
    (pathOff pathLen : Word) (v11 v12 : Word)
    (halign : listBase.toNat % 8 = 0)
    (hover_base : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid_all : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hc : RlpListCountItemsSAsm.Result bytes listBase listLen (0 : Word)
      (BitVec.ofNat 64 2))
    (hs0 : nSaved.s0 = listBase)
    (hn : RlpListNthItemSAsm.Result bytes listBase listLen 0 oldOff oldLen
      (0 : Word) pathOff pathLen)
    (hb_opt : pathLen = (0 : Word) ∨
      (pathLen ≠ (0 : Word) ∧ ∃ b : BitVec 8, bytes[pathOff.toNat]? = some b)) :
    cpsTripleWithin 17 (pc 25) (pc 48) fullCode
      (nthPeelAmb newSp nSaved ks (0 : Word) pathOff pathLen v11 v12 countW
        listBase bytes)
      (fun h => ∃ kind : Nat,
        (bodyPost newSp ks kind listBase bytes listLen oldCount oldOff oldLen
          countW pathOff pathLen) h) := by
  have hhp := nth_ok_to_hp listBase pathOff pathLen bytes v11 v12
    halign hover_base hvalid_all hb_opt
    (nthOkCallerF newSp ks countW)
    (nthOkCallerF_pcFree newSp ks countW)
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := nthPeel_drop_saved_ok newSp nSaved ks v11 v12 countW
        pathOff pathLen listBase bytes hs0 h hp
      xperm_chunked hp')
    (fun h hq => ?post) hhp
  obtain ⟨kind, x28v, x29v, x30v, hbig⟩ := hq
  have hspl := (sepConj_pure_right _).1 hbig
  obtain ⟨hamb, hpure⟩ := hspl
  simp only [nthOkHpFrame, nthOkCallerF, kindSavedFrame] at hamb
  have hx :
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) **
        (.x5 ↦ᵣ MnkPathLen) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x1 ↦ᵣ (pc 25)) ** (.x28 ↦ᵣ x28v) ** (.x29 ↦ᵣ x29v) ** (.x30 ↦ᵣ x30v) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (BitVec.ofNat 64 kind)) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x31 **
          bytesRegion listBase bytes **
          (MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen) **
          (.x2 ↦ᵣ newSp) **
          ((newSp ↦ₘ ks.ra) ** ((newSp + 8) ↦ₘ ks.s0) ** ((newSp + 16) ↦ₘ ks.s1)) **
          regOwn .x9 **
          regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
          (MnkCount ↦ₘ countW) ** stackFree newSp 8)) h := by
    xperm_chunked hamb
  have d1 := sepConj_mono (regIs_implies_regOwn (v := listBase) .x8) (fun _ x => x) h hx
  have d2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := pathOff) .x6) (fun _ x => x)) h d1
  have d3 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := pathLen) .x7) (fun _ x => x))) h d2
  have d4 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := MnkPathLen) .x5) (fun _ x => x)))) h d3
  have d5 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := v11) .x11) (fun _ x => x))))) h d4
  have d6 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn (v := v12) .x12) (fun _ x => x)))))) h d5
  have d7 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn (v := pc 25) .x1) (fun _ x => x))))))) h d6
  have d8 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn (v := x28v) .x28) (fun _ x => x)))))))) h d7
  have d9 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn (v := x29v) .x29) (fun _ x => x))))))))) h d8
  have d10 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn (v := x30v) .x30)
              (fun _ x => x)))))))))) h d9
  refine ⟨kind, ?_⟩
  unfold bodyPost
  refine (sepConj_pure_right _).2 ⟨?_, ?_⟩
  · simp only [bodyExitAmb, kindSavedFrame, regsOwnAt_kindFrame] at d10 ⊢
    xperm_chunked d10
  · cases hpure with
    | inl hz =>
      obtain ⟨hlen0, hkind3⟩ := hz
      subst hlen0 hkind3
      exact .emptyPath pathOff hc (by convert hn)
    | inr hne_ex =>
      obtain ⟨hne, b, hb, hk⟩ := hne_ex
      have hlen_pos : 0 < pathLen.toNat := by
        have : pathLen.toNat ≠ 0 := by
          intro h0
          apply hne
          exact BitVec.eq_of_toNat_eq (by simp [h0])
        omega
      exact .path pathOff pathLen b kind hc hn hlen_pos hb hk

/-! ## Nth callReturn peel → bodyPost (fail | ok+HP) -/

/-- Body-post existential over kind and final path BSS cells. -/
def bodyPostEx (newSp : Word) (ks : KindSaved)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen countW : Word) : Assertion :=
  fun h => ∃ (kind : Nat) (offW lenW : Word),
    (bodyPost newSp ks kind listBase bytes listLen oldCount oldOff oldLen
      countW offW lenW) h

/-- Like `bodyPostEx`, but also hides the final count BSS word (count arms differ). -/
def bodyPostExAny (newSp : Word) (ks : KindSaved)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen : Word) : Assertion :=
  fun h => ∃ (kind : Nat) (countW offW lenW : Word),
    (bodyPost newSp ks kind listBase bytes listLen oldCount oldOff oldLen
      countW offW lenW) h

/-! Nth return (any Result) → bodyPost. Fuel 17.
    Requires `nSaved.s0 = listBase` so ok-path keeps x8 as listBase. -/
set_option maxRecDepth 8000 in
theorem nth_outcome
    (newSp : Word) (ks : KindSaved)
    (nSaved : RlpListNthItemSAsm.Saved)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen countW : Word)
    (halign : listBase.toNat % 8 = 0)
    (hover_base : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid_all : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hc : RlpListCountItemsSAsm.Result bytes listBase listLen (0 : Word)
      (BitVec.ofNat 64 2))
    (hs0 : nSaved.s0 = listBase)
    (hpath : PathByteOk bytes listBase listLen oldOff oldLen) :
    cpsTripleWithin 17 (pc 25) (pc 48) fullCode
      (((.x1 ↦ᵣ (pc 25)) **
        RlpListNthItemSAsm.callReturnResult newSp listBase (0 : Word)
          MnkPathOff MnkPathLen oldOff oldLen
          { nSaved with ra := pc 25 } bytes listLen 0) **
        kindSavedFrame newSp ks ** (MnkCount ↦ₘ countW))
      (bodyPostEx newSp ks listBase bytes listLen oldCount oldOff oldLen countW) := by
  refine cpsTripleWithin_nthReturn_pre (N := 17) (ret := pc 48) (X := pc 25)
    (F := kindSavedFrame newSp ks ** (MnkCount ↦ₘ countW))
    newSp listBase MnkPathOff MnkPathLen oldOff oldLen
    { nSaved with ra := pc 25 } bytes listLen
    (fun status offset len v11 v12 hres => by
      cases hres with
      | fail hf =>
        have hfail := nth_fail_outcome newSp ks { nSaved with ra := pc 25 }
          listBase bytes listLen oldCount oldOff oldLen countW v11 v12
          hc (.fail hf)
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken
            (fun h hp => by
              simp only [nthPeelAmb, RlpListNthItemSAsm.savedRegTail] at hp ⊢
              xperm_chunked hp)
            (fun _ hq => ⟨3, oldOff, oldLen, hq⟩) hfail)
      | ok _ _ hSucc =>
        have hn : RlpListNthItemSAsm.Result bytes listBase listLen 0 oldOff oldLen
            (0 : Word) offset len := .ok offset len hSucc
        have hb := hpath offset len hn
        have hok := nth_ok_outcome newSp ks { nSaved with ra := pc 25 }
          listBase bytes listLen oldCount oldOff oldLen countW offset len v11 v12
          halign hover_base hvalid_all hc hs0 hn hb
        exact cpsTripleWithin_weaken
          (fun h hp => by
            simp only [nthPeelAmb, RlpListNthItemSAsm.savedRegTail] at hp ⊢
            xperm_chunked hp)
          (fun _ hq => by
            obtain ⟨kind, hq'⟩ := hq
            exact ⟨kind, offset, len, hq'⟩) hok)

/-! ## Count callReturn peel → bodyPost (fail | branch | badArity | eq2→nth) -/

/-- Peeled count-return ambient (matches `cpsTripleWithin_countReturn_pre` arm). -/
def countPeelAmb (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved)
    (ks : KindSaved) (status result v11 v12 : Word)
    (oldOff oldLen v13 v14 v20 v21 : Word)
    (listBase : Word) (bytes : List (BitVec 8))
    (R : Assertion) : Assertion :=
  ((.x1 ↦ᵣ (pc 9)) **
    (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
      RlpListCountItemsSAsm.savedRegTail cSaved) **
     ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase bytes ** (MnkCount ↦ₘ result)))) **
  countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R

/-! Drop count savedRegTail + concrete temps to owns; recombine
    `R ** stackFree 6` → `stackFree 8` via the split equality. -/
private theorem countPeel_drop_to_exit
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (kindW result v11 v12 : Word)
    (oldOff oldLen v13 v14 v20 v21 : Word)
    (listBase : Word) (bytes : List (BitVec 8))
    (R : Assertion)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (h : PartialState)
    (hp : (((.x1 ↦ᵣ (pc 9)) **
        (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
          RlpListCountItemsSAsm.savedRegTail cSaved) **
         ((.x10 ↦ᵣ kindW) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase bytes ** (MnkCount ↦ₘ result)))) **
      countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R) h) :
    (bodyExitAmb newSp ks kindW listBase bytes result oldOff oldLen) h := by
  simp only [countCallF, kindSavedFrame, RlpListCountItemsSAsm.savedRegTail] at hp
  have hx :
      ((.x8 ↦ᵣ cSaved.s0) ** (.x9 ↦ᵣ cSaved.s1) **
        (.x18 ↦ᵣ cSaved.s2) ** (.x19 ↦ᵣ cSaved.s3) **
        (.x1 ↦ᵣ (pc 9)) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        ((.x10 ↦ᵣ kindW) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes **
          (MnkCount ↦ₘ result) ** (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
          (.x2 ↦ᵣ newSp) **
          ((newSp ↦ₘ ks.ra) ** ((newSp + 8) ↦ₘ ks.s0) ** ((newSp + 16) ↦ₘ ks.s1)) **
          (R ** stackFree newSp 6))) h := by
    xperm_chunked hp
  have d1 := sepConj_mono (regIs_implies_regOwn (v := cSaved.s0) .x8)
    (fun _ x => x) h hx
  have d2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := cSaved.s1) .x9) (fun _ x => x)) h d1
  have d3 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := cSaved.s2) .x18) (fun _ x => x))) h d2
  have d4 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := cSaved.s3) .x19) (fun _ x => x)))) h d3
  have d5 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn (v := pc 9) .x1) (fun _ x => x))))) h d4
  have d6 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn (v := v11) .x11) (fun _ x => x)))))) h d5
  have d7 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn (v := v12) .x12) (fun _ x => x))))))) h d6
  have d8 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn (v := v13) .x13)
            (fun _ x => x)))))))) h d7
  have d9 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn (v := v14) .x14)
            (fun _ x => x))))))))) h d8
  have d10 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn (v := v20) .x20)
              (fun _ x => x)))))))))) h d9
  have d11 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn (v := v21) .x21)
              (fun _ x => x))))))))))) h d10
  -- Front the residual stack pair so `hR` rewrites it to `stackFree 8`.
  have hx2 :
      (((R ** stackFree newSp 6) **
        ((.x10 ↦ᵣ kindW) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes **
          (MnkCount ↦ₘ result) ** (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
          (.x2 ↦ᵣ newSp) **
          ((newSp ↦ₘ ks.ra) ** ((newSp + 8) ↦ₘ ks.s0) ** ((newSp + 16) ↦ₘ ks.s1)) **
          regOwn .x8 ** regOwn .x9 **
          regOwn .x18 ** regOwn .x19 **
          regOwn .x1 **
          regOwn .x11 ** regOwn .x12 **
          regOwn .x13 ** regOwn .x14 **
          regOwn .x20 ** regOwn .x21))) h := by
    xperm_chunked d11
  rw [← hR] at hx2
  simp only [bodyExitAmb, kindSavedFrame, regsOwnAt_kindFrame] at hx2 ⊢
  xperm_chunked hx2

/-! Count fail (status=1) → bodyPost kind 3 + `.countFail`. Fuel 2. -/
set_option maxRecDepth 8000 in
theorem count_fail_outcome
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen v11 v12 v13 v14 v20 v21 : Word)
    (R : Assertion)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (hRp : R.pcFree)
    (hf : RlpListCountItemsSAsm.Result bytes listBase listLen (1 : Word) (0 : Word)) :
    cpsTripleWithin 2 (pc 9) (pc 48) fullCode
      (countPeelAmb newSp cSaved ks (1 : Word) (0 : Word) v11 v12
        oldOff oldLen v13 v14 v20 v21 listBase bytes R)
      (bodyPost newSp ks 3 listBase bytes listLen oldCount oldOff oldLen
        (0 : Word) oldOff oldLen) := by
  have hfail := count_fail_arm newSp listBase (0 : Word) v11 v12 cSaved bytes
    (countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)
    (countCallF_pcFree newSp ks oldOff oldLen v13 v14 v20 v21 R hRp)
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [countPeelAmb] at hp ⊢
      xperm_chunked hp)
    (fun h hq => ?post) hfail
  unfold bodyPost
  refine (sepConj_pure_right _).2 ⟨?_, .countFail hf⟩
  exact countPeel_drop_to_exit newSp cSaved ks (3 : Word) (0 : Word)
    v11 v12 oldOff oldLen v13 v14 v20 v21 listBase bytes R hR h hq

/-! Count ok + count=17 → bodyPost kind 0 + `.branch`. Fuel 8.
    Result uses `BitVec.ofNat 64 17` (matches `.branch`); machine posts `(17 : Word)`. -/
set_option maxRecDepth 8000 in
theorem count_branch_outcome
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen v11 v12 v13 v14 v20 v21 : Word)
    (R : Assertion)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (hRp : R.pcFree)
    (hb : RlpListCountItemsSAsm.Result bytes listBase listLen (0 : Word)
      (BitVec.ofNat 64 17)) :
    cpsTripleWithin 8 (pc 9) (pc 48) fullCode
      (countPeelAmb newSp cSaved ks (0 : Word) (17 : Word) v11 v12
        oldOff oldLen v13 v14 v20 v21 listBase bytes R)
      (bodyPost newSp ks 0 listBase bytes listLen oldCount oldOff oldLen
        (17 : Word) oldOff oldLen) := by
  let F : Assertion :=
    ((.x1 ↦ᵣ (pc 9)) **
      (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
        RlpListCountItemsSAsm.savedRegTail cSaved) **
       (regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         bytesRegion listBase bytes)) **
      countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)
  have hF : F.pcFree := by
    unfold F countCallF kindSavedFrame RlpListCountItemsSAsm.savedRegTail
    repeat' first
      | exact hRp | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj
  have hbr := count_ok_branch_arm v11 v12 F hF
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [countPeelAmb, F] at hp ⊢
      xperm_chunked hp)
    (fun h hq => ?post) hbr
  simp only [F] at hq
  have hy :
      ((.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ (17 : Word)) ** (.x7 ↦ᵣ (17 : Word)) **
        ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (MnkCount ↦ₘ (17 : Word)) **
          (.x1 ↦ᵣ (pc 9)) **
          (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
            RlpListCountItemsSAsm.savedRegTail cSaved) **
           (regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
             bytesRegion listBase bytes)) **
          countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)) h := by
    xperm_chunked hq
  have d1 := sepConj_mono (regIs_implies_regOwn (v := MnkCount) .x5)
    (fun _ x => x) h hy
  have d2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := (17 : Word)) .x6) (fun _ x => x)) h d1
  have d3 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := (17 : Word)) .x7) (fun _ x => x))) h d2
  have hpeel :
      (((.x1 ↦ᵣ (pc 9)) **
        (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
          RlpListCountItemsSAsm.savedRegTail cSaved) **
         ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase bytes **
          (MnkCount ↦ₘ (17 : Word))))) **
        countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R) h := by
    xperm_chunked d3
  unfold bodyPost
  refine (sepConj_pure_right _).2 ⟨?_, .branch hb⟩
  exact countPeel_drop_to_exit newSp cSaved ks (0 : Word) (17 : Word)
    v11 v12 oldOff oldLen v13 v14 v20 v21 listBase bytes R hR h hpeel

private theorem ofNat64_ne_of_ne (c d : Nat) (hc : c < 2 ^ 64) (hd : d < 2 ^ 64)
    (hne : c ≠ d) : BitVec.ofNat 64 c ≠ BitVec.ofNat 64 d := by
  intro heq
  have := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at this
  exact hne this

/-! Count ok + count≠17≠2 → bodyPost kind 3 + `.badArity`. Fuel 9.
    Path: BNE ntaken + load + BEQ ntaken + li2 + BNE taken → li3. -/
set_option maxRecDepth 8000 in
theorem count_badArity_outcome
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (listBase : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen v11 v12 v13 v14 v20 v21 : Word)
    (c : Nat) (hc64 : c < 2 ^ 64)
    (R : Assertion)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (hRp : R.pcFree)
    (hb : RlpListCountItemsSAsm.Result bytes listBase listLen (0 : Word)
      (BitVec.ofNat 64 c))
    (hne17 : c ≠ 17) (hne2 : c ≠ 2) :
    cpsTripleWithin 9 (pc 9) (pc 48) fullCode
      (countPeelAmb newSp cSaved ks (0 : Word) (BitVec.ofNat 64 c) v11 v12
        oldOff oldLen v13 v14 v20 v21 listBase bytes R)
      (bodyPost newSp ks 3 listBase bytes listLen oldCount oldOff oldLen
        (BitVec.ofNat 64 c) oldOff oldLen) := by
  let countW : Word := BitVec.ofNat 64 c
  have hne17W : countW ≠ (17 : Word) :=
    ofNat64_ne_of_ne c 17 hc64 (by decide) hne17
  have hne2W : countW ≠ (2 : Word) :=
    ofNat64_ne_of_ne c 2 hc64 (by decide) hne2
  let F : Assertion :=
    ((.x1 ↦ᵣ (pc 9)) **
      (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
        RlpListCountItemsSAsm.savedRegTail cSaved) **
       (regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         bytesRegion listBase bytes)) **
      countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)
  have hF : F.pcFree := by
    unfold F countCallF kindSavedFrame RlpListCountItemsSAsm.savedRegTail
    repeat' first
      | exact hRp | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj
  -- BNE status=0 ntaken
  let off9 : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 36)
  have hbne := bne_spec_gen_within .x10 .x0 off9 (0 : Word) (0 : Word) (pc 9)
  rw [bne_fail_off9, bne_nt_off9] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (kindMem (pc 9) 9 (.BNE .x10 .x0 off9)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  -- Avoid `pcf` here: it unfolds transparent `let F` into residual R.
  have hntF := cpsTripleWithin_frameR
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ countW) ** F)
    (by
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | apply pcFree_sepConj) hnt
  -- load count
  have hload := count_load_block countW
  have hloadF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** F)
    (by
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | apply pcFree_sepConj) hload
  -- BEQ ntaken + li 2
  have hne17b := count_ne17_li2 countW hne17W (0 : Word)
    ((.x5 ↦ᵣ MnkCount) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ countW) ** F)
    (by
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | apply pcFree_sepConj)
  -- BNE taken ≠2 → fail
  have hne2b := count_ne2_fail_arm countW hne2W (0 : Word)
    ((.x5 ↦ᵣ MnkCount) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ countW) ** F)
    (by
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | apply pcFree_sepConj)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hntF hloadF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hne17b
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hne2b
  refine cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [countPeelAmb, F] at hp ⊢
      xperm_chunked hp)
    (fun h hq => ?post) c0123
  -- post: drop temps to owns → bodyPost .badArity
  simp only [F] at hq
  have hy :
      ((.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ (2 : Word)) **
        ((.x10 ↦ᵣ (3 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (MnkCount ↦ₘ countW) **
          (.x1 ↦ᵣ (pc 9)) **
          (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
            RlpListCountItemsSAsm.savedRegTail cSaved) **
           (regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
             bytesRegion listBase bytes)) **
          countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)) h := by
    xperm_chunked hq
  have d1 := sepConj_mono (regIs_implies_regOwn (v := MnkCount) .x5)
    (fun _ x => x) h hy
  have d2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := countW) .x6) (fun _ x => x)) h d1
  have d3 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := (2 : Word)) .x7) (fun _ x => x))) h d2
  have hpeel :
      (((.x1 ↦ᵣ (pc 9)) **
        (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
          RlpListCountItemsSAsm.savedRegTail cSaved) **
         ((.x10 ↦ᵣ (3 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase bytes **
          (MnkCount ↦ₘ countW)))) **
        countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R) h := by
    xperm_chunked d3
  unfold bodyPost
  refine (sepConj_pure_right _).2 ⟨?_, .badArity c hc64 hb hne17 hne2⟩
  exact countPeel_drop_to_exit newSp cSaved ks (3 : Word) countW
    v11 v12 oldOff oldLen v13 v14 v20 v21 listBase bytes R hR h hpeel

/-! Count ok + count=2 → reach nth entry at pc17 (status load + ne17 + eq2).
    Fuel: 1+4+2+1 = 8. Leaves x6=x7=2, x5=MnkCount, MnkCount↦2. -/
set_option maxRecDepth 8000 in
theorem count_eq2_to_nth_entry
    (v11 v12 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 9) (pc 17) fullCode
      (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (2 : Word))) ** F)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (2 : Word)) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (2 : Word))) ** F) := by
  let off9 : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 36)
  have hbne := bne_spec_gen_within .x10 .x0 off9 (0 : Word) (0 : Word) (pc 9)
  rw [bne_fail_off9, bne_nt_off9] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (kindMem (pc 9) 9 (.BNE .x10 .x0 off9)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have hntF := cpsTripleWithin_frameR
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (2 : Word)) ** F)
    (by
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | apply pcFree_sepConj) hnt
  have hload := count_load_block (2 : Word)
  have hloadF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** F)
    (by
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | apply pcFree_sepConj) hload
  have hne17b := count_ne17_li2 (2 : Word) (by decide) (0 : Word)
    ((.x5 ↦ᵣ MnkCount) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (2 : Word)) ** F)
    (by
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | apply pcFree_sepConj)
  have heq2 := count_eq2_nth_entry (0 : Word)
    ((.x5 ↦ᵣ MnkCount) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (2 : Word)) ** F)
    (by
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | apply pcFree_sepConj)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hntF hloadF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hne17b
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 heq2
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c0123

/-- Fuel for count=2 path through nth call + outcome.
    8 (eq2 entry) + 7 (nth setup) + nth_call + 17 (nth_outcome). -/
def countEq2Fuel (_listLen : Nat) : Nat :=
  8 + 7 + (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9)) + 17

/-- eq2-entry frame (matches `count_eq2_to_nth_entry` F). -/
def countEq2F (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved)
    (ks : KindSaved) (oldOff oldLen v13 v14 v20 v21 : Word)
    (listBase : Word) (bytes : List (BitVec 8)) (R : Assertion) : Assertion :=
  ((.x1 ↦ᵣ (pc 9)) **
    (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
      RlpListCountItemsSAsm.savedRegTail cSaved) **
     (regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       bytesRegion listBase bytes)) **
    countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)

theorem countEq2F_pcFree (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved)
    (ks : KindSaved) (oldOff oldLen v13 v14 v20 v21 : Word)
    (listBase : Word) (bytes : List (BitVec 8)) (R : Assertion)
    (hRp : R.pcFree) :
    (countEq2F newSp cSaved ks oldOff oldLen v13 v14 v20 v21 listBase bytes R).pcFree := by
  unfold countEq2F countCallF kindSavedFrame RlpListCountItemsSAsm.savedRegTail
  repeat' first
    | exact hRp | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-- Reshape peel ambient → eq2-entry pre. -/
private theorem countPeel_to_eq2_pre
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (v11 v12 v13 v14 v20 v21 oldOff oldLen : Word)
    (listBase : Word) (bytes : List (BitVec 8)) (R : Assertion)
    (h : PartialState)
    (hp : (countPeelAmb newSp cSaved ks (0 : Word) (2 : Word) v11 v12
        oldOff oldLen v13 v14 v20 v21 listBase bytes R) h) :
    (((( .x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (2 : Word))) **
      countEq2F newSp cSaved ks oldOff oldLen v13 v14 v20 v21 listBase bytes R) h) := by
  simp only [countPeelAmb, countEq2F] at hp ⊢
  xperm_chunked hp

/-! Count peel + eq2 entry → pc17 with count loaded and x6=x7=2. -/
set_option maxRecDepth 8000 in
theorem count_eq2_reach_nth
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (listBase : Word) (bytes : List (BitVec 8))
    (oldOff oldLen v11 v12 v13 v14 v20 v21 : Word)
    (R : Assertion) (hRp : R.pcFree) :
    cpsTripleWithin 8 (pc 9) (pc 17) fullCode
      (countPeelAmb newSp cSaved ks (0 : Word) (2 : Word) v11 v12
        oldOff oldLen v13 v14 v20 v21 listBase bytes R)
      (((( .x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (2 : Word)) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (2 : Word))) **
        countEq2F newSp cSaved ks oldOff oldLen v13 v14 v20 v21 listBase bytes R)) := by
  have heq := count_eq2_to_nth_entry v11 v12
    (countEq2F newSp cSaved ks oldOff oldLen v13 v14 v20 v21 listBase bytes R)
    (countEq2F_pcFree newSp cSaved ks oldOff oldLen v13 v14 v20 v21 listBase bytes R hRp)
  exact cpsTripleWithin_weaken
    (fun h hp => countPeel_to_eq2_pre newSp cSaved ks v11 v12 v13 v14 v20 v21
      oldOff oldLen listBase bytes R h hp)
    (fun _ hq => hq) heq

/-- nth_setup frame after eq2: stack residual form, s0/s1 rewritten to list ABI. -/
def countEq2SetupF (newSp : Word) (ks : KindSaved)
    (listBase : Word) (_listLenW v18 v19 v20 v21 : Word)
    (bytes : List (BitVec 8)) (oldOff oldLen : Word) (R : Assertion) : Assertion :=
  ((.x1 ↦ᵣ (pc 9)) ** (.x2 ↦ᵣ newSp) ** (R ** stackFree newSp 6) **
    (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
    (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (2 : Word)) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    bytesRegion listBase bytes **
    (MnkCount ↦ₘ (2 : Word)) **
    (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
    kindSavedFrame newSp ks)

theorem countEq2SetupF_pcFree (newSp : Word) (ks : KindSaved)
    (listBase _listLenW v18 v19 v20 v21 : Word)
    (bytes : List (BitVec 8)) (oldOff oldLen : Word) (R : Assertion)
    (hRp : R.pcFree) :
    (countEq2SetupF newSp ks listBase _listLenW v18 v19 v20 v21
      bytes oldOff oldLen R).pcFree := by
  unfold countEq2SetupF kindSavedFrame
  repeat' first
    | exact hRp | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-- Reshape eq2 post → nth_setup pre (needs s0=listBase, s1=listLenW). -/
private theorem countEq2_post_to_setup_pre
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (listBase listLenW : Word) (bytes : List (BitVec 8))
    (oldOff oldLen v11 v12 v13 v14 v20 v21 : Word)
    (R : Assertion)
    (hs0 : cSaved.s0 = listBase) (hs1 : cSaved.s1 = listLenW)
    (h : PartialState)
    (hp : (((( .x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (2 : Word)) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (2 : Word))) **
        countEq2F newSp cSaved ks oldOff oldLen v13 v14 v20 v21 listBase bytes R) h)) :
    (((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
      countEq2SetupF newSp ks listBase listLenW cSaved.s2 cSaved.s3 v20 v21
        bytes oldOff oldLen R) h) := by
  simp only [countEq2F, countCallF, RlpListCountItemsSAsm.savedRegTail,
    countEq2SetupF, kindSavedFrame, hs0, hs1] at hp ⊢
  xperm_chunked hp

/-! peel → pc24 after nth_setup (ABI args ready for nth call). -/
set_option maxRecDepth 8000 in
theorem count_eq2_nth_setup
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (listBase listLenW : Word) (bytes : List (BitVec 8))
    (oldOff oldLen v11 v12 v13 v14 v20 v21 : Word)
    (R : Assertion) (hRp : R.pcFree)
    (hs0 : cSaved.s0 = listBase) (hs1 : cSaved.s1 = listLenW) :
    cpsTripleWithin (8 + 7) (pc 9) (pc 24) fullCode
      (countPeelAmb newSp cSaved ks (0 : Word) (2 : Word) v11 v12
        oldOff oldLen v13 v14 v20 v21 listBase bytes R)
      (((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ MnkPathOff) ** (.x14 ↦ᵣ MnkPathLen) **
        countEq2SetupF newSp ks listBase listLenW cSaved.s2 cSaved.s3 v20 v21
          bytes oldOff oldLen R)) := by
  have hreach := count_eq2_reach_nth newSp cSaved ks listBase bytes
    oldOff oldLen v11 v12 v13 v14 v20 v21 R hRp
  have hsetup := nth_setup_spec listBase listLenW (0 : Word) v11 v12 v13 v14
    (countEq2SetupF newSp ks listBase listLenW cSaved.s2 cSaved.s3 v20 v21
      bytes oldOff oldLen R)
    (countEq2SetupF_pcFree newSp ks listBase listLenW cSaved.s2 cSaved.s3 v20 v21
      bytes oldOff oldLen R hRp)
  have hreachW := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => countEq2_post_to_setup_pre newSp cSaved ks listBase listLenW
      bytes oldOff oldLen v11 v12 v13 v14 v20 v21 R hs0 hs1 h hq) hreach
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hreachW hsetup

/-- Frame for nth call after eq2 setup: kind frame + count BSS pinned at 2. -/
def countEq2NthCallF (newSp : Word) (ks : KindSaved) : Assertion :=
  kindSavedFrame newSp ks ** (MnkCount ↦ₘ (2 : Word))

theorem countEq2NthCallF_pcFree (newSp : Word) (ks : KindSaved) :
    (countEq2NthCallF newSp ks).pcFree := by
  unfold countEq2NthCallF kindSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj

/-- nth Saved constructed for the eq2→nth path (s0 = listBase for ok arm). -/
def eq2NthSaved (listBase listLenW v18 v19 v20 v21 : Word) :
    RlpListNthItemSAsm.Saved :=
  { ra := pc 25, s0 := listBase, s1 := listLenW,
    s2 := v18, s3 := v19, s4 := v20, s5 := v21 }

/-- Drop x5/x6/x7 values, recombine residual stack to 8, reshape into nth call pre. -/
theorem countEq2_setup_to_nth_call_pre
    (newSp : Word) (ks : KindSaved)
    (listBase listLenW : Word) (bytes : List (BitVec 8))
    (oldOff oldLen v18 v19 v20 v21 : Word)
    (R : Assertion)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (h : PartialState)
    (hp : (((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ MnkPathOff) ** (.x14 ↦ᵣ MnkPathLen) **
        countEq2SetupF newSp ks listBase listLenW v18 v19 v20 v21
          bytes oldOff oldLen R) h)) :
    (((.x1 ↦ᵣ (pc 9)) **
      RlpListNthItemSAsm.callEntryRest newSp listBase listLenW (0 : Word)
        MnkPathOff MnkPathLen oldOff oldLen
        (eq2NthSaved listBase listLenW v18 v19 v20 v21) bytes) **
      countEq2NthCallF newSp ks) h := by
  simp only [countEq2SetupF, kindSavedFrame] at hp
  have hx :
      ((.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (2 : Word)) **
        ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
          (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ MnkPathOff) ** (.x14 ↦ᵣ MnkPathLen) **
          (.x1 ↦ᵣ (pc 9)) ** (.x2 ↦ᵣ newSp) ** (R ** stackFree newSp 6) **
          (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
          (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes **
          (MnkCount ↦ₘ (2 : Word)) **
          (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
          ((newSp ↦ₘ ks.ra) ** ((newSp + 8) ↦ₘ ks.s0) **
            ((newSp + 16) ↦ₘ ks.s1)))) h := by
    xperm_chunked hp
  have d1 := sepConj_mono (regIs_implies_regOwn (v := MnkCount) .x5)
    (fun _ x => x) h hx
  have d2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := (2 : Word)) .x6) (fun _ x => x)) h d1
  have d3 := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn (v := (2 : Word)) .x7) (fun _ x => x))) h d2
  have hx2 :
      (((R ** stackFree newSp 6) **
        ((.x1 ↦ᵣ (pc 9)) ** (.x2 ↦ᵣ newSp) **
          (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
          (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
          (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
          (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x13 ↦ᵣ MnkPathOff) ** (.x14 ↦ᵣ MnkPathLen) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase bytes **
          (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen) **
          (MnkCount ↦ₘ (2 : Word)) **
          ((newSp ↦ₘ ks.ra) ** ((newSp + 8) ↦ₘ ks.s0) **
            ((newSp + 16) ↦ₘ ks.s1))))) h := by
    xperm_chunked d3
  rw [← hR] at hx2
  -- Unfold target so xperm sees flat atoms matching hx2.
  simp only [RlpListNthItemSAsm.callEntryRest, RlpListNthItemSAsm.entryRest,
    RlpListNthItemSAsm.savedRegTail, eq2NthSaved, countEq2NthCallF,
    kindSavedFrame] at hx2 ⊢
  xperm_chunked hx2


end EvmAsm.Codegen.MptNodeKindSpec
