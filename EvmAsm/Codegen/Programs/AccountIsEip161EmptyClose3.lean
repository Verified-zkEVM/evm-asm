/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose3

  Field-processing composition for the whole-program K137 contract
  `account_is_eip161_empty_spec_within` (`AccountFields.lean`).

  Consumes the three `rlp_list_nth_item` `returnResult` posts (the K20 call
  adapters `aieCall0`/`aieCall1`/`aieCall3` in `AccountIsEip161EmptyClose.lean`)
  by the standard dispatch pattern (template:
  `RlpFieldToU64SAsm.listResultBranch`): unpack the `∃ status offset len v11 v12`
  return existential, case the semantic `Result` into `Success`/`Failure`, and
  route instruction `bne a0, zero` to the parse-fail verdict or the field body.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose2

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
    | pcFree)

/-- `k`-th instruction membership into the full closure `fullCode`, as the
    singleton→`fullCode` transformer that `cpsBranchWithin_extend_code` and
    `cpsTripleWithin_extend_code` consume. -/
local macro "aieFC" k:term ", " A:term ", " ins:term : term =>
  `((fun a i hi => aie_mono a i
      (CodeReq.ofProg_mem_at AB $A accountIsEip161Empty_prog $k $ins (by bv_omega)
        (by rw [aie_prog_length]; omega) rfl (by rw [aie_prog_length]; norm_num) a i hi)))

/-- Peel a leading existential out of the left operand of a separating
    conjunction. -/
private theorem sepConj_exists_left' {α : Sort _} {F : α → Assertion} {R : Assertion} :
    ∀ h, ((fun hp => ∃ a, F a hp) ** R) h → ∃ a, (F a ** R) h := by
  rintro h ⟨h1, h2, hd, hu, ⟨a, hF⟩, hR⟩
  exact ⟨a, h1, h2, hd, hu, hF, hR⟩

/-! ## Unpacked K20 return state at an AIE call site

    The register-explicit form of `returnResult`'s inner state (the seven
    callee-saved registers restored via `regsAt listNthFrame`, plus the ABI
    outputs and owned scratch), together with the AIE frame slots and the
    output cell that the call adapters frame around it. -/

/-- Unpacked K20 return state, generic over the ABI status `st` and the
    offset/len witnesses. -/
def aieCallCore (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv st offset len v11 v12 : Word) : Assertion :=
  (.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  (.x10 ↦ᵣ st) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes **
  (OffA ↦ₘ offset) ** (LenA ↦ₘ len) **
  savedFrame newSp (mkSaved retA accBase lenW outPtr s3 s4 s5) **
  aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)

theorem pcFree_aieCallCore (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv st offset len v11 v12 : Word) :
    (aieCallCore spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
      bytes outv st offset len v11 v12).pcFree := by
  unfold aieCallCore savedFrame aieSlots
  pcfR

/-- The K20 return as an AIE-shaped semantic result: some status/offset/len,
    the unpacked state, and the pure `Result` fact. -/
def aieCallResult (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv : Word) (oldOff oldLen : Word)
    (listLen index : Nat) : Assertion :=
  fun h => ∃ st offset len v11 v12,
    (aieCallCore spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
        bytes outv st offset len v11 v12 **
      ⌜Result bytes accBase listLen index oldOff oldLen st offset len⌝) h

/-- On K20 success (`status = 0`): the unpacked state and the `Success` fact. -/
def aieSelected (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv : Word) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (aieCallCore spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
        bytes outv 0 offset len v11 v12 **
      ⌜Success bytes accBase listLen index offset len⌝) h

/-- On K20 failure (`status = 1`, cells unchanged): the unpacked state and the
    `Failure` fact. -/
def aieFailed (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word)
    (listLen index : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    (aieCallCore spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
        bytes outv 1 oldOff oldLen v11 v12 **
      ⌜Failure bytes accBase listLen index⌝) h

/-! ## `returnResult` reshape

    The call adapters produce `returnResult ** aieSlots ** (outPtr ↦ₘ outv)`;
    peel the five-fold existential and permute into `aieCallResult`. -/

set_option maxRecDepth 8000 in
theorem aieReturn_to_result
    (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word)
    (listLen index : Nat) : ∀ h,
    (returnResult spA newSp accBase (BitVec.ofNat 64 index) OffA LenA oldOff oldLen
        (mkSaved retA accBase lenW outPtr s3 s4 s5) bytes listLen index **
      aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)) h →
    aieCallResult spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
      bytes outv oldOff oldLen listLen index h := by
  intro h hp
  unfold returnResult at hp
  -- peel the five existentials out of the left operand
  obtain ⟨st, hp⟩ := (sepConj_exists_left' h hp)
  obtain ⟨offset, hp⟩ := (sepConj_exists_left' h hp)
  obtain ⟨len, hp⟩ := (sepConj_exists_left' h hp)
  obtain ⟨v11, hp⟩ := (sepConj_exists_left' h hp)
  obtain ⟨v12, hp⟩ := (sepConj_exists_left' h hp)
  refine ⟨st, offset, len, v11, v12, ?_⟩
  rw [regsAt_listNthFrame] at hp
  simp only [mkSaved] at hp ⊢
  unfold aieCallCore
  simp only [mkSaved]
  xperm_pure hp


/-- `aieCallCore` with the dispatch registers `x10`/`x0` removed — the frame the
    `bne a0, zero` step carries. -/
def aieCallRest (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv offset len v11 v12 : Word) : Assertion :=
  (.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ spA) ** (.x8 ↦ᵣ accBase) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion accBase bytes ** (OffA ↦ₘ offset) ** (LenA ↦ₘ len) **
  savedFrame newSp (mkSaved retA accBase lenW outPtr s3 s4 s5) **
  aieSlots spA raIn c8 c9 c18 ** (outPtr ↦ₘ outv)

theorem pcFree_aieCallRest (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv offset len v11 v12 : Word) :
    (aieCallRest spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
      bytes outv offset len v11 v12).pcFree := by
  unfold aieCallRest savedFrame aieSlots
  pcfR

/-! ## Semantic dispatch of the K20 return

    `aieCallResult` splits into `aieSelected` (K20 `Success`, `a0 = 0`) or
    `aieFailed` (K20 `Failure`, `a0 = 1`) by casing the `Result`. -/

theorem aieResult_cases (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word) (listLen index : Nat) : ∀ h,
    aieCallResult spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
      bytes outv oldOff oldLen listLen index h →
    aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
      bytes outv listLen index h ∨
    aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
      bytes outv oldOff oldLen listLen index h := by
  intro h hq
  unfold aieCallResult at hq
  obtain ⟨st, offset, len, v11, v12, hq⟩ := hq
  extract_pure_deep hq
  obtain ⟨hcore, hresult⟩ := hq
  cases hresult with
  | ok offset len h_ok =>
    exact Or.inl ⟨offset, len, v11, v12, (sepConj_pure_right h).2 ⟨hcore, h_ok⟩⟩
  | fail h_fail =>
    exact Or.inr ⟨v11, v12, (sepConj_pure_right h).2 ⟨hcore, h_fail⟩⟩


set_option maxRecDepth 8000 in
/-- On K20 success, `bne a0, zero` is not taken; the field body follows. -/
theorem aieBranchSelected (entry : Word) (foff : BitVec 13)
    (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word) (listLen index : Nat)
    (hmem : ∀ a i, CodeReq.singleton entry (.BNE .x10 .x0 foff) a = some i →
      fullCode a = some i)
    (hft : entry + signExtend13 foff = AB + 396) :
    cpsBranchWithin 1 entry fullCode
      (aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
        bytes outv listLen index)
      (AB + 396)
        (aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
          bytes outv oldOff oldLen listLen index)
      (entry + 4)
        (aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
          bytes outv listLen index) := by
  unfold aieSelected
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_ok => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 foff (0 : Word) (0 : Word) entry
  rw [hft] at hb0
  have hb1 := cpsBranchWithin_extend_code hmem hb0
  let R : Assertion :=
    aieCallRest spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
      bytes outv offset len v11 v12 **
    ⌜Success bytes accBase listLen index offset len⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (pcFree_aieCallRest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by pcf)) hb1
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold aieCallCore at hp
      unfold R aieCallRest
      xperm_pure hp) (fun h hp => by
      extract_pure_deep hp
      obtain ⟨h_ne, -⟩ := hp
      exact False.elim (h_ne rfl)) (fun h hp => ?_) hbF
  extract_pure_deep hp
  obtain ⟨-, hstate⟩ := hp
  refine ⟨offset, len, v11, v12, ?_⟩
  unfold R aieCallRest at hstate
  unfold aieCallCore
  xperm_pure hstate


set_option maxRecDepth 8000 in
/-- On K20 failure, `bne a0, zero` is taken to the parse-fail verdict. -/
theorem aieBranchFailed (entry : Word) (foff : BitVec 13)
    (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word) (listLen index : Nat)
    (hmem : ∀ a i, CodeReq.singleton entry (.BNE .x10 .x0 foff) a = some i →
      fullCode a = some i)
    (hft : entry + signExtend13 foff = AB + 396) :
    cpsBranchWithin 1 entry fullCode
      (aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
        bytes outv oldOff oldLen listLen index)
      (AB + 396)
        (aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
          bytes outv oldOff oldLen listLen index)
      (entry + 4)
        (aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
          bytes outv listLen index) := by
  unfold aieFailed
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_fail => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 foff (1 : Word) (0 : Word) entry
  rw [hft] at hb0
  have hb1 := cpsBranchWithin_extend_code hmem hb0
  let R : Assertion :=
    aieCallRest spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
      bytes outv oldOff oldLen v11 v12 **
    ⌜Failure bytes accBase listLen index⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (pcFree_aieCallRest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by pcf)) hb1
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold aieCallCore at hp
      unfold R aieCallRest
      xperm_pure hp) (fun h hp => ?_) (fun h hp => by
      extract_pure_deep hp
      obtain ⟨h_eq, -⟩ := hp
      exact False.elim ((by decide : (1 : Word) ≠ 0) h_eq)) hbF
  extract_pure_deep hp
  obtain ⟨-, hstate⟩ := hp
  refine ⟨v11, v12, ?_⟩
  unfold R aieCallRest at hstate
  unfold aieCallCore
  xperm_pure hstate


set_option maxRecDepth 8000 in
/-- **Unified `bne a0, zero` dispatch** over the K20 return existential: parse
    failure branches to the fail verdict `AB+396`; success falls to the field
    body at `entry+4`. -/
theorem aieResultBranch (entry : Word) (foff : BitVec 13)
    (spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word) (listLen index : Nat)
    (hmem : ∀ a i, CodeReq.singleton entry (.BNE .x10 .x0 foff) a = some i →
      fullCode a = some i)
    (hft : entry + signExtend13 foff = AB + 396) :
    cpsBranchWithin 1 entry fullCode
      (aieCallResult spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
        bytes outv oldOff oldLen listLen index)
      (AB + 396)
        (aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
          bytes outv oldOff oldLen listLen index)
      (entry + 4)
        (aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
          bytes outv listLen index) := by
  have hs := aieBranchSelected entry foff spA newSp accBase lenW outPtr raIn c8 c9 c18
    retA s3 s4 s5 bytes outv oldOff oldLen listLen index hmem hft
  have hf := aieBranchFailed entry foff spA newSp accBase lenW outPtr raIn c8 c9 c18
    retA s3 s4 s5 bytes outv oldOff oldLen listLen index hmem hft
  have hor := cpsBranchWithin_pre_or hs hf
  exact cpsBranchWithin_weaken
    (fun h hp => aieResult_cases spA newSp accBase lenW outPtr raIn c8 c9 c18 retA
      s3 s4 s5 bytes outv oldOff oldLen listLen index h hp)
    (fun _ hq => hq) (fun _ hq => hq) hor


/-! ## Per-field dispatch instantiations

    The three concrete `bne a0, zero` dispatches after `aieCall0`/`aieCall1`/
    `aieCall3`.  All three fail-branch to the shared parse-fail verdict `AB+396`;
    on success each falls to its field body. -/

/-- Field-0 (nonce) dispatch `[17]` at `AB+68`: fail → `AB+396`, ok → `AB+72`. -/
theorem aieDispatch0 (spA newSp accBase lenW outPtr raIn c8 c9 c18 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word) (listLen : Nat) :
    cpsBranchWithin 1 (AB + 68) fullCode
      (aieCallResult spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 68) s3 s4 s5
        bytes outv oldOff oldLen listLen 0)
      (AB + 396)
        (aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 68) s3 s4 s5
          bytes outv oldOff oldLen listLen 0)
      (AB + 72)
        (aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 68) s3 s4 s5
          bytes outv listLen 0) := by
  have h := aieResultBranch (AB + 68) (328 : BitVec 13) spA newSp accBase lenW outPtr
    raIn c8 c9 c18 (AB + 68) s3 s4 s5 bytes outv oldOff oldLen listLen 0
    (aieFC 17, (AB + 68), (.BNE .x10 .x0 (328 : BitVec 13)))
    (by rw [show signExtend13 (328 : BitVec 13) = (328 : Word) from by decide]; bv_omega)
  rw [show (AB + 68 : Word) + 4 = AB + 72 from by bv_omega] at h
  exact h


/-- Field-1 (balance) dispatch `[44]` at `AB+176`: fail → `AB+396`, ok → `AB+180`. -/
theorem aieDispatch1 (spA newSp accBase lenW outPtr raIn c8 c9 c18 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word) (listLen : Nat) :
    cpsBranchWithin 1 (AB + 176) fullCode
      (aieCallResult spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 176) s3 s4 s5
        bytes outv oldOff oldLen listLen 1)
      (AB + 396)
        (aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 176) s3 s4 s5
          bytes outv oldOff oldLen listLen 1)
      (AB + 180)
        (aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 176) s3 s4 s5
          bytes outv listLen 1) := by
  have h := aieResultBranch (AB + 176) (220 : BitVec 13) spA newSp accBase lenW outPtr
    raIn c8 c9 c18 (AB + 176) s3 s4 s5 bytes outv oldOff oldLen listLen 1
    (aieFC 44, (AB + 176), (.BNE .x10 .x0 (220 : BitVec 13)))
    (by rw [show signExtend13 (220 : BitVec 13) = (220 : Word) from by decide]; bv_omega)
  rw [show (AB + 176 : Word) + 4 = AB + 180 from by bv_omega] at h
  exact h


/-- Field-3 (code_hash) dispatch `[68]` at `AB+272`: fail → `AB+396`, ok → `AB+276`. -/
theorem aieDispatch3 (spA newSp accBase lenW outPtr raIn c8 c9 c18 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word) (listLen : Nat) :
    cpsBranchWithin 1 (AB + 272) fullCode
      (aieCallResult spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 272) s3 s4 s5
        bytes outv oldOff oldLen listLen 3)
      (AB + 396)
        (aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 272) s3 s4 s5
          bytes outv oldOff oldLen listLen 3)
      (AB + 276)
        (aieSelected spA newSp accBase lenW outPtr raIn c8 c9 c18 (AB + 272) s3 s4 s5
          bytes outv listLen 3) := by
  have h := aieResultBranch (AB + 272) (124 : BitVec 13) spA newSp accBase lenW outPtr
    raIn c8 c9 c18 (AB + 272) s3 s4 s5 bytes outv oldOff oldLen listLen 3
    (aieFC 68, (AB + 272), (.BNE .x10 .x0 (124 : BitVec 13)))
    (by rw [show signExtend13 (124 : BitVec 13) = (124 : Word) from by decide]; bv_omega)
  rw [show (AB + 272 : Word) + 4 = AB + 276 from by bv_omega] at h
  exact h


/-! ## Parse-fail return bridge (`aieFailed` at `AB+396` → `raIn`)

    The residual owned/frame state carried untouched from the K20 return
    through the fail verdict tail and epilogue to the caller. -/

/-- The untouched residual carried across the fail bridge (everything except the
    dispatch/frame registers `aieRetFail` restores), keeping the K20 `Failure`
    witness live. -/
def aieFailG (newSp accBase lenW outPtr retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen v11 v12 : Word)
    (listLen index : Nat) : Assertion :=
  (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes **
  (OffA ↦ₘ oldOff) ** (LenA ↦ₘ oldLen) **
  savedFrame newSp (mkSaved retA accBase lenW outPtr s3 s4 s5) **
  (outPtr ↦ₘ outv) ** ⌜Failure bytes accBase listLen index⌝

theorem pcFree_aieFailG (newSp accBase lenW outPtr retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen v11 v12 : Word)
    (listLen index : Nat) :
    (aieFailG newSp accBase lenW outPtr retA s3 s4 s5 bytes outv oldOff oldLen
      v11 v12 listLen index).pcFree := by
  unfold aieFailG savedFrame
  pcfR

set_option maxRecDepth 8000 in
/-- Parse-fail return bridge: from the K20-failure return state at `AB+396`,
    set `a0 = 1`, restore the frame, and return to `raIn`, leaving the output
    cell untouched and carrying the `Failure` witness. -/
theorem aieFailToRet (sp0 spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (outv oldOff oldLen : Word) (listLen index : Nat)
    (hspA : spA = sp0 + signExtend12 (-40 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 8 (AB + 396) raIn fullCode
      (aieFailed spA newSp accBase lenW outPtr raIn c8 c9 c18 retA s3 s4 s5
        bytes outv oldOff oldLen listLen index)
      (fun h => ∃ v11 v12,
        ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) **
          (.x18 ↦ᵣ c18) ** aieSlots spA raIn c8 c9 c18 ** (.x10 ↦ᵣ (1 : Word)) **
          aieFailG newSp accBase lenW outPtr retA s3 s4 s5 bytes outv oldOff oldLen
            v11 v12 listLen index) h) := by
  unfold aieFailed
  refine cpsTripleWithin_exists_assertion (fun v11 => ?_)
  refine cpsTripleWithin_exists_assertion (fun v12 => ?_)
  have hepi := aieRetFail sp0 spA raIn c8 c9 c18 retA accBase lenW outPtr (1 : Word)
    (aieFailG newSp accBase lenW outPtr retA s3 s4 s5 bytes outv oldOff oldLen
      v11 v12 listLen index)
    (pcFree_aieFailG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) hspA hret
  refine cpsTripleWithin_weaken ?_ ?_ hepi
  · intro h hp
    unfold aieCallCore at hp
    unfold aieFailG
    xperm_chunked hp
  · intro h hq
    exact ⟨v11, v12, hq⟩


end EvmAsm.Codegen.AccountIsEip161EmptySpec
