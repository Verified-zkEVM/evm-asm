/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose5

  The three field-body OK-paths and the top-level whole-program assembly for
  the K137 contract `account_is_eip161_empty_spec_within` (`AccountFields.lean`).

  Builds on the field-3 size-check + pointer-setup + model scaffolding
  (`AccountIsEip161EmptyClose4.lean`), the dispatch infrastructure
  (`AccountIsEip161EmptyClose3.lean`), the verdict-store tails + return bridges
  (`AccountIsEip161EmptyClose2.lean`), the RLP call adapters + prologue/epilogue
  (`AccountIsEip161EmptyClose.lean`), and the three byte-scan loop lemmas
  (`AccountIsEip161EmptyLoop.lean`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose4

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! ## Generic helpers -/

/-- Introduce SEVEN owned registers' values at once (trailing `regOwn` chain). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn7
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 r4 r5 r6 r7 : Reg}
    {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5 v6 v7, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) **
       (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact h v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2,
        g6, g7, d4, u4, hv3, g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
        g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

/-- Least-index witness of a bounded universal's failure. -/
theorem first_mismatch {P : Nat → Prop} [DecidablePred P] {n : Nat}
    (h : ¬ ∀ k, k < n → P k) :
    ∃ j, j < n ∧ (∀ k, k < j → P k) ∧ ¬ P j := by
  obtain ⟨k0, hk0⟩ : ∃ k, k < n ∧ ¬ P k := by
    obtain ⟨k, hk⟩ := Classical.not_forall.mp h
    obtain ⟨hlt, hnp⟩ := Classical.not_imp.mp hk
    exact ⟨k, hlt, hnp⟩
  have hex : ∃ k, ¬ P k := ⟨k0, hk0.2⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · exact Nat.lt_of_le_of_lt (Nat.find_le hk0.2) hk0.1
  · intro k hk
    exact not_not.mp (Nat.find_min hex hk)

/-- `offset = BitVec.ofNat 64 offset.toNat` for a 64-bit word. -/
theorem word_eq_ofNat_toNat (w : Word) : w = BitVec.ofNat 64 w.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

/-- `aieJunk` with the leading `regOwn .x5` removed; the owned residual the
    verdict-return bridges carry (their `x5` is threaded separately). -/
def aieJunkNoX5 (newSp accBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  memOwn OffA ** memOwn LenA **
  memOwn newSp ** memOwn (newSp + 8) ** memOwn (newSp + 16) ** memOwn (newSp + 24) **
  memOwn (newSp + 32) ** memOwn (newSp + 40) ** memOwn (newSp + 48) **
  bytesRegion accBase bytes ** bytesRegion ECB aieEmptyCodeHashBytes

/-- `aieJunk = regOwn .x5 ** aieJunkNoX5` — the two agree definitionally. -/
theorem aieJunk_eq (newSp accBase : Word) (bytes : List (BitVec 8)) :
    aieJunk newSp accBase bytes = (regOwn .x5 ** aieJunkNoX5 newSp accBase bytes) := rfl

theorem pcFree_aieJunkNoX5 (newSp accBase : Word) (bytes : List (BitVec 8)) :
    (aieJunkNoX5 newSp accBase bytes).pcFree := by
  unfold aieJunkNoX5
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj

/-- `aieJunk` with the `(.x0 ↦ᵣ 0)` cell removed; the residual the not-empty
    verdict-return bridge carries (its `x0` is threaded separately). -/
def aieJunkNoX0 (newSp accBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  memOwn OffA ** memOwn LenA **
  memOwn newSp ** memOwn (newSp + 8) ** memOwn (newSp + 16) ** memOwn (newSp + 24) **
  memOwn (newSp + 32) ** memOwn (newSp + 40) ** memOwn (newSp + 48) **
  bytesRegion accBase bytes ** bytesRegion ECB aieEmptyCodeHashBytes

theorem pcFree_aieJunkNoX0 (newSp accBase : Word) (bytes : List (BitVec 8)) :
    (aieJunkNoX0 newSp accBase bytes).pcFree := by
  unfold aieJunkNoX0
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj

/-! ## Folding the verdict-return-bridge posts into the abstract `aiePost`. -/

/-- Inject the four-way `aieOutcome` pure fact into the abstract return post. -/
theorem aiePost_intro (sp0 spA raIn c8 c9 c18 newSp accBase outPtr : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) (a0 outVal : Word)
    (hout : aieOutcome bytes accBase listLen a0 outVal) : ∀ h,
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) **
      aieSlots spA raIn c8 c9 c18 ** (.x10 ↦ᵣ a0) ** (outPtr ↦ₘ outVal) **
      aieJunk newSp accBase bytes) h →
    aiePost sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen h := by
  intro h hp
  refine ⟨a0, outVal, ?_⟩
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (fun hh hj => (sepConj_pure_right hh).2 ⟨hj, hout⟩)))))))) h hp

/-- Empty return-bridge post → `aiePost` (a0 = 0, out = 1, empty verdict). -/
theorem aieEmptyPost_to_aiePost (sp0 spA raIn c8 c9 c18 newSp accBase outPtr : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hempty : accountEip161Empty bytes accBase listLen) : ∀ h,
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) **
      aieSlots spA raIn c8 c9 c18 ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
      (outPtr ↦ₘ (1 : Word)) ** aieJunkNoX5 newSp accBase bytes) h →
    aiePost sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen h := by
  intro h hp
  have hp2 := (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (regIs_implies_regOwn .x5)))))))) h hp
  refine aiePost_intro sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen 0 1
    (Or.inl ⟨rfl, rfl, hempty⟩) h ?_
  unfold aieJunk aieJunkNoX5 at *
  xperm_chunked hp2

/-- Not-empty return-bridge post → `aiePost` (a0 = 0, out = 0). -/
theorem aieNotEmptyPost_to_aiePost (sp0 spA raIn c8 c9 c18 newSp accBase outPtr : Word)
    (bytes : List (BitVec 8)) (listLen : Nat) : ∀ h,
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ c8) ** (.x9 ↦ᵣ c9) ** (.x18 ↦ᵣ c18) **
      aieSlots spA raIn c8 c9 c18 ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
      (outPtr ↦ₘ (0 : Word)) ** aieJunkNoX0 newSp accBase bytes) h →
    aiePost sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen h := by
  intro h hp
  refine aiePost_intro sp0 spA raIn c8 c9 c18 newSp accBase outPtr bytes listLen 0 0
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) h ?_
  unfold aieJunk aieJunkNoX0 at *
  xperm_chunked hp

/-! ## Boundary folds: field-3 loop/size-exit residuals into the owned residual. -/

/-- Downgrade the seven callee-saved frame cells to `memOwn`. -/
theorem savedFrame_to_memOwns (newSp : Word) (saved : Saved) : ∀ h,
    savedFrame newSp saved h →
    (memOwn newSp ** memOwn (newSp + 8) ** memOwn (newSp + 16) ** memOwn (newSp + 24) **
      memOwn (newSp + 32) ** memOwn (newSp + 40) ** memOwn (newSp + 48)) h := by
  intro h hp
  unfold savedFrame at hp
  exact sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))))) h hp

/-- The field-3 content-loop / size-exit residual in `aieJunkNoX5` order, with
    the callee-saved frame cells inlined (`x5`/`x0` are threaded by the bridges). -/
def aieResMixedNoX5 (newSp accBase : Word) (bytes : List (BitVec 8))
    (v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) : Assertion :=
  regOwn .x6 ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  (OffA ↦ₘ offset) ** (LenA ↦ₘ len) **
  (newSp ↦ₘ fr0) ** ((newSp + 8) ↦ₘ fr1) ** ((newSp + 16) ↦ₘ fr2) **
  ((newSp + 24) ↦ₘ fr3) ** ((newSp + 32) ↦ₘ fr4) ** ((newSp + 40) ↦ₘ fr5) **
  ((newSp + 48) ↦ₘ fr6) **
  bytesRegion accBase bytes ** bytesRegion ECB aieEmptyCodeHashBytes

theorem pcFree_aieResMixedNoX5 (newSp accBase : Word) (bytes : List (BitVec 8))
    (v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) :
    (aieResMixedNoX5 newSp accBase bytes v7 v11 v12 s3 s4 s5 offset len
      fr0 fr1 fr2 fr3 fr4 fr5 fr6).pcFree := by
  unfold aieResMixedNoX5
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj

theorem aieResMixedNoX5_to_aieJunkNoX5 (newSp accBase : Word) (bytes : List (BitVec 8))
    (v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) : ∀ h,
    aieResMixedNoX5 newSp accBase bytes v7 v11 v12 s3 s4 s5 offset len
      fr0 fr1 fr2 fr3 fr4 fr5 fr6 h →
    aieJunkNoX5 newSp accBase bytes h := by
  intro h hp
  unfold aieResMixedNoX5 at hp
  unfold aieJunkNoX5
  refine sepConj_mono (fun _ h => h) ?_ h hp
  refine sepConj_mono (regIs_implies_regOwn .x7) ?_
  refine sepConj_mono (regIs_implies_regOwn .x11) ?_
  refine sepConj_mono (regIs_implies_regOwn .x12) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (regIs_implies_regOwn .x19) ?_
  refine sepConj_mono (regIs_implies_regOwn .x20) ?_
  refine sepConj_mono (regIs_implies_regOwn .x21) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono (fun _ h => h) ?_
  exact fun _ h => h

/-- The field-3 loop-exit residual keeping `x5`, in `aieJunkNoX0` order
    (`x0` is threaded by the not-empty bridge). -/
def aieResMixedNoX0 (newSp accBase : Word) (bytes : List (BitVec 8))
    (v5 v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) : Assertion :=
  (.x5 ↦ᵣ v5) ** regOwn .x6 ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (OffA ↦ₘ offset) ** (LenA ↦ₘ len) **
  (newSp ↦ₘ fr0) ** ((newSp + 8) ↦ₘ fr1) ** ((newSp + 16) ↦ₘ fr2) **
  ((newSp + 24) ↦ₘ fr3) ** ((newSp + 32) ↦ₘ fr4) ** ((newSp + 40) ↦ₘ fr5) **
  ((newSp + 48) ↦ₘ fr6) **
  bytesRegion accBase bytes ** bytesRegion ECB aieEmptyCodeHashBytes

theorem pcFree_aieResMixedNoX0 (newSp accBase : Word) (bytes : List (BitVec 8))
    (v5 v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) :
    (aieResMixedNoX0 newSp accBase bytes v5 v7 v11 v12 s3 s4 s5 offset len
      fr0 fr1 fr2 fr3 fr4 fr5 fr6).pcFree := by
  unfold aieResMixedNoX0
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj

theorem aieResMixedNoX0_to_aieJunkNoX0 (newSp accBase : Word) (bytes : List (BitVec 8))
    (v5 v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) : ∀ h,
    aieResMixedNoX0 newSp accBase bytes v5 v7 v11 v12 s3 s4 s5 offset len
      fr0 fr1 fr2 fr3 fr4 fr5 fr6 h →
    aieJunkNoX0 newSp accBase bytes h := by
  intro h hp
  unfold aieResMixedNoX0 at hp
  unfold aieJunkNoX0
  refine sepConj_mono (regIs_implies_regOwn .x5) ?_ h hp
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (regIs_implies_regOwn .x7) ?_
  refine sepConj_mono (regIs_implies_regOwn .x11) ?_
  refine sepConj_mono (regIs_implies_regOwn .x12) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (regIs_implies_regOwn .x19) ?_
  refine sepConj_mono (regIs_implies_regOwn .x20) ?_
  refine sepConj_mono (regIs_implies_regOwn .x21) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono (fun _ h => h) ?_
  exact fun _ h => h

/-- The field-3 size-fail residual (no content loop ran) with the output cell,
    in `(outPtr ↦ₘ 0) ** aieJunk` order. -/
def aieResMixedSizeFail (newSp accBase outPtr : Word) (bytes : List (BitVec 8))
    (v5 v6 v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) : Assertion :=
  (outPtr ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
  (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  (OffA ↦ₘ offset) ** (LenA ↦ₘ len) **
  (newSp ↦ₘ fr0) ** ((newSp + 8) ↦ₘ fr1) ** ((newSp + 16) ↦ₘ fr2) **
  ((newSp + 24) ↦ₘ fr3) ** ((newSp + 32) ↦ₘ fr4) ** ((newSp + 40) ↦ₘ fr5) **
  ((newSp + 48) ↦ₘ fr6) **
  bytesRegion accBase bytes ** bytesRegion ECB aieEmptyCodeHashBytes

theorem pcFree_aieResMixedSizeFail (newSp accBase outPtr : Word) (bytes : List (BitVec 8))
    (v5 v6 v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) :
    (aieResMixedSizeFail newSp accBase outPtr bytes v5 v6 v7 v11 v12 s3 s4 s5 offset len
      fr0 fr1 fr2 fr3 fr4 fr5 fr6).pcFree := by
  unfold aieResMixedSizeFail
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj

theorem aieResMixedSizeFail_to_junk (newSp accBase outPtr : Word) (bytes : List (BitVec 8))
    (v5 v6 v7 v11 v12 s3 s4 s5 offset len fr0 fr1 fr2 fr3 fr4 fr5 fr6 : Word) : ∀ h,
    aieResMixedSizeFail newSp accBase outPtr bytes v5 v6 v7 v11 v12 s3 s4 s5 offset len
      fr0 fr1 fr2 fr3 fr4 fr5 fr6 h →
    ((outPtr ↦ₘ (0 : Word)) ** aieJunk newSp accBase bytes) h := by
  intro h hp
  unfold aieResMixedSizeFail at hp
  unfold aieJunk
  refine sepConj_mono (fun _ h => h) ?_ h hp
  refine sepConj_mono (regIs_implies_regOwn .x5) ?_
  refine sepConj_mono (regIs_implies_regOwn .x6) ?_
  refine sepConj_mono (regIs_implies_regOwn .x7) ?_
  refine sepConj_mono (regIs_implies_regOwn .x11) ?_
  refine sepConj_mono (regIs_implies_regOwn .x12) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (regIs_implies_regOwn .x19) ?_
  refine sepConj_mono (regIs_implies_regOwn .x20) ?_
  refine sepConj_mono (regIs_implies_regOwn .x21) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono (fun _ h => h) ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono memIs_implies_memOwn ?_
  refine sepConj_mono (fun _ h => h) ?_
  exact fun _ h => h

end EvmAsm.Codegen.AccountIsEip161EmptySpec
