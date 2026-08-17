/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec

  K73's callee composition layer.  `HeaderBaseFeeSpec` contains the linked
  arithmetic seams and the equal-target route; this module keeps the larger
  call/branch composition out of that file's Codegen/Programs line cap.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeSpec
import EvmAsm.Codegen.Proofs.HandlerHandlesUnary
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Codegen.Proofs.U256IsZeroSpec

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256DivU64BeSAsm

/-! The zero test consumes four dword cells, while K73's caller contract owns
    the same 32 bytes as one `bytesRegion`.  Keep this bridge local to the
    caller composition; it does not change the public memory vocabulary. -/
theorem k73_bytes4cells (ptr : Word) (bs : List (BitVec 8))
    (hlen : bs.length = 32) :
    bytesRegion ptr bs =
      ((ptr ↦ₘ packBytes ((bs.drop 0).take 8)) **
       ((ptr + 8) ↦ₘ packBytes ((bs.drop 8).take 8)) **
       ((ptr + 16) ↦ₘ packBytes ((bs.drop 16).take 8)) **
       ((ptr + 24) ↦ₘ packBytes ((bs.drop 24).take 8))) := by
  simpa [EvmAsm.Codegen.Proofs.wsDword] using (bytesRegion_eq_4cells ptr bs hlen)

/-! The increase arm's register setup after the shared head.  Keeping this
    separate from the multiply call makes the caller-to-callee boundary
    explicit: the delta is formed in `x19`, then the multiply ABI arguments
    are installed in `x10`--`x12`. -/
def k73IncreaseSetupPost
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) **
  (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) ** (.x18 ↦ᵣ target) **
  (.x19 ↦ᵣ (gasUsed - target)) ** (.x20 ↦ᵣ 1) **
  (.x10 ↦ᵣ basePtr) ** (.x11 ↦ᵣ (gasUsed - target)) **
  (.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ outPtr) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
  frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
  bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F

theorem k73_increase_setup_spec_within
    (spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) :
    cpsTripleWithin 5 (K73 + 64) (K73 + 84) wholeCode
      (k73HeadPost spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes outBytes F)
      (k73IncreaseSetupPost spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes outBytes F) := by
  have h0 := li_spec_gen_within .x20 v20 (1 : Word) (K73 + 64) (by decide)
  have h0' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mem 16 _ (K73 + 64) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi) h0
  have h0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) **
      (.x9 ↦ᵣ outPtr) ** (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ v19) **
      (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) **
      (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ 0) ** frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) h0'
  have h1 := sub_spec_gen_within .x19 .x11 .x18 gasUsed target v19
    (K73 + 68) (by decide)
  have h1' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mem 17 _ (K73 + 68) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi) h1
  have h1F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) **
      (.x9 ↦ᵣ outPtr) ** (.x20 ↦ᵣ (1 : Word)) **
      (.x10 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) h1'
  have h2 := mv_spec_gen_within .x10 .x8 basePtr gasLimit (K73 + 72) (by decide)
  have h2' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mem 18 _ (K73 + 72) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi) h2
  have h2F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) **
      (.x9 ↦ᵣ outPtr) ** (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ (gasUsed - target)) **
      (.x20 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ gasUsed) **
      (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** (.x0 ↦ᵣ 0) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) h2'
  have h3 := mv_spec_gen_within .x11 .x19 (gasUsed - target) gasUsed
    (K73 + 76) (by decide)
  have h3' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mem 19 _ (K73 + 76) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi) h3
  have h3F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) **
      (.x9 ↦ᵣ outPtr) ** (.x18 ↦ᵣ target) **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x10 ↦ᵣ basePtr) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) h3'
  have h4 := mv_spec_gen_within .x12 .x9 outPtr basePtr (K73 + 80) (by decide)
  have h4' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mem 20 _ (K73 + 80) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi) h4
  have h4F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) **
      (.x18 ↦ᵣ target) **
      (.x19 ↦ᵣ (gasUsed - target)) ** (.x20 ↦ᵣ (1 : Word)) **
      (.x10 ↦ᵣ basePtr) ** (.x11 ↦ᵣ (gasUsed - target)) **
      (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ 0) ** frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) h4'
  simp [k73Frame, k73Saved, frameSlotsSaved] at h0F h1F h2F h3F h4F
  have h01 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h01 h2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h012 h3F
  have h01234 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h0123 h4F
  unfold k73HeadPost k73IncreaseSetupPost at *
  simp [k73Frame, k73Saved, frameSlotsSaved] at *
  exact cpsTripleWithin_weaken (by xsimp) (by xsimp) h01234

/-! `mulWhole_spec` keeps the saved return address inside its epilogue post.
    Calls need that cell factored out so `callWithin_spec` can install its
    own return address.  The remainder is deliberately the same frame,
    overflow and output relation as the callee theorem. -/
def k73MulEpilogueNoRa
    (spNew vRa v8 v9 v18 v19 v20 : Word) : Assertion :=
  ((.x2 : Reg) ↦ᵣ (spNew + signExtend12 (48 : BitVec 12))) **
    ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
    ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
    ((.x20 : Reg) ↦ᵣ v20) **
    EvmAsm.Codegen.U256MulU64Be.frameSlots spNew vRa v8 v9 v18 v19 v20

def k73MulOverflowNoRa
    (spNew vRa v8 v9 v18 v19 v20 outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) : Assertion :=
  fun s =>
    (∃ k, (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
      bytesRegion outPtr outBytes **
      EvmAsm.Codegen.U256MulU64Be.overflowNonzeroCore accBytes k) s) ∨
    (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
      bytesRegion outPtr outBytes **
      EvmAsm.Codegen.U256MulU64Be.overflowZeroCore accBytes 8) s

def k73MulBodyPostNoRa
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (aBytes : List (BitVec 8)) (accBytes outBytes : List (BitVec 8)) : Assertion :=
  EvmAsm.Codegen.U256MulU64Be.mulTailExtra aPtr b outPtr aBytes **
    k73MulOverflowNoRa spNew vRa v8 v9 v18 v19 v20 outPtr accBytes outBytes

def k73MulPreNoRa
    (spOld v8 v9 v18 v19 v20 aPtr b outPtr v13 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (aBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x2 : Reg) ↦ᵣ spOld) ** ((.x8 : Reg) ↦ᵣ v8) **
    ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
    ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ v13) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 **
    regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    EvmAsm.Codegen.U256MulU64Be.frameSlots
      (spOld + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
    bytesRegion aPtr aBytes ** bytesRegion
      EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
    bytesRegion outPtr outBytes ** F

theorem k73_mul_epilogue_factor
    (spNew vRa v8 v9 v18 v19 v20 : Word) :
    ∀ s,
      EvmAsm.Codegen.U256MulU64Be.mulEpiloguePost
        spNew vRa v8 v9 v18 v19 v20 s →
      (((.x1 : Reg) ↦ᵣ vRa) **
        k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20) s := by
  intro s hs
  dsimp [EvmAsm.Codegen.U256MulU64Be.mulEpiloguePost,
    k73MulEpilogueNoRa] at hs ⊢
  xperm_hyp hs

theorem k73_mul_overflow_factor
    (spNew vRa v8 v9 v18 v19 v20 outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) :
    ∀ s,
      EvmAsm.Codegen.U256MulU64Be.overflowTailPost
        spNew vRa v8 v9 v18 v19 v20 outPtr accBytes outBytes s →
      (((.x1 : Reg) ↦ᵣ vRa) **
        k73MulOverflowNoRa spNew vRa v8 v9 v18 v19 v20 outPtr
          accBytes outBytes) s := by
  intro s hs
  dsimp [EvmAsm.Codegen.U256MulU64Be.overflowTailPost,
    k73MulOverflowNoRa] at hs ⊢
  rcases hs with hs | hs
  ·
    rcases hs with ⟨k, hk⟩
    have hbranch :
        (((.x1 : Reg) ↦ᵣ vRa) **
          (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
            bytesRegion outPtr outBytes **
            EvmAsm.Codegen.U256MulU64Be.overflowNonzeroCore accBytes k)) s := by
      dsimp [EvmAsm.Codegen.U256MulU64Be.mulEpiloguePost,
        k73MulEpilogueNoRa] at hk ⊢
      xperm_hyp hk
    unfold k73MulOverflowNoRa at ⊢
    exact sepConj_mono_right (fun _ h => Or.inl ⟨k, h⟩) s hbranch
  ·
    have hbranch :
        (((.x1 : Reg) ↦ᵣ vRa) **
          (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
            bytesRegion outPtr outBytes **
            EvmAsm.Codegen.U256MulU64Be.overflowZeroCore accBytes 8)) s := by
      dsimp [EvmAsm.Codegen.U256MulU64Be.mulEpiloguePost,
        k73MulEpilogueNoRa] at hs ⊢
      xperm_hyp hs
    unfold k73MulOverflowNoRa at ⊢
    exact sepConj_mono_right (fun _ h => Or.inr h) s hbranch

theorem k73_mul_body_post_factor
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (aBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) :
    ∀ s,
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
        spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr aBytes accBytes outBytes ** F) s →
      (((.x1 : Reg) ↦ᵣ vRa) **
        (k73MulBodyPostNoRa spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          aBytes accBytes outBytes ** F)) s := by
  intro s hs
  have hover := k73_mul_overflow_factor spNew vRa v8 v9 v18 v19 v20
    outPtr accBytes outBytes
  unfold EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost at hs
  have hcore : ∀ s,
      (EvmAsm.Codegen.U256MulU64Be.mulTailExtra aPtr b outPtr aBytes **
        EvmAsm.Codegen.U256MulU64Be.overflowTailPost
          spNew vRa v8 v9 v18 v19 v20 outPtr accBytes outBytes) s →
      (((.x1 : Reg) ↦ᵣ vRa) **
        k73MulBodyPostNoRa spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          aBytes accBytes outBytes) s := by
    intro s hs
    have hs' := sepConj_mono_right
      (Q := EvmAsm.Codegen.U256MulU64Be.overflowTailPost
        spNew vRa v8 v9 v18 v19 v20 outPtr accBytes outBytes)
      (Q' := ((.x1 : Reg) ↦ᵣ vRa) **
        k73MulOverflowNoRa spNew vRa v8 v9 v18 v19 v20 outPtr
          accBytes outBytes)
      (fun h hq => hover h hq) s hs
    dsimp [k73MulBodyPostNoRa]
    xperm_hyp hs'
  have hs' := sepConj_mono_left hcore s hs
  dsimp [k73MulBodyPostNoRa] at hs' ⊢
  xperm_hyp hs'

/-! A complete K73 multiply call adapter.  The raw whole-multiply theorem is
    accepted at the callee boundary and its saved `x1` is factored only at
    this interface, preserving the full overflow relation for callers. -/
theorem k73_mul_call_spec_within
    {cr : CodeReq} {n : Nat}
    (callerPC calleeEntry oldRa spOld spNew v8 v9 v18 v19 v20 aPtr b outPtr v13 : Word)
    (offset : BitVec 21) (F : Assertion) (hF : F.pcFree)
    (f0 f1 f2 f3 f4 f5 : Word)
    (aBytes accBytes outBytes : List (BitVec 8))
    (hcallee : cpsTripleWithin n calleeEntry (callerPC + 4) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre F spOld (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr v13 f0 f1 f2 f3 f4 f5
        aBytes accBytes outBytes)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost spNew (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr aBytes accBytes outBytes ** F))
    (htarget : callerPC + signExtend21 offset = calleeEntry)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
      cr a = some i)
    (hcalleeMem : ∀ a i, mulCode a = some i → cr a = some i) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ oldRa) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accBytes outBytes F))
      (((.x1 ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accBytes outBytes ** F))) := by
  have hcalleeC := cpsTripleWithin_extend_code hcalleeMem hcallee
  have hcallee' : cpsTripleWithin n calleeEntry (callerPC + 4) cr
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accBytes outBytes F)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accBytes outBytes ** F)) := by
    refine cpsTripleWithin_weaken (nSteps := n) (entry := calleeEntry)
      (exit_ := callerPC + 4) (cr := cr)
      (P := EvmAsm.Codegen.U256MulU64Be.mulWholePre F spOld (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr v13 f0 f1 f2 f3 f4 f5
        aBytes accBytes outBytes)
      (P' := ((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accBytes outBytes F)
      (Q := EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost spNew (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr aBytes accBytes outBytes ** F)
      (Q' := ((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accBytes outBytes ** F))
      ?_ ?_ hcalleeC
    · intro h hp
      dsimp [EvmAsm.Codegen.U256MulU64Be.mulWholePre, k73MulPreNoRa] at hp ⊢
      xperm_hyp hp
    · intro s hq
      exact k73_mul_body_post_factor spNew (callerPC + 4) v8 v9 v18 v19 v20
        aPtr b outPtr aBytes accBytes outBytes F s hq
  have hP : (k73MulPreNoRa spOld v8 v9 v18 v19 v20
      aPtr b outPtr v13 f0 f1 f2 f3 f4 f5 aBytes accBytes outBytes F).pcFree := by
    dsimp [k73MulPreNoRa]
    pcf
    exact hF
  have hcall := callWithin_spec callerPC calleeEntry oldRa offset n
    htarget hmem hP hcallee'
  exact hcall

@[irreducible] def k73IncreaseMulPre
    (spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  k73HeadPost spH raIn gasLimit gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes outBytes
    (EvmAsm.Codegen.U256MulU64Be.frameSlots
      (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** F)

def k73IncreaseMulPost
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (K73 + 88)) **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (k73MulBodyPostNoRa (spH + signExtend12 (-48 : BitVec 12))
      (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word)
      basePtr (gasUsed - target) outPtr baseBytes accBytes outBytes ** F)

@[irreducible] def k73IncreaseMulCalleePre
    (spH basePtr outPtr target gasUsed : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  EvmAsm.Codegen.U256MulU64Be.mulWholePre F spH (K73 + 88)
    basePtr outPtr target (gasUsed - target) (1 : Word)
    basePtr (gasUsed - target) outPtr outPtr f0 f1 f2 f3 f4 f5
    baseBytes accBytes outBytes

@[irreducible] def k73IncreaseMulCalleePost
    (spH basePtr outPtr target gasUsed : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
    (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
    basePtr outPtr target (gasUsed - target) (1 : Word)
    basePtr (gasUsed - target) outPtr baseBytes accBytes outBytes ** F

/-! The increase setup feeds the linked multiply routine.  The temporary
    multiply frame and accumulator are caller-owned resources at this seam;
    `mulWhole_spec` consumes them and returns the complete overflow relation
    needed by the following status branch. -/
theorem k73_increase_mul_spec_within
    (spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes F)
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes F)) :
    cpsTripleWithin 3856 (K73 + 64) (K73 + 88) wholeCode
      (k73IncreaseMulPre spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes F)
      (k73IncreaseMulPost spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes outBytes F) := by
  let Fmul : Assertion :=
    EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** F
  have hFmul : Fmul.pcFree := by
    dsimp [Fmul]
    pcf
    exact hF
  have hsetup := k73_increase_setup_spec_within
    spH raIn gasLimit gasUsed basePtr outPtr target v8 v9 v18 v19 v20
    baseBytes outBytes Fmul hFmul
  have htarget :
      (K73 + 84) + signExtend21
        (jalOff GuestAddrs.u256_mul_u64_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 84)) =
      (GuestAddrs.u256_mul_u64_be : Word) := by
    change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 84 + _ = BitVec.ofNat 64 GuestAddrs.u256_mul_u64_be
    exact jalOff_correct_add GuestAddrs.u256_mul_u64_be
      GuestAddrs.eip1559_calc_base_fee_per_gas 84
      (by decide) (by decide) (by decide) (by decide)
  have hmem : ∀ a i, CodeReq.singleton (K73 + 84)
      (.JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 84))) a = some i →
      wholeCode a = some i := by
    intro a i hi
    exact k73_whole_mono a i (k73_mem 21 _ (K73 + 84) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi)
  have hcalleeMem : ∀ a i, mulCode a = some i → wholeCode a = some i :=
    mul_whole_mono
  have hcallee' : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre F spH (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word)
        basePtr (gasUsed - target) outPtr outPtr f0 f1 f2 f3 f4 f5
        baseBytes accBytes outBytes)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word)
        basePtr (gasUsed - target) outPtr baseBytes accBytes outBytes ** F) := by
    simpa only [k73IncreaseMulCalleePre, k73IncreaseMulCalleePost] using hcallee
  let Fframe : Assertion :=
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20)
  have hFframe : Fframe.pcFree := by
    dsimp [Fframe]
    exact pcFree_frameSlotsSaved _ _ _
  have hcalleeFramed := cpsTripleWithin_frameR Fframe hFframe hcallee'
  have hcallee'' : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre (Fframe ** F) spH (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word)
        basePtr (gasUsed - target) outPtr outPtr f0 f1 f2 f3 f4 f5
        baseBytes accBytes outBytes)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word)
        basePtr (gasUsed - target) outPtr baseBytes accBytes outBytes **
        (Fframe ** F)) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [Fframe,
          EvmAsm.Codegen.U256MulU64Be.mulWholePre] at hp ⊢
        xperm_hyp hp)
      (fun s hq => by
        dsimp [Fframe,
          EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost] at hq ⊢
        xperm_hyp hq)
      hcalleeFramed
  let Fcall : Assertion := Fframe ** F
  have hFcall : Fcall.pcFree := by
    dsimp [Fcall]
    exact pcFree_sepConj hFframe hF
  have hcall := k73_mul_call_spec_within
    (cr := wholeCode) (n := 3850)
    (K73 + 84) (GuestAddrs.u256_mul_u64_be : Word) raIn spH
    (spH + signExtend12 (-48 : BitVec 12)) basePtr outPtr target
    (gasUsed - target) (1 : Word) basePtr (gasUsed - target) outPtr outPtr
    (jalOff GuestAddrs.u256_mul_u64_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 84)) Fcall hFcall
    f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
    hcallee'' htarget hmem hcalleeMem
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Fmul, k73IncreaseSetupPost, k73MulPreNoRa] at hp ⊢
      xperm_hyp hp)
    hsetup hcall
  have hseq' := cpsTripleWithin_mono_nSteps (nSteps' := 3856)
    (by omega) hseq
  simp only [k73IncreaseMulPre, k73IncreaseMulPost] at ⊢
  have hseqAddr : cpsTripleWithin 3856 (K73 + 64) (K73 + 88) wholeCode
      (k73HeadPost spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes outBytes Fmul)
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        k73MulBodyPostNoRa (spH + signExtend12 (-48 : BitVec 12))
          (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word)
          basePtr (gasUsed - target) outPtr baseBytes accBytes outBytes **
        Fcall) := by
    simpa only [show (K73 + 84) + 4 = K73 + 88 by bv_omega] using hseq'
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [Fmul] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp [Fcall, Fframe] at hq ⊢
      xperm_hyp hq)
    hseqAddr

def k73MulOverflowCoreNoStatus
    (accBytes : List (BitVec 8)) (k : Nat) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (EvmAsm.Codegen.U256MulU64Be.accBase +
      BitVec.ofNat 64 (32 + k))) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
    regOwn .x28 ** EvmAsm.Rv64.bytesRegion
      EvmAsm.Codegen.U256MulU64Be.accBase accBytes

def k73IncreaseMulCarryRest
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (K73 + 88)) **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
      (gasUsed - target) outPtr baseBytes **
      (fun s => ∃ k, (k73MulEpilogueNoRa
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion outPtr outBytes **
        k73MulOverflowCoreNoStatus accBytes k) s) ** F)

theorem k73_mul_overflow_nonzero_core_factor
    (accBytes : List (BitVec 8)) (k : Nat) : ∀ s,
      EvmAsm.Codegen.U256MulU64Be.overflowNonzeroCore accBytes k s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
        k73MulOverflowCoreNoStatus accBytes k) s := by
  intro s hs
  dsimp [EvmAsm.Codegen.U256MulU64Be.overflowNonzeroCore,
    k73MulOverflowCoreNoStatus] at hs ⊢
  xperm_hyp hs

theorem k73_mul_overflow_zero_core_factor
    (accBytes : List (BitVec 8)) (k : Nat) : ∀ s,
      EvmAsm.Codegen.U256MulU64Be.overflowZeroCore accBytes k s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        k73MulOverflowCoreNoStatus accBytes k) s := by
  intro s hs
  dsimp [EvmAsm.Codegen.U256MulU64Be.overflowZeroCore,
    k73MulOverflowCoreNoStatus] at hs ⊢
  xperm_hyp hs

theorem k73_mul_overflow_status_factor
    (spNew vRa v8 v9 v18 v19 v20 outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) : ∀ s,
      k73MulOverflowNoRa spNew vRa v8 v9 v18 v19 v20 outPtr
        accBytes outBytes s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        (fun s => ∃ k, (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
          bytesRegion outPtr outBytes **
          k73MulOverflowCoreNoStatus accBytes k) s)) s := by
  intro s hs
  dsimp [k73MulOverflowNoRa] at hs
  rcases hs with ⟨k, hk⟩ | hk
  · have hfull := sepConj_mono_right
      (fun h hq => sepConj_mono_right
        (fun h' hq' => k73_mul_overflow_nonzero_core_factor
          accBytes k h' hq') h hq) s hk
    have hraw :
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
          (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
            bytesRegion outPtr outBytes **
            k73MulOverflowCoreNoStatus accBytes k)) s := by
      xperm_hyp hfull
    have hown :
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
            bytesRegion outPtr outBytes **
            k73MulOverflowCoreNoStatus accBytes k)) s := by
      apply sepConj_mono_right
      intro h hq
      exact sepConj_mono_left (regIs_to_regOwn .x10 (1 : Word)) h hq
      exact hraw
    exact sepConj_mono_right (fun h hq => sepConj_mono_right
      (fun _ hrest => ⟨k, hrest⟩) h hq) s hown
  · have hfull := sepConj_mono_right
      (fun h hq => sepConj_mono_right
        (fun h' hq' => k73_mul_overflow_zero_core_factor
          accBytes 8 h' hq') h hq) s hk
    have hraw :
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
          (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
            bytesRegion outPtr outBytes **
            k73MulOverflowCoreNoStatus accBytes 8)) s := by
      xperm_hyp hfull
    have hown :
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (k73MulEpilogueNoRa spNew vRa v8 v9 v18 v19 v20 **
            bytesRegion outPtr outBytes **
            k73MulOverflowCoreNoStatus accBytes 8)) s := by
      apply sepConj_mono_right
      intro h hq
      exact sepConj_mono_left (regIs_to_regOwn .x10 (0 : Word)) h hq
      exact hraw
    exact sepConj_mono_right (fun h hq => sepConj_mono_right
      (fun _ hrest => ⟨8, hrest⟩) h hq) s hown

theorem k73_increase_mul_post_factor
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : ∀ s,
      k73IncreaseMulPost spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes outBytes F s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        (k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F)) s := by
  intro s hs
  dsimp [K73, k73IncreaseMulPost, k73MulBodyPostNoRa,
    k73IncreaseMulCarryRest] at hs ⊢
  have hstatus := k73_mul_overflow_status_factor
    (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
    basePtr outPtr target (gasUsed - target) (1 : Word)
    outPtr accBytes outBytes
  let newOverflow : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
      (fun s => ∃ k, (k73MulEpilogueNoRa
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion outPtr outBytes **
        k73MulOverflowCoreNoStatus accBytes k) s)
  have h_over : ∀ h,
      k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
          (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word)
          outPtr accBytes outBytes h → newOverflow h := by
    intro h hh
    exact hstatus h hh
  have hbody0 : ∀ h,
      (EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
          (gasUsed - target) outPtr baseBytes **
        k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
          (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word)
          outPtr accBytes outBytes) h →
      (EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
          (gasUsed - target) outPtr baseBytes ** newOverflow) h := by
    intro h hh
    exact sepConj_mono_right h_over h hh
  have hbody : ∀ h,
      ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
          (gasUsed - target) outPtr baseBytes **
        k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
          (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word)
          outPtr accBytes outBytes) ** F) h →
      ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
          (gasUsed - target) outPtr baseBytes ** newOverflow) ** F) h := by
    intro h hh
    exact sepConj_mono_left hbody0 h hh
  have hframe : ∀ h,
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
            (gasUsed - target) outPtr baseBytes **
          k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
            (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word)
            outPtr accBytes outBytes) ** F)) h →
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
            (gasUsed - target) outPtr baseBytes ** newOverflow) ** F)) h := by
    intro h hh
    exact sepConj_mono_right hbody h hh
  have houter : ∀ h,
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
            (gasUsed - target) outPtr baseBytes **
          k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
            (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word)
            outPtr accBytes outBytes) ** F)) h →
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
            (gasUsed - target) outPtr baseBytes ** newOverflow) ** F)) h := by
    intro h hh
    exact sepConj_mono_right hframe h hh
  have hmapped := houter s (by simpa [K73] using hs)
  dsimp [newOverflow] at hmapped ⊢
  xperm_hyp hmapped

/-! The multiply's status is tested immediately at `+88`.  Both outcomes
    retain the carry relation; only the continuation PC differs. -/
theorem k73_increase_status_branch_spec_within
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) :
    cpsBranchWithin 1 (K73 + 88) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F ** regOwn .x10)
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes outBytes F ** regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes outBytes F ** regOwn .x10) := by
  let Rest : Assertion :=
    k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes outBytes F
  have hRest : Rest.pcFree := by
    have hExists : Assertion.pcFree (fun s => ∃ k, (k73MulEpilogueNoRa
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion outPtr outBytes **
        k73MulOverflowCoreNoStatus accBytes k) s) := by
      apply pcFree_exists
      intro k
      pcf
    dsimp [Rest, k73IncreaseMulCarryRest]
    pcf
    exact hExists
    exact hF
  have hraw : ∀ old10, cpsBranchWithin 1 (K73 + 88) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) **
        ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 272) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 92) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10) := by
    intro old10
    have hbne := bne_spec_gen_within .x10 .x0 (184 : BitVec 13)
      old10 (0 : Word) (K73 + 88)
    have hbneC := cpsBranchWithin_extend_code
      (k73_whole_mem 22 _ (K73 + 88) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hbne
    have hbneF := cpsBranchWithin_frameR Rest hRest hbneC
    refine cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) (fun h hq => ?_) hbneF
    · have hq1 := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
      drop_pure hq1
      dsimp [Rest] at hq1 ⊢
      xperm_hyp hq1
    · have hq1 := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
      drop_pure hq1
      dsimp [Rest] at hq1 ⊢
      xperm_hyp hq1
  have hbr := cpsBranchWithin_of_forall_regIs_to_regOwn
    (r := .x10) (P := ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) hraw
  dsimp [Rest] at hbr ⊢
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) (fun _ hq => by xperm_hyp hq) hbr

def k73IncreaseDivPairFrame
    (spH gasUsed basePtr outPtr target : Word)
    (baseBytes accBytes : List (BitVec 8)) (G : Assertion) (k : Nat) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spH) **
    ((.x8 : Reg) ↦ᵣ basePtr) **
    ((.x19 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
    frameSlotsSaved k73Frame spH (k73Saved (K73 + 88) basePtr outPtr
      target (gasUsed - target) (1 : Word)) **
    bytesRegion basePtr baseBytes **
    bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
    k73MulOverflowCoreNoStatus accBytes k ** G

def k73IncreaseDivPairPre
    (spH gasUsed basePtr outPtr target : Word)
    (baseBytes accBytes outBytes : List (BitVec 8))
    (G : Assertion) (k : Nat) : Assertion :=
  (((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x18 : Reg) ↦ᵣ target) **
    ((.x11 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
    regOwns u256DivU64BeScratch **
    bytesRegion outPtr outBytes **
    k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
      baseBytes accBytes G k) ** regOwn .x10

def k73IncreaseDivPairPost
    (spH gasUsed basePtr outPtr target : Word)
    (baseBytes accBytes outBytes : List (BitVec 8))
    (G : Assertion) (k : Nat) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x18 : Reg) ↦ᵣ target) **
    ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
      (u256DivU64BeQuotBytes outBytes outBytes target)
      (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
    ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
    regOwns u256DivU64BeScratch **
    bytesRegion outPtr (u256DivU64BeQuotBytes
      (u256DivU64BeQuotBytes outBytes outBytes target)
      (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
    k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
      baseBytes accBytes G k

/-! The in-place increase divider is applied to each concrete overflow-core
    branch.  The public continuation keeps the existential carry index while
    exposing the exact divider post needed by the next status test. -/
theorem k73_increase_div_pair_spec_within
    (spH gasUsed basePtr outPtr target : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (htargetBound : target.toNat ≤ 2 ^ 56)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4) :
    cpsTripleWithin
      (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps)
      (K73 + 92) (K73 + 124) wholeCode
      (fun s => ∃ k, k73IncreaseDivPairPre spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k s)
      (fun s => ∃ k, k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k s) := by
  have hframe : ∀ k, (k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
      baseBytes accBytes G k).pcFree := by
    intro k
    dsimp [k73IncreaseDivPairFrame]
    pcf
    exact hG
  have hpairOwn : ∀ k, cpsTripleWithin
      (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps)
      (K73 + 92) (K73 + 124) wholeCode
      (k73IncreaseDivPairPre spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k)
      (k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k) := by
    intro k
    have hown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
        (P := ((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x18 : Reg) ↦ᵣ target) **
          ((.x11 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256DivU64BeScratch ** bytesRegion outPtr outBytes **
          k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
            baseBytes accBytes G k)
        (Q := k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
          baseBytes accBytes outBytes G k) (fun old10 => by
          have hpairRaw : cpsTripleWithin
              (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
                (u256DivU64BeInPlaceFn outPtr 8
                  (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps)
              (K73 + 92) (K73 + 124) wholeCode
              (((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
                ((.x18 : Reg) ↦ᵣ target) ** ((.x10 : Reg) ↦ᵣ old10) **
                ((.x11 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                regOwns u256DivU64BeScratch ** bytesRegion outPtr outBytes **
                k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                  baseBytes accBytes G k)
              (k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
                baseBytes accBytes outBytes G k) := by
            have hpair0 := k73_in_place_div_pair_spec_within
              outPtr target (K73 + 88) old10 (gasUsed - target) outPtr outBytes
              empAssertion (by pcf) hrw hlenOut hoverOut
              htargetPos htargetBound hsz1 hsz2 hret1 hret2
            have hpairF := cpsTripleWithin_frameR
              (k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                baseBytes accBytes G k) (hframe k) hpair0
            have hpairFW := cpsTripleWithin_extend_code full_whole_mono hpairF
            have hpairFW0 := cpsTripleWithin_weaken
              (P := (((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
                ((.x18 : Reg) ↦ᵣ target) ** ((.x10 : Reg) ↦ᵣ old10) **
                ((.x11 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                regOwns u256DivU64BeScratch ** bytesRegion outPtr outBytes **
                empAssertion) **
                k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                  baseBytes accBytes G k)
              (P' := (((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
                ((.x18 : Reg) ↦ᵣ target) ** ((.x10 : Reg) ↦ᵣ old10) **
                ((.x11 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                regOwns u256DivU64BeScratch ** bytesRegion outPtr outBytes) **
                k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                  baseBytes accBytes G k)
              (Q := (((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
                ((.x18 : Reg) ↦ᵣ target) **
                ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
                  (u256DivU64BeQuotBytes outBytes outBytes target)
                  (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
                ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                regOwns u256DivU64BeScratch ** bytesRegion outPtr
                  (u256DivU64BeQuotBytes
                    (u256DivU64BeQuotBytes outBytes outBytes target)
                    (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
                empAssertion) **
                k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                  baseBytes accBytes G k)
              (Q' := (((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
                ((.x18 : Reg) ↦ᵣ target) **
                ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
                  (u256DivU64BeQuotBytes outBytes outBytes target)
                  (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
                ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                regOwns u256DivU64BeScratch ** bytesRegion outPtr
                  (u256DivU64BeQuotBytes
                    (u256DivU64BeQuotBytes outBytes outBytes target)
                    (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
                k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                  baseBytes accBytes G k)
              (fun _ hp => by simpa only [sepConj_emp_right'] using hp)
              (fun _ hq => by simpa only [sepConj_emp_right'] using hq) hpairFW
            have hpairFW1 := cpsTripleWithin_weaken
              (P' := (((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
                ((.x18 : Reg) ↦ᵣ target) ** ((.x10 : Reg) ↦ᵣ old10) **
                ((.x11 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                regOwns u256DivU64BeScratch ** bytesRegion outPtr outBytes **
                k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                  baseBytes accBytes G k))
              (Q' := k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
                baseBytes accBytes outBytes G k)
              (fun _ hp => by simpa only [sepConj_assoc'] using hp)
              (fun _ hq => by
                simpa only [k73IncreaseDivPairPost, sepConj_assoc'] using hq) hpairFW0
            exact hpairFW1
          exact cpsTripleWithin_weaken
            (P := ((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
              ((.x18 : Reg) ↦ᵣ target) ** ((.x10 : Reg) ↦ᵣ old10) **
              ((.x11 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
              regOwns u256DivU64BeScratch ** bytesRegion outPtr outBytes **
              k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                baseBytes accBytes G k)
            (P' := (((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
              ((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ (gasUsed - target)) **
              ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
              bytesRegion outPtr outBytes **
              k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
                baseBytes accBytes G k) ** (.x10 ↦ᵣ old10))
            (Q := k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
              baseBytes accBytes outBytes G k)
            (Q' := k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
              baseBytes accBytes outBytes G k)
            (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) hpairRaw)
    simpa only [k73IncreaseDivPairPre] using hown
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (P := fun k => k73IncreaseDivPairPre spH gasUsed basePtr outPtr target
      baseBytes accBytes outBytes G k)
    (Q := fun s => ∃ k, k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
      baseBytes accBytes outBytes G k s) ?_
  intro k
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ⟨k, hq⟩)
    (hpairOwn k)

/-! The increase route's first post-division test is a linked call to
    `u256_is_zero`.  The divider owns the exposed scratch registers, so this
    adapter deliberately peels that ownership to arbitrary concrete values
    for the callee and re-owns the complete scratch set afterwards. -/
theorem k73_increase_is_zero_call_spec_within
    (ptr oldRa : Word) (w0 w1 w2 w3 : Word) (F : Assertion)
    (hF : F.pcFree) :
    ∀ old10, cpsTripleWithin 11 (K73 + 128) (K73 + 136) wholeCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) := by
  intro old10
  let tail : List Reg :=
    [.x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]
  have htail : ∀ vf : Reg → Word,
      regAtomsOf vf u256DivU64BeScratch =
        (((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
          ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
          regAtomsOf vf tail) := by
    intro vf
    simp only [u256DivU64BeScratch, tail, regAtomsOf_cons, regAtomsOf_nil]
  have hmvAny : cpsTripleWithin 1 (K73 + 128) (K73 + 132) wholeCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
      (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) := by
    have hmv := mv_spec_gen_within .x10 .x9 ptr old10 (K73 + 128) (by decide)
    have hmvC := cpsTripleWithin_extend_code
      (k73_whole_mem 32 _ (K73 + 128) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hmv
    have hR : (((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F).pcFree := by
      pcf
      exact hF
    have hmvF := cpsTripleWithin_frameR _ hR hmvC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hmvF
  have htarget :
      (K73 + 132) + signExtend21
        (jalOff GuestAddrs.u256_is_zero
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 132)) =
        (GuestAddrs.u256_is_zero : Word) := by
    change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 132 + _ = BitVec.ofNat 64 GuestAddrs.u256_is_zero
    exact jalOff_correct_add GuestAddrs.u256_is_zero
      GuestAddrs.eip1559_calc_base_fee_per_gas 132
      (by decide) (by decide) (by decide) (by decide)
  have hmem : ∀ a i, CodeReq.singleton (K73 + 132)
      (.JAL .x1 (jalOff GuestAddrs.u256_is_zero
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 132))) a = some i →
      wholeCode a = some i := by
    intro a i hi
    exact k73_whole_mem 33 _ (K73 + 132) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi
  have hcallAny : ∀ vf : Reg → Word,
      cpsTripleWithin 10 (K73 + 132) (K73 + 136) wholeCode
      (((((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regAtomsOf vf u256DivU64BeScratch))
      (((((.x1 : Reg) ↦ᵣ (K73 + 136)) ** regOwn .x10 **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regOwns u256DivU64BeScratch)) := by
    intro vf
    have hzero := u256IsZeroFlat_spec_domain ptr (K73 + 136)
      (vf .x5) (vf .x6) (vf .x7) (vf .x28) w0 w1 w2 w3
    have hzeroC := cpsTripleWithin_extend_code isZero_whole_mono hzero
    have hP0 : (((.x10 : Reg) ↦ᵣ ptr) **
        ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
        ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3))).pcFree := by
      pcf
    have hcallee0 : cpsTripleWithin 9 (GuestAddrs.u256_is_zero : Word)
        (K73 + 136) wholeCode
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x10 : Reg) ↦ᵣ ptr) **
          ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
          ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)))
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
          ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
            (1 : Word) else 0)) **
          ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
          ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
          ((.x28 : Reg) ↦ᵣ w3) **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3))) := by
      exact cpsTripleWithin_weaken
        (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) hzeroC
    have hcall0 := callWithin_spec
      (cr := wholeCode)
      (P := ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
        ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)))
      (Q := ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
          (1 : Word) else 0)) **
        ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
        ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
        ((.x28 : Reg) ↦ᵣ w3) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)))
      (K73 + 132) (GuestAddrs.u256_is_zero : Word) oldRa
      (jalOff GuestAddrs.u256_is_zero
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 132)) 9 htarget hmem hP0 hcallee0
    have hcallF := cpsTripleWithin_frameR
      (regAtomsOf vf tail ** F) (by dsimp [tail]; pcf; exact hF) hcall0
    have hcall : cpsTripleWithin 10 (K73 + 132) (K73 + 136) wholeCode
        (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
          ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
          ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
          regAtomsOf vf tail **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
          ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
            (1 : Word) else 0)) **
          ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
          ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
          ((.x28 : Reg) ↦ᵣ w3) ** regAtomsOf vf tail **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) := by
      simpa only [show 1 + 9 = 10 by decide, sepConj_assoc', sepConj_comm',
        sepConj_left_comm',
        show (K73 + 132) + 4 = K73 + 136 by bv_omega] using hcallF
    have hownChain : ∀ v10 v5 v6 v7 v28 : Word, ∀ s,
        (((.x10 : Reg) ↦ᵣ v10) ** ((.x5 : Reg) ↦ᵣ v5) **
          ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
          ((.x28 : Reg) ↦ᵣ v28) ** regAtomsOf vf tail **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) s →
        (regOwn .x10 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwns tail **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) s := by
      intro v10 v5 v6 v7 v28 s hs
      exact sepConj_mono (regIs_implies_regOwn .x10)
        (sepConj_mono (regIs_implies_regOwn .x5)
          (sepConj_mono (regIs_implies_regOwn .x6)
            (sepConj_mono (regIs_implies_regOwn .x7)
              (sepConj_mono (regIs_implies_regOwn .x28)
                (sepConj_mono (fun s h => regAtomsOf_to_regOwns vf tail s h)
                  (fun _ h => h)))))) s hs
    have hcall' := cpsTripleWithin_weaken
      (P' := (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regAtomsOf vf u256DivU64BeScratch)
      (Q' := (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** regOwn .x10 **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regOwns u256DivU64BeScratch)
      (fun _ hp => by
        rw [htail vf] at hp
        xperm_hyp hp)
      (fun s hq => by
        have hq0 :
            (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
              ((.x10 : Reg) ↦ᵣ
                (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
                  (1 : Word) else 0)) **
              ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
              ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
              ((.x28 : Reg) ↦ᵣ w3) ** regAtomsOf vf tail **
              ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
              ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) s := by
          xperm_hyp hq
        have hq1 := sepConj_mono_right
          (hownChain (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
            (1 : Word) else 0) (w0 ||| w1 ||| w2 ||| w3) w1 w2 w3) _ hq0
        simp only [tail, u256DivU64BeScratch, regOwns] at hq1 ⊢
        xperm_hyp hq1) hcall
    exact hcall'
  have hcallOwn := cpsTripleWithin_peel_regOwns u256DivU64BeScratch (by decide)
    (P := ((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
      ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
        ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
    (Q := ((((.x1 : Reg) ↦ᵣ (K73 + 136)) ** regOwn .x10 **
      ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
        ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
      regOwns u256DivU64BeScratch)) hcallAny
  have hcallFramed := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr)) (by pcf) hcallOwn
  have hcallFramed' := cpsTripleWithin_weaken
    (P' := (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
        ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F))
    (Q' := (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
        ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F))
    (fun _ hp => by
      simp only [u256DivU64BeScratch, regOwns] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [u256DivU64BeScratch, regOwns] at hq ⊢
      xperm_hyp hq) hcallFramed
  have hseq := cpsTripleWithin_seq_same_cr hmvAny hcallFramed'
  exact hseq

/-! Both overflow arms converge on the same `li x10,1` plus epilogue tail.
    Keeping this adapter separate lets arithmetic-call posts retain their own
    status/overflow relation while the caller frame is restored uniformly. -/
theorem k73_failure_tail_spec_within
    (sp0 spH raIn : Word) (saved : Reg → Word) (P : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : saved .x1 = raIn) (hP : P.pcFree) :
    cpsTripleWithin 9 (K73 + 272) raIn wholeCode
      ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** P)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 1) ** P) := by
  let Rest : Assertion :=
    (.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved ** P
  have hRest : Rest.pcFree := by
    dsimp [Rest]
    exact pcFree_sepConj (pcFree_regIs (r := .x2) (v := spH))
      (pcFree_sepConj (pcFree_regsOwnAt k73Frame)
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hP))
  have hliAny : ∀ old10, cpsTripleWithin 1 (K73 + 272) (K73 + 276)
      wholeCode (Rest ** (.x10 ↦ᵣ old10))
      (Rest ** (.x10 ↦ᵣ (1 : Word))) := by
    intro old10
    have hli := li_spec_gen_within .x10 old10 (1 : Word) (K73 + 272)
      (by decide)
    have hliC := cpsTripleWithin_extend_code
      (k73_whole_mem 68 _ (K73 + 272) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hli
    have hliF := cpsTripleWithin_frameR Rest hRest hliC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have hli' := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
    (P := Rest) (Q := Rest ** (.x10 ↦ᵣ (1 : Word))) hliAny
  let P1 : Assertion := (.x10 ↦ᵣ (1 : Word)) ** P
  have hP1 : P1.pcFree := by
    dsimp [P1]
    exact pcFree_sepConj (pcFree_regIs (r := .x10) (v := 1)) hP
  have hepi := k73_epilogue_spec_within sp0 spH raIn saved P1
    hsp hret hsaved hP1
  have hepi' : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 1) ** P))
      (((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 1) ** P)) := by
    dsimp [P1] at hepi ⊢
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hepi
  have hepi'' : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      (Rest ** (.x10 ↦ᵣ (1 : Word)))
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 1) ** P) := by
    simpa [Rest, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hepi'
  have hseq := cpsTripleWithin_seq_same_cr hli' hepi''
  dsimp [Rest] at hseq ⊢
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hseq

/-! The successful increase arm has the analogous `li x10,0` plus a jump over
    the failure arm before entering the shared epilogue. -/
theorem k73_success_tail_spec_within
    (sp0 spH raIn : Word) (saved : Reg → Word) (P : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : saved .x1 = raIn) (hP : P.pcFree) :
    cpsTripleWithin 10 (K73 + 196) raIn wholeCode
      ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** P)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 0) ** P) := by
  let Rest : Assertion :=
    (.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved ** P
  have hRest : Rest.pcFree := by
    dsimp [Rest]
    exact pcFree_sepConj (pcFree_regIs (r := .x2) (v := spH))
      (pcFree_sepConj (pcFree_regsOwnAt k73Frame)
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hP))
  have hliAny : ∀ old10, cpsTripleWithin 1 (K73 + 196) (K73 + 200)
      wholeCode (Rest ** (.x10 ↦ᵣ old10))
      (Rest ** (.x10 ↦ᵣ (0 : Word))) := by
    intro old10
    have hli := li_spec_gen_within .x10 old10 (0 : Word) (K73 + 196)
      (by decide)
    have hliC := cpsTripleWithin_extend_code
      (k73_whole_mem 49 _ (K73 + 196) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hli
    have hliF := cpsTripleWithin_frameR Rest hRest hliC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have hli' := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
    (P := Rest) (Q := Rest ** (.x10 ↦ᵣ (0 : Word))) hliAny
  have hj := jal_x0_spec_gen_within (76 : BitVec 21) (K73 + 200)
  rw [show (K73 + 200) + signExtend21 (76 : BitVec 21) = K73 + 276 by
    rw [show signExtend21 (76 : BitVec 21) = (76 : Word) from by decide]
    bv_omega] at hj
  have hjC := cpsTripleWithin_extend_code
    (k73_whole_mem 50 _ (K73 + 200) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hj
  let P0 : Assertion := (.x10 ↦ᵣ (0 : Word)) ** P
  have hP0 : P0.pcFree := by
    dsimp [P0]
    exact pcFree_sepConj (pcFree_regIs (r := .x10) (v := 0)) hP
  have hjF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved) ** P0)
    (by dsimp [P0]; pcf; exact hP) hjC
  have hjump : cpsTripleWithin 1 (K73 + 200) (K73 + 276) wholeCode
      (Rest ** (.x10 ↦ᵣ (0 : Word)))
      (Rest ** (.x10 ↦ᵣ (0 : Word))) := by
    simpa [Rest, P0, sepConj_assoc', sepConj_comm', sepConj_left_comm',
      sepConj_emp_left', sepConj_emp_right'] using hjF
  have hepi := k73_epilogue_spec_within sp0 spH raIn saved P0
    hsp hret hsaved hP0
  have hepi' : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      (Rest ** (.x10 ↦ᵣ (0 : Word)))
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 0) ** P) := by
    simpa [Rest, P0, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hepi
  have hseq := cpsTripleWithin_seq_same_cr hli' hjump
  have hseq' := cpsTripleWithin_seq_same_cr hseq hepi'
  dsimp [Rest] at hseq' ⊢
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hseq'

end EvmAsm.Codegen.HeaderBaseFeeSpec
