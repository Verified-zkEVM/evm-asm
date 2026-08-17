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
