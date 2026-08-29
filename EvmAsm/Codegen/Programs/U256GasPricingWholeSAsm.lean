/-
  EvmAsm.Codegen.Programs.U256GasPricingWholeSAsm

  Stage 2 of the EIP-1559 priority-fee helper (#13068): the frame
  prologue and epilogue composed with the Stage-1 body triple into the
  entry-anchored whole-routine contract
  `priority_fee_per_gas_eip1559_spec`.  Split from
  `U256GasPricingSAsm.lean` (file-size guardrail).
-/

import EvmAsm.Codegen.Programs.U256GasPricingSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.U256MinSAsm
open EvmAsm.Codegen.U256SubBeSAsm

namespace U256GasPricingSAsm

/-! ## Stage 2 (#13068): the entry-anchored whole-routine triple

    The body triple above starts at `P + 24` (after the frame prologue)
    and ends at `P + 88` (before the epilogue).  This section proves the
    six-instruction prologue and the seven-instruction epilogue and
    seq-composes all three into the whole-routine contract at `P`. -/

private theorem cps_fuel_mono' {n m : Nat} {entry exit_ : Word}
    {cr : CodeReq} {Pa Q : Assertion} (hnm : n ≤ m)
    (h : cpsTripleWithin n entry exit_ cr Pa Q) :
    cpsTripleWithin m entry exit_ cr Pa Q := by
  intro R hR s hcr hp hpc
  obtain ⟨k, hk, rest⟩ := h R hR s hcr hp hpc
  exact ⟨k, Nat.le_trans hk hnm, rest⟩

/-- Disjunctive-precondition elimination: a triple from `A ∨ B` follows
    from a triple on each disjunct (same post). -/
private theorem cps_or_pre {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {A B Q : Assertion}
    (h1 : cpsTripleWithin n entry exit_ cr A Q)
    (h2 : cpsTripleWithin n entry exit_ cr B Q) :
    cpsTripleWithin n entry exit_ cr (fun h => A h ∨ B h) Q := by
  intro R hR s hcr hp hpc
  obtain ⟨hps, hcompat, ha, hb, hd, hu, hab, hr⟩ := hp
  cases hab with
  | inl hA => exact h1 R hR s hcr ⟨hps, hcompat, ha, hb, hd, hu, hA, hr⟩ hpc
  | inr hB => exact h2 R hR s hcr ⟨hps, hcompat, ha, hb, hd, hu, hB, hr⟩ hpc

set_option maxRecDepth 8000 in
/-- The frame prologue (`addi sp, sp, -48` and the five saves). -/
private theorem priority_prologue_spec
    (sp0 ret v8 v9 v18 v19 m0 m1 m2 m3 m4 : Word) :
    cpsTripleWithin 6 P (P + 24) fullCode
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ m3) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ m4))
      (((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        ((.x1 : Reg) ↦ᵣ ret) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ ret) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ v8) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ v9) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ v18) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ v19)) := by
  set nsp := sp0 + signExtend12 (-48 : BitVec 12) with hnsp
  have haddisp := addi_spec_gen_same_within .x2 sp0 (-48 : BitVec 12)
    P (by decide)
  rw [← hnsp] at haddisp
  have haddispc := cpsTripleWithin_extend_code
    (priority_mem 0 _ P (by decide) (by decide) (by rfl)) haddisp
  have hsd1 := sd_spec_gen_within .x2 .x1 nsp ret m0 (0 : BitVec 12) (P + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show nsp + (0 : Word) = nsp from by bv_omega] at hsd1
  have hsd1c := cpsTripleWithin_extend_code
    (priority_mem 1 _ (P + 4) (by decide) (by decide) (by rfl)) hsd1
  have hsd2 := sd_spec_gen_within .x2 .x8 nsp v8 m1 (8 : BitVec 12) (P + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hsd2
  have hsd2c := cpsTripleWithin_extend_code
    (priority_mem 2 _ (P + 8) (by decide) (by decide) (by rfl)) hsd2
  have hsd3 := sd_spec_gen_within .x2 .x9 nsp v9 m2 (16 : BitVec 12) (P + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hsd3
  have hsd3c := cpsTripleWithin_extend_code
    (priority_mem 3 _ (P + 12) (by decide) (by decide) (by rfl)) hsd3
  have hsd4 := sd_spec_gen_within .x2 .x18 nsp v18 m3 (24 : BitVec 12) (P + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at hsd4
  have hsd4c := cpsTripleWithin_extend_code
    (priority_mem 4 _ (P + 16) (by decide) (by decide) (by rfl)) hsd4
  have hsd5 := sd_spec_gen_within .x2 .x19 nsp v19 m4 (32 : BitVec 12) (P + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at hsd5
  have hsd5c := cpsTripleWithin_extend_code
    (priority_mem 5 _ (P + 20) (by decide) (by decide) (by rfl)) hsd5
  runBlock haddispc hsd1c hsd2c hsd3c hsd4c hsd5c

set_option maxRecDepth 8000 in
/-- The epilogue (five restores, `addi sp, sp, 48`, `jalr x0, 0(ra)`),
    entered with `ra` merely owned (both status arms leave different
    link values) and the frame slots holding the saved registers. -/
private theorem priority_epilogue_spec
    (nsp sp0 ret v8 v9 v18 v19 p8 p9 p18 p19 : Word)
    (hnsp48 : nsp + (48 : Word) = sp0) :
    cpsTripleWithin 7 (P + 88) (ret &&& ~~~1) fullCode
      (regOwn .x1 ** ((.x2 : Reg) ↦ᵣ nsp) **
        (.x8 ↦ᵣ p8) ** (.x9 ↦ᵣ p9) ** (.x18 ↦ᵣ p18) ** (.x19 ↦ᵣ p19) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19))
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19)) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := ((.x2 : Reg) ↦ᵣ nsp) **
        (.x8 ↦ᵣ p8) ** (.x9 ↦ᵣ p9) ** (.x18 ↦ᵣ p18) ** (.x19 ↦ᵣ p19) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19))
      (fun v1 => ?_))
  have hld1 := ld_spec_gen_within .x1 .x2 nsp v1 ret (0 : BitVec 12)
    (P + 88) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show nsp + (0 : Word) = nsp from by bv_omega] at hld1
  have hld1c := cpsTripleWithin_extend_code
    (priority_mem 22 _ (P + 88) (by decide) (by decide) (by rfl)) hld1
  have hld8 := ld_spec_gen_within .x8 .x2 nsp p8 v8 (8 : BitVec 12)
    (P + 92) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hld8
  have hld8c := cpsTripleWithin_extend_code
    (priority_mem 23 _ (P + 92) (by decide) (by decide) (by rfl)) hld8
  have hld9 := ld_spec_gen_within .x9 .x2 nsp p9 v9 (16 : BitVec 12)
    (P + 96) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hld9
  have hld9c := cpsTripleWithin_extend_code
    (priority_mem 24 _ (P + 96) (by decide) (by decide) (by rfl)) hld9
  have hld18 := ld_spec_gen_within .x18 .x2 nsp p18 v18 (24 : BitVec 12)
    (P + 100) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at hld18
  have hld18c := cpsTripleWithin_extend_code
    (priority_mem 25 _ (P + 100) (by decide) (by decide) (by rfl)) hld18
  have hld19 := ld_spec_gen_within .x19 .x2 nsp p19 v19 (32 : BitVec 12)
    (P + 104) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at hld19
  have hld19c := cpsTripleWithin_extend_code
    (priority_mem 26 _ (P + 104) (by decide) (by decide) (by rfl)) hld19
  have haddsp := addi_spec_gen_same_within .x2 nsp (48 : BitVec 12)
    (P + 108) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide,
      hnsp48] at haddsp
  have haddspc := cpsTripleWithin_extend_code
    (priority_mem 27 _ (P + 108) (by decide) (by decide) (by rfl)) haddsp
  have hjalr := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (P + 112)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (ret + 0 : Word) = ret from by bv_omega] at hjalr
  have hjalrc := cpsTripleWithin_extend_code
    (priority_mem 28 _ (P + 112) (by decide) (by decide) (by rfl)) hjalr
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (?_ : cpsTripleWithin 7 (P + 88) (ret &&& ~~~1) fullCode
      (((.x2 : Reg) ↦ᵣ nsp) ** ((.x1 : Reg) ↦ᵣ v1) **
        (.x8 ↦ᵣ p8) ** (.x9 ↦ᵣ p9) ** (.x18 ↦ᵣ p18) ** (.x19 ↦ᵣ p19) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19))
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19)))
  runBlock hld1c hld8c hld9c hld18c hld19c haddspc hjalrc

/-- Distribute a disjunctive left conjunct out of a `sepConj`. -/
private theorem sepConj_or_distrib {A B X : Assertion} :
    ∀ h, ((fun h' => A h' ∨ B h') ** X) h → ((A ** X) h ∨ (B ** X) h) := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, hab, hx⟩ := hp
  cases hab with
  | inl ha => exact Or.inl ⟨h1, h2, hd, hu, ha, hx⟩
  | inr hb => exact Or.inr ⟨h1, h2, hd, hu, hb, hx⟩

/-- The success arm of the whole-routine contract: `a0 = 0`, the output
    buffer holds `min(priority, surplus)` in big-endian, callee-saved
    registers and `sp` restored, the five frame slots holding the saved
    entry values. -/
def priorityWholeSuccessPost
    (sp0 ret v8 v9 v18 v19 pPtr fPtr bPtr outPtr : Word)
    (pBytes fBytes bBytes subBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
    (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
    (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat subBytes
      then pPtr else outPtr)) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x31 ↦ᵣ (32 : Word)) ** regOwn .x13 **
    regOwns prioritySubResidualScratch ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion pPtr pBytes **
    bytesRegion outPtr (if beBytesToNat pBytes ≤ beBytesToNat subBytes
      then pBytes else subBytes) **
    bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes **
    ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ ret) **
    ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ v8) **
    ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ v9) **
    ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ v18) **
    ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ v19) ** F

/-- The reject arm of the whole-routine contract: `a0 = 1` (the
    subtraction borrowed — `max_fee < base_fee`), the output buffer holds
    the raw wrapped difference, callee-saved registers and `sp`
    restored. -/
def priorityWholeFailurePost
    (status sp0 ret v8 v9 v18 v19 pPtr fPtr bPtr outPtr : Word)
    (pBytes fBytes bBytes subBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
    (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
    ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ⌜status ≠ 0⌝ **
    regOwns prioritySubRetScratch ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion pPtr pBytes ** bytesRegion outPtr subBytes **
    bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes **
    ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ ret) **
    ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ v8) **
    ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ v9) **
    ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ v18) **
    ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ v19) ** F

set_option maxRecDepth 8000 in
/-- ⭐ **The whole-routine contract of `priority_fee_per_gas_eip1559` at
    its guest entry** (#13068, Stage 2): entered with the four pointer
    arguments in `a0..a3`, five owned frame dwords below `sp`, and an
    aligned return address, it returns to `ret` with `sp`/`ra` and the
    four callee-saved registers restored, and either `a0 = 0` with
    `min(priority, max_fee - base_fee)` written to `*out`, or `a0 = 1`
    (the subtraction borrowed: `max_fee < base_fee`, reject the tx). -/
theorem priority_fee_per_gas_eip1559_spec
    (sp0 ret v8 v9 v18 v19 m0 m1 m2 m3 m4 : Word)
    (pPtr fPtr bPtr outPtr : Word)
    (pBytes fBytes bBytes outBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroF : Region.wf ⟨fPtr, fBytes⟩)
    (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenP : pBytes.length = 32)
    (hlenF : fBytes.length = 32)
    (hlenB : bBytes.length = 32)
    (hlenOut : outBytes.length = 32)
    (halignP : pPtr.toNat % 8 = 0)
    (halignOut : outPtr.toNat % 8 = 0)
    (hovP : pPtr.toNat + 32 < 2 ^ 64)
    (hovF : fPtr.toNat + 32 < 2 ^ 64)
    (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisjF : fPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ fPtr.toNat)
    (hdisjB : bPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ bPtr.toNat)
    (hvalidP : ∀ k, k < 32 →
      isValidByteAccess (pPtr + BitVec.ofNat 64 k) = true)
    (hvalidOut : ∀ k, k < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hsz : 4 * ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.size + 1)
      ≤ 2 ^ 64) :
    cpsTripleWithin
      (337 + (prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.steps)
      P (ret &&& ~~~1) fullCode
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ fPtr) ** (.x12 ↦ᵣ bPtr) **
        (.x13 ↦ᵣ outPtr) ** regOwns prioritySetupScratch **
        (.x0 ↦ᵣ (0 : Word)) **
        ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ m3) **
        ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ m4) **
        bytesRegion pPtr pBytes ** bytesRegion fPtr fBytes **
        bytesRegion bPtr bBytes ** bytesRegion outPtr outBytes ** F)
      (fun h =>
        priorityWholeSuccessPost sp0 ret v8 v9 v18 v19 pPtr fPtr bPtr outPtr
          pBytes fBytes bBytes (u256SubBeBytes fBytes bBytes outBytes) F h ∨
        priorityWholeFailurePost (u256SubBeBorrow fBytes bBytes outBytes)
          sp0 ret v8 v9 v18 v19 pPtr fPtr bPtr outPtr
          pBytes fBytes bBytes (u256SubBeBytes fBytes bBytes outBytes) F h) := by
  set nsp := sp0 + signExtend12 (-48 : BitVec 12) with hnsp
  set subBytes := u256SubBeBytes fBytes bBytes outBytes with hsubBytes
  set status := u256SubBeBorrow fBytes bBytes outBytes with hstatus
  have hnsp48 : nsp + (48 : Word) = sp0 := by
    rw [hnsp, show signExtend12 (-48 : BitVec 12)
      = (0xFFFFFFFFFFFFFFD0 : Word) from by decide]
    bv_omega
  -- prologue, framed with everything it does not touch
  have hProl := priority_prologue_spec sp0 ret v8 v9 v18 v19 m0 m1 m2 m3 m4
  rw [← hnsp] at hProl
  have hProlF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ fPtr) ** (.x12 ↦ᵣ bPtr) **
      (.x13 ↦ᵣ outPtr) ** regOwns prioritySetupScratch **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion pPtr pBytes ** bytesRegion fPtr fBytes **
      bytesRegion bPtr bBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) hProl
  -- body, framed with `sp` and the five slots
  have hBody := priority_fee_per_gas_eip1559_body_spec ret pPtr fPtr bPtr
    outPtr v8 v9 v18 v19 pBytes fBytes bBytes outBytes F hF hrw hroF hroB
    hlenP hlenF hlenB hlenOut halignP halignOut hovP hovF hovB hovOut
    hdisjF hdisjB hvalidP hvalidOut hsz (by decide)
  have hBodyF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
      ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19))
    (by pcf) hBody
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hProlF hBodyF
    intro h hp; xperm_hyp hp
  -- the epilogue, once per status arm
  have hEpiS := priority_epilogue_spec nsp sp0 ret v8 v9 v18 v19
    pPtr fPtr bPtr outPtr hnsp48
  have hEpiSF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat subBytes
        then pPtr else outPtr)) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x31 ↦ᵣ (32 : Word)) ** regOwn .x13 **
      regOwns prioritySubResidualScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion pPtr pBytes **
      bytesRegion outPtr (if beBytesToNat pBytes ≤ beBytesToNat subBytes
        then pBytes else subBytes) **
      bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes ** F)
    (by pcf; exact hF) hEpiS
  have hEpiFa := priority_epilogue_spec nsp sp0 ret v8 v9 v18 v19
    pPtr fPtr bPtr outPtr hnsp48
  have hEpiFaF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ⌜status ≠ 0⌝ **
      regOwns prioritySubRetScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion pPtr pBytes ** bytesRegion outPtr subBytes **
      bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes ** F)
    (by pcf; exact hF) hEpiFa
  -- the whole-routine post (the goal's disjunction)
  set WholeQ : Assertion := fun h =>
    priorityWholeSuccessPost sp0 ret v8 v9 v18 v19 pPtr fPtr bPtr outPtr
      pBytes fBytes bBytes subBytes F h ∨
    priorityWholeFailurePost status sp0 ret v8 v9 v18 v19 pPtr fPtr bPtr
      outPtr pBytes fBytes bBytes subBytes F h with hWholeQ
  -- success arm: convert the body's link pin to ownership, run the
  -- framed epilogue, tag the post `inl`
  have hS : cpsTripleWithin 7 (P + 88) (ret &&& ~~~1) fullCode
      ((prioritySuccessPost pPtr fPtr bPtr outPtr pBytes fBytes bBytes
        subBytes F) ** (((.x2 : Reg) ↦ᵣ nsp) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19)))
      WholeQ := by
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hEpiSF
    · dsimp only [prioritySuccessPost] at hp
      have hp1 : ((((.x1 : Reg) ↦ᵣ (P + 76))) **
          (((.x2 : Reg) ↦ᵣ nsp) **
            (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
            (.x19 ↦ᵣ outPtr) **
            (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19) **
            (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat subBytes
          then pPtr else outPtr)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x31 ↦ᵣ (32 : Word)) ** regOwn .x13 **
        regOwns prioritySubResidualScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion pPtr pBytes **
        bytesRegion outPtr (if beBytesToNat pBytes ≤ beBytesToNat subBytes
          then pBytes else subBytes) **
        bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes ** F))) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono_left (regIs_to_regOwn .x1 (P + 76)) h hp1
      xperm_hyp hp2
    · rw [hWholeQ]
      refine Or.inl ?_
      dsimp only [priorityWholeSuccessPost]
      rw [← hnsp]
      xperm_hyp hq
  -- reject arm
  have hFa : cpsTripleWithin 7 (P + 88) (ret &&& ~~~1) fullCode
      ((priorityFailurePost status pPtr fPtr bPtr outPtr pBytes fBytes
        bBytes subBytes F) ** (((.x2 : Reg) ↦ᵣ nsp) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19)))
      WholeQ := by
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hEpiFaF
    · dsimp only [priorityFailurePost] at hp
      have hp1 : ((((.x1 : Reg) ↦ᵣ (P + 56))) **
          (((.x2 : Reg) ↦ᵣ nsp) **
            (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
            (.x19 ↦ᵣ outPtr) **
            (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9) **
        ((nsp + 24) ↦ₘ v18) ** ((nsp + 32) ↦ₘ v19) **
            (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ⌜status ≠ 0⌝ **
        regOwns prioritySubRetScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion pPtr pBytes ** bytesRegion outPtr subBytes **
        bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes ** F))) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono_left (regIs_to_regOwn .x1 (P + 56)) h hp1
      xperm_hyp hp2
    · rw [hWholeQ]
      refine Or.inr ?_
      dsimp only [priorityWholeFailurePost]
      rw [← hnsp]
      xperm_hyp hq
  have hEpiOr := cps_or_pre hS hFa
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hEpiOr
    intro h hp
    exact sepConj_or_distrib h hp
  rw [hWholeQ] at s2
  refine cps_fuel_mono' ?_
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) s2)
  omega

#print axioms priority_fee_per_gas_eip1559_spec

end U256GasPricingSAsm

end EvmAsm.Codegen
