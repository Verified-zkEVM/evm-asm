import EvmAsm.Codegen.Programs.U256MulU64Be.WholeOuter

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm Rv64 Rv64.SAsm Rv64.SAsm.Stmt

def outerHeaderInitPre
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr old5 : Word) : Assertion :=
  ((.x20 : Reg) ↦ᵣ v20) ** ((.x5 : Reg) ↦ᵣ old5) **
    outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 0

def outerHeaderInitPost
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 0

theorem outerHeaderInit_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr old5 : Word) :
    cpsTripleWithin 2 (mulBase + 76) (mulBase + 84) mulCR
      (outerHeaderInitPre F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr old5)
      (outerHeaderInitPost F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr) := by
  have h20 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x20 v20 (0 : Word) (mulBase + 76) (by decide))
  rw [show mulBase + 76 + 4 = mulBase + 80 from by decide] at h20
  have houter : (outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 0).pcFree := by
    dsimp [outerLoopInv]
    exact pcFree_sepConj hF (by pcf)
  have h20F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ old5) **
      outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 0)
    (pcFree_sepConj pcFree_regIs houter) h20
  have h5 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x5 old5 (32 : Word) (mulBase + 80) (by decide))
  rw [show mulBase + 80 + 4 = mulBase + 84 from by decide] at h5
  have h5F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ (0 : Word)) **
      outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 0)
    (pcFree_sepConj pcFree_regIs houter) h5
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h20F h5F
  simpa only [outerHeaderInitPre, outerHeaderInitPost, sepConj_assoc', sepConj_comm',
    sepConj_left_comm'] using hseq

/- private def copyStable
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
    ((.x20 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwn .x13 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** frameSlots spNew vRa v8 v9 v18 v19 v20

def copyInitP
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) : Assertion :=
  copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
    regOwn .x28 **
    bytesRegion accBase accBytes ** bytesRegion outPtr outBytes

def copyStableNo19
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x20 : Reg) ↦ᵣ (32 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) ** regOwn .x13 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** frameSlots spNew vRa v8 v9 v18 v19 v20

def copyStableNo18
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x19 : Reg) ↦ᵣ accBase) ** ((.x20 : Reg) ↦ᵣ (32 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) ** regOwn .x13 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** frameSlots spNew vRa v8 v9 v18 v19 v20

theorem copyInit_exact_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes accBytes outBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr old6 old7 : Word) :
    cpsTripleWithin 3 (mulBase + 240) (mulBase + 252) mulCR
      (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ old6) **
        ((.x7 : Reg) ↦ᵣ old7) ** copyInitP F aBytes spNew vRa v8 v9 v18 v19 v20
          aPtr b outPtr accBytes outBytes)
      (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv (copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr)
          accBytes outBytes outPtr 0) := by
  have h0 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (mv_spec_gen_within .x5 .x19 accBase (32 : Word) (mulBase + 240) (by decide))
  rw [show mulBase + 240 + 4 = mulBase + 244 from by decide] at h0
  have hno19 : (copyStableNo19 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      regOwn .x28 ** bytesRegion accBase accBytes ** bytesRegion outPtr outBytes).pcFree := by
    dsimp [copyStableNo19]
    repeat (first | apply pcFree_sepConj | exact hF | pcf)
  have hno18 : (copyStableNo18 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      regOwn .x28 ** bytesRegion accBase accBytes ** bytesRegion outPtr outBytes).pcFree := by
    dsimp [copyStableNo18]
    repeat (first | apply pcFree_sepConj | exact hF | pcf)
  have hcopyP : (copyInitP F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
      accBytes outBytes).pcFree := by
    dsimp [copyInitP]
    exact pcFree_sepConj (by
      dsimp [copyStable]
      exact pcFree_sepConj hF (by pcf)) (by pcf)
  have h0F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ old6) ** ((.x7 : Reg) ↦ᵣ old7) **
      copyStableNo19 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      regOwn .x28 ** bytesRegion accBase accBytes ** bytesRegion outPtr outBytes)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hno19)) h0
  have h1 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (addi_spec_gen_within .x6 .x18 outPtr old6 (32 : BitVec 12) (mulBase + 244)
      (by decide))
  rw [show mulBase + 244 + 4 = mulBase + 248 from by decide,
    show Rv64.signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at h1
  have h1F := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ old7) ** ((.x5 : Reg) ↦ᵣ accBase) **
      copyStableNo18 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      regOwn .x28 ** bytesRegion accBase accBytes ** bytesRegion outPtr outBytes)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hno18)) h1
  have h2 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x7 old7 (32 : Word) (mulBase + 248) (by decide))
  rw [show mulBase + 248 + 4 = mulBase + 252 from by decide] at h2
  have h2F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ accBase) **
      ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 32)) **
      copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      regOwn .x28 ** bytesRegion accBase accBytes ** bytesRegion outPtr outBytes)
    (by
      dsimp [copyStable]
      repeat (first | apply pcFree_sepConj | exact hF | pcf)) h2
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have hseq' := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hseq h2F
  refine cpsTripleWithin_weaken (fun _ hp => by
    dsimp [copyInitP]
    xperm_hyp hp) (fun _ hq => by
    dsimp [copyInv, copyStable]
    xperm_hyp hq) hseq' -/

/-! ## Reverse copy from the accumulator into the result window

The copy is deliberately proved before the multiply loop.  Its source is the
low 32 bytes of the little-endian accumulator, while the result window is
filled from its end, so the machine's five-instruction body has a small,
independent functional state. -/

def copyState (accBytes outBytes : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => outBytes
  | i + 1 => (copyState accBytes outBytes i).set (31 - i) (accBytes.getD i 0)

def copyInv (F : Assertion) (accBytes outBytes : List (BitVec 8)) (outPtr : Word)
    (i : Nat) : Assertion :=
  F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i)) **
    ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (32 - i))) **
    regOwn .x28 **
    bytesRegion accBase accBytes ** bytesRegion outPtr (copyState accBytes outBytes i)

theorem frameSlots_pcFree
    (spNew vRa v8 v9 v18 v19 v20 : Word) :
    (frameSlots spNew vRa v8 v9 v18 v19 v20).pcFree := by
  dsimp [frameSlots]
  apply pcFree_sepConj
  · exact pcFree_memIs
  · apply pcFree_sepConj
    · exact pcFree_memIs
    · apply pcFree_sepConj
      · exact pcFree_memIs
      · apply pcFree_sepConj
        · exact pcFree_memIs
        · apply pcFree_sepConj
          · exact pcFree_memIs
          · exact pcFree_memIs

def copyStable
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
    ((.x20 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwn .x13 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** frameSlots spNew vRa v8 v9 v18 v19 v20

def copyInitP
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) : Assertion :=
  copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
    bytesRegion accBase accBytes ** bytesRegion outPtr outBytes

def copyStableNo19
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x20 : Reg) ↦ᵣ (32 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) ** regOwn .x13 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** frameSlots spNew vRa v8 v9 v18 v19 v20

def copyStableNo18
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x19 : Reg) ↦ᵣ accBase) ** ((.x20 : Reg) ↦ᵣ (32 : Word)) **
    ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) ** regOwn .x13 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** frameSlots spNew vRa v8 v9 v18 v19 v20

theorem copyInit_exact_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes accBytes outBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr old6 old7 : Word) :
    cpsTripleWithin 3 (mulBase + 240) (mulBase + 252) mulCR
      (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ old6) **
        ((.x7 : Reg) ↦ᵣ old7) ** copyInitP F aBytes spNew vRa v8 v9 v18 v19 v20
          aPtr b outPtr accBytes outBytes)
      (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv (copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr)
          accBytes outBytes outPtr 0) := by
  have h0 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (mv_spec_gen_within .x5 .x19 accBase (32 : Word) (mulBase + 240) (by decide))
  rw [show mulBase + 240 + 4 = mulBase + 244 from by decide] at h0
  letI : Assertion.PCFree F := ⟨hF⟩
  letI : Assertion.PCFree (bytesRegion aPtr aBytes) :=
    ⟨bytesRegion_pcFree _ _⟩
  letI : Assertion.PCFree (bytesRegion accBase accBytes) :=
    ⟨bytesRegion_pcFree _ _⟩
  letI : Assertion.PCFree (bytesRegion outPtr outBytes) :=
    ⟨bytesRegion_pcFree _ _⟩
  letI : Assertion.PCFree (frameSlots spNew vRa v8 v9 v18 v19 v20) :=
    ⟨frameSlots_pcFree _ _ _ _ _ _ _⟩
  have h0F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ old6) ** ((.x7 : Reg) ↦ᵣ old7) **
      copyStableNo19 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
      bytesRegion accBase accBytes ** bytesRegion outPtr outBytes)
    (by
      dsimp [copyStableNo19]
      exact (inferInstance : Assertion.PCFree _).proof) h0
  have h1 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (addi_spec_gen_within .x6 .x18 old6 outPtr (32 : BitVec 12) (mulBase + 244)
      (by decide))
  rw [show mulBase + 244 + 4 = mulBase + 248 from by decide,
    show Rv64.signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at h1
  have h1F := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ old7) **
      ((.x5 : Reg) ↦ᵣ accBase) **
      copyStableNo18 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
      bytesRegion accBase accBytes ** bytesRegion outPtr outBytes)
    (by
      dsimp [copyStableNo18]
      exact (inferInstance : Assertion.PCFree _).proof) h1
  have h2 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x7 old7 (32 : Word) (mulBase + 248) (by decide))
  rw [show mulBase + 248 + 4 = mulBase + 252 from by decide] at h2
  have h2F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 32)) **
      ((.x5 : Reg) ↦ᵣ accBase) ** ((.x18 : Reg) ↦ᵣ outPtr) **
      copyStableNo18 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
      bytesRegion accBase accBytes ** bytesRegion outPtr outBytes)
    (by
      dsimp [copyStableNo18]
      exact (inferInstance : Assertion.PCFree _).proof) h2
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    dsimp [copyStableNo19, copyStableNo18, copyStable] at hp ⊢
    xperm_hyp hp) h0F h1F
  have hseq' := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    dsimp [copyStableNo18, copyStable] at hp ⊢
    xperm_hyp hp) hseq h2F
  refine cpsTripleWithin_weaken (fun _ hp => by
    dsimp [copyInitP, copyStableNo19, copyStableNo18, copyStable] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp [copyInv, copyStableNo19, copyStableNo18, copyStable] at hq ⊢
    simp only [BitVec.add_zero] at hq ⊢
    xperm_hyp hq) hseq'

theorem copy_src_succ (i : Nat) (_hi : i < 32) :
    accBase + BitVec.ofNat 64 i + Rv64.signExtend12 (1 : BitVec 12) =
      accBase + BitVec.ofNat 64 (i + 1) := by
  rw [show Rv64.signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  bv_omega

theorem copy_dst_decr (outPtr : Word) (i : Nat) (_hi : i < 32) :
    outPtr + BitVec.ofNat 64 (32 - i) + Rv64.signExtend12 (-1 : BitVec 12) =
      outPtr + BitVec.ofNat 64 (31 - i) := by
  have hc :
      BitVec.ofNat 64 (32 - i) + (-1 : Word) =
        BitVec.ofNat 64 (31 - i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
    omega
  rw [show Rv64.signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
    BitVec.add_assoc, hc]

theorem copy_ctr_decr (i : Nat) (_hi : i < 32) :
    BitVec.ofNat 64 (32 - i) + Rv64.signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 (32 - (i + 1)) := by
  rw [show Rv64.signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  bv_omega

theorem copyState_succ (accBytes outBytes : List (BitVec 8)) (i : Nat) :
    copyState accBytes outBytes (i + 1) =
      (copyState accBytes outBytes i).set (31 - i) (accBytes.getD i 0) := rfl

theorem copyState_len (accBytes outBytes : List (BitVec 8)) (i : Nat)
    (hout : outBytes.length = 32) :
    (copyState accBytes outBytes i).length = 32 := by
  induction i with
  | zero => exact hout
  | succ i ih => rw [copyState_succ, List.length_set, ih]

theorem copyBody_spec (F : Assertion) (hF : F.pcFree)
    (accBytes outBytes : List (BitVec 8)) (outPtr : Word)
    (hacc : accBytes.length = 40) (hout : outBytes.length = 32)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true)
    (i : Nat) (hi : i < 32) :
    cpsTripleWithin 5 (mulBase + 256) (mulBase + 276) mulCR
      (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        copyInv F accBytes outBytes outPtr i)
      (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
        (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (i + 1))) **
        ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (31 - i))) **
        ((.x28 : Reg) ↦ᵣ (accBytes[i]'(by omega)).zeroExtend 64) **
        bytesRegion accBase accBytes **
        bytesRegion outPtr (copyState accBytes outBytes (i + 1)))) := by
  let pre : Assertion :=
    ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      copyInv F accBytes outBytes outPtr i
  let post : Assertion :=
    ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (i + 1))) **
      ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (31 - i))) **
      ((.x28 : Reg) ↦ᵣ (accBytes[i]'(by omega)).zeroExtend 64) **
      bytesRegion accBase accBytes **
      bytesRegion outPtr (copyState accBytes outBytes (i + 1)))
  have h0 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (addi_spec_gen_same_within .x6 (outPtr + BitVec.ofNat 64 (32 - i))
      (-1 : BitVec 12) (mulBase + 256) (by decide))
  rw [show mulBase + 256 + 4 = mulBase + 260 from by decide,
    copy_dst_decr outPtr i hi] at h0
  have h1own0 : cpsTripleWithin 1 (mulBase + 260) (mulBase + 264) mulCR
      ((((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i)) **
        bytesRegion accBase accBytes) ** regOwn .x28)
      (((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i)) **
        ((.x28 : Reg) ↦ᵣ (accBytes[i]'(by omega)).zeroExtend 64) **
        bytesRegion accBase accBytes) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i)) **
        bytesRegion accBase accBytes) (r := .x28) ?_
    intro old28
    have h1 := bytesRegion_lbu_within .x28 .x5 accBase old28 (mulBase + 260)
      accBytes i (by decide) accBase_align (by omega)
      (by apply accBase_no_overflow; omega) (by apply accBase_valid_byte; omega)
    have h1e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h1
    rw [show mulBase + 260 + 4 = mulBase + 264 from by decide] at h1e
    simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using h1e
  have h2 := bytesRegion_sb_within .x6 .x28 outPtr
      ((accBytes[i]'(by omega)).zeroExtend 64) (mulBase + 264)
      (copyState accBytes outBytes i) (31 - i)
      halignOut (by rw [copyState_len _ _ i hout]; omega)
      (by omega) (hvalidOut (31 - i) (by omega))
  have h2e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h2
  rw [show mulBase + 264 + 4 = mulBase + 268 from by decide] at h2e
  have hset :
      (copyState accBytes outBytes i).set (31 - i)
          (((accBytes[i]'(by omega)).zeroExtend 64).truncate 8) =
        copyState accBytes outBytes (i + 1) := by
    rw [truncate_zeroExtend_byte, copyState_succ]
    have hiAcc : i < accBytes.length := by omega
    have hget : accBytes.getD i 0 = accBytes[i]'hiAcc := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiAcc]
      rfl
    rw [hget]
  rw [hset] at h2e
  have h3 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (addi_spec_gen_same_within .x5 (accBase + BitVec.ofNat 64 i)
      (1 : BitVec 12) (mulBase + 268) (by decide))
  rw [show mulBase + 268 + 4 = mulBase + 272 from by decide,
    copy_src_succ i hi] at h3
  have h4 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (addi_spec_gen_same_within .x7 (BitVec.ofNat 64 (32 - i))
      (-1 : BitVec 12) (mulBase + 272) (by decide))
  rw [show mulBase + 272 + 4 = mulBase + 276 from by decide,
    copy_ctr_decr i hi] at h4
  have f0 := cpsTripleWithin_frameR
    (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i)) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) ** regOwn .x28 **
      bytesRegion accBase accBytes ** bytesRegion outPtr (copyState accBytes outBytes i))
    (pcFree_sepConj hF (by pcf)) h0
  have f1 := cpsTripleWithin_frameR
    (F ** ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (31 - i))) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      bytesRegion outPtr (copyState accBytes outBytes i))
    (pcFree_sepConj hF (by pcf)) h1own0
  have f2 := cpsTripleWithin_frameR
    (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 i)) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      bytesRegion accBase accBytes) (pcFree_sepConj hF (by pcf)) h2e
  have f3 := cpsTripleWithin_frameR
    (F ** ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (31 - i))) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x28 : Reg) ↦ᵣ (accBytes[i]'(by omega)).zeroExtend 64) **
      bytesRegion accBase accBytes ** bytesRegion outPtr (copyState accBytes outBytes (i + 1)))
    (pcFree_sepConj hF (by pcf)) h3
  have f4 := cpsTripleWithin_frameR
    (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (i + 1))) **
      ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (31 - i))) **
      ((.x28 : Reg) ↦ᵣ (accBytes[i]'(by omega)).zeroExtend 64) **
      bytesRegion accBase accBytes ** bytesRegion outPtr (copyState accBytes outBytes (i + 1)))
    (pcFree_sepConj hF (by pcf)) h4
  simp only [sepConj_assoc'] at f0 f1 f2 f3 f4
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 f1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f2
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f3
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f4
  exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp [pre, copyInv] at hp ⊢
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
    (fun _ hq => by
      dsimp [post] at hq ⊢
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq) s4

theorem copyLoop_spec (F : Assertion) (hF : F.pcFree)
    (accBytes outBytes : List (BitVec 8)) (outPtr : Word)
    (hacc : accBytes.length = 40) (hout : outBytes.length = 32)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 225 (mulBase + 252) (mulBase + 280) mulCR
      (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv F accBytes outBytes outPtr 0)
      (((.x7 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv F accBytes outBytes outPtr 32) := by
  let inv : Nat → Assertion := fun n =>
    copyInv F accBytes outBytes outPtr (32 - n)
  have hinv : ∀ n, (inv n).pcFree := by
    intro n
    dsimp [inv, copyInv]
    apply pcFree_sepConj
    · exact hF
    · pcf
  have hguardMem : ∀ a ins,
      CodeReq.singleton (mulBase + 252) (.BEQ .x7 .x0 (28 : BitVec 13)) a = some ins →
        mulCR a = some ins := by
    intro a ins h
    exact CodeReq.ofProg_mem_at mulBase (mulBase + 252) mulProg 63
      (.BEQ .x7 .x0 (28 : BitVec 13)) (by decide) (by decide) (by decide)
      (by decide) a ins h
  have hbody : ∀ n, n < 32 →
      cpsTripleWithin 6 (mulBase + 256) (mulBase + 252) mulCR
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** inv (n + 1))
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** inv n) := by
    intro n hn
    have hi : 31 - n < 32 := by omega
    have hcopy := copyBody_spec F hF accBytes outBytes outPtr hacc hout
      halignOut hoverOut hvalidOut (31 - n) hi
    have hcopy0 := cpsTripleWithin_frameR
      ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcf) hcopy
    have hjal := cpsTripleWithin_extend_code (cr' := mulCR)
      (hmono := by code_mem)
      (jal_x0_spec_gen_within (-24 : BitVec 21) (mulBase + 276))
    rw [show mulBase + 276 + Rv64.signExtend21 (-24 : BitVec 21) =
      mulBase + 252 from by decide] at hjal
    have hjalF := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        inv n) (by
          apply pcFree_sepConj
          · pcf
          · apply pcFree_sepConj
            · pcf
            · exact hinv n) hjal
    have hjalF' : cpsTripleWithin 1 (mulBase + 276) (mulBase + 252) mulCR
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          inv n)
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          inv n) := by
      refine cpsTripleWithin_weaken
        (fun _ hp => by simpa only [sepConj_emp_left'] using hp)
        (fun _ hq => by simpa only [sepConj_emp_left'] using hq) hjalF
    have hcopy1 : cpsTripleWithin 5 (mulBase + 256) (mulBase + 276) mulCR
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** inv (n + 1))
        (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** inv n) := by
      have hiPre : 32 - (31 - n) = n + 1 := by omega
      have hiPreInv : 32 - (n + 1) = 31 - n := by omega
      have hiPost : 32 - (32 - n) = n := by omega
      have hiXPost : 32 - (31 - n + 1) = n := by omega
      have hiCopyPost : 31 - n + 1 = 32 - n := by omega
      have hiX6Post : 31 - (31 - n) = n := by omega
      have hcopy' : cpsTripleWithin 5 (mulBase + 256) (mulBase + 276) mulCR
          (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              copyInv F accBytes outBytes outPtr (31 - n))
          (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              copyInv F accBytes outBytes outPtr (32 - n)) := by
        refine cpsTripleWithin_weaken
          (fun _ hp => by
          rw [hiPre] at ⊢
          simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
          (fun s hq => by
          dsimp [copyInv] at ⊢
          rw [hiPost] at ⊢
          rw [hiXPost, hiCopyPost, hiX6Post] at hq
          have hqFixed :
              (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 - n))) **
                  ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 n)) **
                  ((.x28 : Reg) ↦ᵣ (accBytes[31 - n]'(by omega)).zeroExtend 64) **
                  bytesRegion accBase accBytes **
                  bytesRegion outPtr (copyState accBytes outBytes (32 - n)))) s := by
            simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq
          have hrest : ∀ s,
              (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 - n))) **
                ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 n)) **
                ((.x28 : Reg) ↦ᵣ (accBytes[31 - n]'(by omega)).zeroExtend 64) **
                bytesRegion accBase accBytes **
                bytesRegion outPtr (copyState accBytes outBytes (32 - n))) s →
              (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 - n))) **
                ((.x6 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 n)) **
                regOwn .x28 ** bytesRegion accBase accBytes **
                bytesRegion outPtr (copyState accBytes outBytes (32 - n))) s := by
            intro s hs
            exact sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_left (regIs_to_regOwn .x28 _)))) s hs
          exact sepConj_mono_right (sepConj_mono_right hrest) _ hqFixed)
          hcopy0
      simpa [inv, hiPreInv] using hcopy'
    have hseq := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hcopy1 hjalF'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hseq
  have hloop := countdownLoop_spec mulCR (mulBase + 252) (mulBase + 280)
    .x7 (28 : BitVec 13) 6 32 inv (by decide) (by decide)
    (by decide) hinv hguardMem (by
      intro n hn
      exact hbody n hn)
  simpa [inv] using hloop


end EvmAsm.Codegen.U256MulU64Be
