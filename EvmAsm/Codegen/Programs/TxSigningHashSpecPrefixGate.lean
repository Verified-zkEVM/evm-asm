/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecPrefixGate

  Gate-lift glue for K145 `tx_signing_hash` (#12038): compose
  total `tsh_prefix_any_callWithin` (every `Word` length, short+long1..long8)
  into the success path with zero-init 16-byte BSS ownership inside the
  existing 128 KiB `tsh_buf`, and `segs` = bare `rlpListPrefix`.

  Lives outside `TxSigningHashSpecSuccess` to stay under the Programs 1500-line cap.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecSuccess

namespace EvmAsm.Codegen.TxSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.MptSpliceSlotSpec
open EvmAsm.Rv64.Tactics
/-! ## Post-nth → any-form prefix `callWithin` (`H+160 → H+220`) -/

/-- nth-success continue through contiguous `rlp_encode_list_prefix` (total on Word).

    Requires the full BSS slot (`8 < |outBytes|`). Clobbers short+long temps. -/
theorem tshPostNthThenPrefixCall_any_spec
    (vOld v5 v6 v7 v28 v29 v30 v31 v11 v12 v22 offVal lenVal hdrLen cellOld : Word)
    (outBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    let payloadLen := (offVal + lenVal) - hdrLen
    cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
      ((.x1 ↦ᵣ vOld) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F)
      ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
        (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
  intro payloadLen
  have hAmb :
      ((.x1 ↦ᵣ vOld) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  have hprep := tshPostNthToPrefixJal_spec v5 v6 v7 v11 v12 v22 offVal lenVal hdrLen
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ vOld) **
      bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
      ((.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** F))
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact hF) hprep
  have hCallF :
      ((.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) ** F).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact hF
  have hcall := tsh_prefix_any_callWithin vOld payloadLen tshPrefixOutPtr
    tshPrefixCellPtr TshBuf (offVal + lenVal) lenVal v28 v29 v30 v31
    outBytes cellOld
    ((.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) ** F)
    hCallF h_out_align h_out_len h_out_valid
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [payloadLen] at hp ⊢
      xperm_hyp hp) hprepF hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [payloadLen] at hq ⊢
      xperm_hyp hq) c

/-- Success-status nth return through any-form prefix `callWithin`. -/
theorem tshNthOkThenPrefixCall_any_spec
    (v11 v12 v22 offVal lenVal hdrLen cellOld : Word)
    (outBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    let payloadLen := (offVal + lenVal) - hdrLen
    let retNth := tshNthJalPC + 4
    cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
      ((.x1 ↦ᵣ retNth) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F)
      ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
        (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
  intro payloadLen retNth
  have hinn : ∀ v5 v6 v7 v28 v29 v30 v31,
      cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
        ((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
          (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
    intro v5 v6 v7 v28 v29 v30 v31
    have h := tshPostNthThenPrefixCall_any_spec retNth v5 v6 v7 v28 v29 v30 v31
      v11 v12 v22 offVal lenVal hdrLen cellOld outBytes F hF
      h_out_align h_out_len h_out_valid
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [retNth] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [payloadLen] at hq ⊢
        exact hq) h
  -- Peel regOwn → regIs outward (x31 … x5).
  have h31 : ∀ v5 v6 v7 v28 v29 v30,
      cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F) **
          regOwn .x31)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
          (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
    intro v5 v6 v7 v28 v29 v30
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v31 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (hinn v5 v6 v7 v28 v29 v30 v31)
  have h30 : ∀ v5 v6 v7 v28 v29,
      cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
          F ** regOwn .x31) **
          regOwn .x30)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
          (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
    intro v5 v6 v7 v28 v29
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v30 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h31 v5 v6 v7 v28 v29 v30)
  have h29 : ∀ v5 v6 v7 v28,
      cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
          F ** regOwn .x31 ** regOwn .x30) **
          regOwn .x29)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
          (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
    intro v5 v6 v7 v28
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v29 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h30 v5 v6 v7 v28 v29)
  have h28 : ∀ v5 v6 v7,
      cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
          F ** regOwn .x31 ** regOwn .x30 ** regOwn .x29) **
          regOwn .x28)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
          (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
    intro v5 v6 v7
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v28 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h29 v5 v6 v7 v28)
  have h7 : ∀ v5 v6,
      cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
          F ** regOwn .x31 ** regOwn .x30 ** regOwn .x29 ** regOwn .x28) **
          regOwn .x7)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
          (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
    intro v5 v6
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v7 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h28 v5 v6 v7)
  have h6 : ∀ v5,
      cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
          F ** regOwn .x31 ** regOwn .x30 ** regOwn .x29 ** regOwn .x28 ** regOwn .x7) **
          regOwn .x6)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
          (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
    intro v5
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v6 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h7 v5 v6)
  have h5 :
      cpsTripleWithin ((1 + 8 + 6) + (1 + tshPrefixFuel)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
          F ** regOwn .x31 ** regOwn .x30 ** regOwn .x29 ** regOwn .x28 **
          regOwn .x7 ** regOwn .x6) **
          regOwn .x5)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr (tshPrefixApply outBytes payloadLen.toNat) **
          (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v5 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h6 v5)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h5

/-! ## Nth ok → any prefix → typed gather → success (`H+160 → bodyExit`) -/

/-- Trailing zero dword of the 16-byte prefix BSS when `NH ≤ 8`.
    Empty when `NH = 9` (long8): that dword is part of the bare header region. -/
def tshPrefixBssTail (payloadLen : Word) : Assertion :=
  if payloadLen.toNat < 72057594037927936 then
    bytesRegion (tshPrefixOutPtr + 8) (List.replicate 8 (0 : BitVec 8))
  else
    empAssertion

theorem tshPrefixBssTail_pcFree (payloadLen : Word) :
    (tshPrefixBssTail payloadLen).pcFree := by
  unfold tshPrefixBssTail
  split
  · exact bytesRegion_pcFree _ _
  · exact pcFree_emp

/-- Peeled nth-success through any-form prefix and typed multi-rate finish.

    Specializes the BSS slot to zero-init 16 bytes so Apply covers long8;
    `segs` use bare `rlpListPrefix`. When NH ≤ 8 the trailing zero dword is
    framed through gather/kss as `tshPrefixBssTail`. -/
theorem tshNthOkThroughTypedSuccess_any_spec
    (v11 v12 v22 offVal lenVal hdrLen cellOld : Word)
    (typePrefix inPtr outPtr : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (sp0 v9 v18 : Word)
    (typeBs payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hnz : typePrefix ≠ 0)
    (htypeLen : typeBs.length = 1)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ((offVal + lenVal) - hdrLen) = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ s ∈ tshTypedSegs typeBs
        (rlpListPrefix ((offVal + lenVal) - hdrLen).toNat)
        payloadBs inPtr hdrLen,
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let payloadLen := (offVal + lenVal) - hdrLen
    let prefixBs := rlpListPrefix payloadLen.toNat
    let cellVal := BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)
    let segs := tshTypedSegs typeBs prefixBs payloadBs inPtr hdrLen
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let prefixFuel := (1 + 8 + 6) + (1 + tshPrefixFuel)
    let gatherFuel := 6 + 3 + 4 + 5 + 3 + 3
    let kssFuel := 1 + (19 + kssBodyFuelMulti segs) + 2
    let bssTail := tshPrefixBssTail payloadLen
    cpsTripleWithin (prefixFuel + (gatherFuel + kssFuel)) (H + 160) tshBodyExit fullCode
      ((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
        (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x2 ↦ᵣ sp0) **
        frameSlotsOwn kssFrame newSp **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
        bytesRegion TshBuf typeBs **
        bytesRegion (inPtr + hdrLen) payloadBs **
        bytesRegion KssZk3 os **
        bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
        regOwns kssFreeTemps ** A ** F)
      (((.x1 ↦ᵣ (tshKssJalPC + 4)) **
        (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
          inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
          ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
            (.x31 ↦ᵣ (inPtr + hdrLen)) **
            (tshPrefixCellPtr ↦ₘ cellVal) **
            ((tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
              regOwn .x28 ** (bssTail ** F)))))) := by
  intro outBytes payloadLen prefixBs cellVal segs newSp prefixFuel gatherFuel kssFuel bssTail
  let Amb : Assertion :=
    (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
      (.x2 ↦ᵣ sp0) **
      frameSlotsOwn kssFrame newSp **
      (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
      ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
      ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
      bytesRegion TshBuf typeBs **
      bytesRegion (inPtr + hdrLen) payloadBs **
      bytesRegion KssZk3 os **
      bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
      regOwns kssFreeTemps ** A ** F
  have hAmb : Amb.pcFree := by
    unfold Amb
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_frameSlotsOwn _ _
      | exact bytesRegion_pcFree _ _
      | exact hA
      | exact hF
      | exact (by pcf)
  have hout_len : 8 < outBytes.length := by
    simp only [outBytes, List.length_replicate]; decide
  have h_out_valid' : ∀ k, k < outBytes.length →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true := by
    intro k hk
    simp only [outBytes, List.length_replicate] at hk
    exact h_out_valid k hk
  have hpref := tshNthOkThenPrefixCall_any_spec v11 v12 v22 offVal lenVal hdrLen cellOld
    outBytes Amb hAmb h_out_align hout_len h_out_valid'
  -- Gather/kss peel parameterized by the framed ambient `G` (F or zeros**F).
  have htail_of : ∀ (G : Assertion) (hG : G.pcFree) (v29 v30 v31),
      cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr prefixBs **
          (tshPrefixCellPtr ↦ₘ cellVal) **
          (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
          (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
          (.x2 ↦ᵣ sp0) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          frameSlotsOwn kssFrame newSp **
          (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
          ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
          ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
          bytesRegion TshBuf typeBs **
          bytesRegion (inPtr + hdrLen) payloadBs **
          bytesRegion KssZk3 os **
          bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
          regOwns kssFreeTemps ** A ** G)
        ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
          (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
            inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
            ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
              (.x31 ↦ᵣ (inPtr + hdrLen)) **
              (tshPrefixCellPtr ↦ₘ cellVal) **
              ((tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
                regOwn .x28 ** G)))) := by
    intro G hG v29 v30 v31
    have hcell : cellVal = BitVec.ofNat 64 prefixBs.length := by
      simp only [cellVal, prefixBs, tshPrefixNH]
    let F28 : Assertion := regOwn .x28 ** G
    have hF28 : F28.pcFree := pcFree_sepConj pcFree_regOwn hG
    have h := tshPrefixReturnThenTypedSuccess_spec v29 v30 v31 typePrefix inPtr outPtr
      hdrLen payloadLen cellVal old0 old1 old2 old3 old4 old5 sp0 v9 v18 offVal lenVal
      typeBs prefixBs payloadBs os A F28 hA hF28 hnz htypeLen hcell hpayW hos
      (by simpa [prefixBs, payloadLen] using hsegsOk)
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [payloadLen, prefixBs, cellVal, F28] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [payloadLen, prefixBs, cellVal, segs, F28, newSp] at hq ⊢
        exact hq) h
  have htail_peel : ∀ (G : Assertion) (hG : G.pcFree),
      cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
        (((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr prefixBs **
          (tshPrefixCellPtr ↦ₘ cellVal) **
          (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
          (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
          (.x2 ↦ᵣ sp0) **
          frameSlotsOwn kssFrame newSp **
          (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
          ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
          ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
          bytesRegion TshBuf typeBs **
          bytesRegion (inPtr + hdrLen) payloadBs **
          bytesRegion KssZk3 os **
          bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
          regOwns kssFreeTemps ** A ** G ** regOwn .x31 ** regOwn .x30) **
          regOwn .x29)
        ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
          (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
            inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
            ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
              (.x31 ↦ᵣ (inPtr + hdrLen)) **
              (tshPrefixCellPtr ↦ₘ cellVal) **
              ((tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
                regOwn .x28 ** G)))) := by
    intro G hG
    have h31 : ∀ v29 v30,
        cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
          (((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
            (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 **
            (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
            (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
            (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
            bytesRegion tshPrefixOutPtr prefixBs **
            (tshPrefixCellPtr ↦ₘ cellVal) **
            (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
            (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
            (.x2 ↦ᵣ sp0) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
            frameSlotsOwn kssFrame newSp **
            (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
            ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
            ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
            bytesRegion TshBuf typeBs **
            bytesRegion (inPtr + hdrLen) payloadBs **
            bytesRegion KssZk3 os **
            bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
            regOwns kssFreeTemps ** A ** G) **
            regOwn .x31)
          ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
            (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
              inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
              ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
                (.x31 ↦ᵣ (inPtr + hdrLen)) **
                (tshPrefixCellPtr ↦ₘ cellVal) **
                ((tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
                  regOwn .x28 ** G)))) := by
      intro v29 v30
      refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v31 => ?_)
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (htail_of G hG v29 v30 v31)
    have h30 : ∀ v29,
        cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
          (((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
            (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 **
            (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
            (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
            (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
            bytesRegion tshPrefixOutPtr prefixBs **
            (tshPrefixCellPtr ↦ₘ cellVal) **
            (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
            (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
            (.x2 ↦ᵣ sp0) ** (.x29 ↦ᵣ v29) **
            frameSlotsOwn kssFrame newSp **
            (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
            ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
            ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
            bytesRegion TshBuf typeBs **
            bytesRegion (inPtr + hdrLen) payloadBs **
            bytesRegion KssZk3 os **
            bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
            regOwns kssFreeTemps ** A ** G ** regOwn .x31) **
            regOwn .x30)
          ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
            (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
              inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
              ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
                (.x31 ↦ᵣ (inPtr + hdrLen)) **
                (tshPrefixCellPtr ↦ₘ cellVal) **
                ((tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
                  regOwn .x28 ** G)))) := by
      intro v29
      refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v30 => ?_)
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (h31 v29 v30)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v29 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h30 v29)
  have hpos := tshPrefixNH_pos payloadLen.toNat
  by_cases hlt : payloadLen.toNat < 72057594037927936
  · have hbr := tshPrefix_bytesRegion_apply16_eq_hdr_lt_2_56 tshPrefixOutPtr
        payloadLen.toNat hlt hpos
    let G : Assertion :=
      bytesRegion (tshPrefixOutPtr + 8) (List.replicate 8 (0 : BitVec 8)) ** F
    have hG : G.pcFree := pcFree_sepConj (bytesRegion_pcFree _ _) hF
    have htail := htail_peel G hG
    have hbss : (bssTail ** F) = G := by
      simp only [bssTail, tshPrefixBssTail, G, hlt, ↓reduceIte]
    have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
        simp only [Amb, payloadLen, prefixBs, cellVal, outBytes, hbr, G] at hp ⊢
        xperm_hyp hp) hpref htail
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [Amb, outBytes] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [payloadLen, prefixBs, cellVal, segs, hbss] at hq ⊢
        exact hq) c
  · have hge : 72057594037927936 ≤ payloadLen.toNat := Nat.le_of_not_lt hlt
    have hbr := tshPrefix_bytesRegion_apply16_eq_hdr_ge_2_56 tshPrefixOutPtr
        payloadLen.toNat hge payloadLen.isLt
    have htail := htail_peel F hF
    have hbss : (bssTail ** F) = F := by
      simp only [bssTail, tshPrefixBssTail, hlt, ↓reduceIte, sepConj_emp_left']
    have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
        simp only [Amb, payloadLen, prefixBs, cellVal, outBytes, hbr] at hp ⊢
        xperm_hyp hp) hpref htail
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [Amb, outBytes] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [payloadLen, prefixBs, cellVal, segs, hbss] at hq ⊢
        exact hq) c

end EvmAsm.Codegen.TxSigningHashSpec
