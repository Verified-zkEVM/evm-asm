/-
  K146 H+324 tail composition: the prefix terminator, KSS descriptor call,
  and final body frame.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyTailCore
import EvmAsm.Codegen.Programs.TxSigningHashLegacyBodyCompose
import EvmAsm.Codegen.Proofs.HashBridgeSha256Final

namespace EvmAsm.Codegen.TxSigningHashLegacyTailCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashLegacySpec
open EvmAsm.Codegen.TxSigningHashLegacyCompose
open EvmAsm.Codegen.TxSigningHashLegacyCopySpec
open EvmAsm.Codegen.TxSigningHashLegacyLoopSpec
open EvmAsm.Codegen.TxSigningHashLegacyChainCompose
open EvmAsm.Codegen.TxSigningHashLegacyUintCompose
open EvmAsm.Codegen.TxSigningHashLegacyPrefixCompose
open EvmAsm.Codegen.TxSigningHashLegacyPrefixCopyCompose
open EvmAsm.Codegen.TxSigningHashSpec
open EvmAsm.Codegen.MptSpliceSlotSpec
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpEncodeUintBeSAsm
open EvmAsm.EL.RLP
/-! The prefix routine writes a 16-byte zero-init slot, while KSS consumes
    only the logical RLP header.  For the short forms the second dword is a
    caller-owned BSS tail; for long8 the nine-byte header occupies both
    dwords.  Keep that split explicit at the K146 boundary rather than
    treating the physical slot as part of the logical segment. -/

def legacyPrefixBssTail (payloadLen : Word) : Assertion :=
  if payloadLen.toNat < 72057594037927936 then
    bytesRegion (legacyPrefixOutPtr + 8) (List.replicate 8 (0 : BitVec 8))
  else
    empAssertion

theorem legacyPrefixBssTail_pcFree (payloadLen : Word) :
    (legacyPrefixBssTail payloadLen).pcFree := by
  unfold legacyPrefixBssTail
  split
  · exact bytesRegion_pcFree _ _
  · exact pcFree_emp

theorem legacyPrefixCopyThenTerminator_split_spec
    (chainId v21 : Word) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    let n :=
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
    let chainLen : Word := BitVec.ofNat 64 n
    let payloadLen := v21 + (chainLen + 2)
    let prefixBytes := rlpListPrefix payloadLen.toNat
    let bssTail := legacyPrefixBssTail payloadLen
    cpsTripleWithin
      (8 + (1 + tshPrefixFuel) + 8 + (n * (6 + 1) + 1) + 4)
      (legacyH + 228) (legacyH + 340) legacyFullCode
      (legacyChainUintPost chainId
          (bytesRegion legacyPrefixOutPtr
              (List.replicate 16 (0 : BitVec 8)) **
            (legacyPrefixCellPtr ↦ₘ cellOld) **
            bytesRegion legacySuffixOutPtr (List.replicate n 0) **
            (legacyTailExtension n ** F)) **
        ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22)
      (((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
        ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 2)) **
        ((.x5 : Reg) ↦ᵣ
          (legacySuffixOutPtr + BitVec.ofNat 64 n)) **
        ((.x6 : Reg) ↦ᵣ
          (legacySuffixChainEncPtr + BitVec.ofNat 64 n)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 **
        ((.x21 : Reg) ↦ᵣ v21) ** ((.x22 : Reg) ↦ᵣ payloadLen) **
        ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
        bytesRegion legacyLinkedChainEncPtr
          (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
            legacyChainEncOld.drop n) **
        bytesRegion legacyPrefixOutPtr prefixBytes **
        (legacyPrefixCellPtr ↦ₘ BitVec.ofNat 64 prefixBytes.length) **
        bytesRegion legacySuffixOutPtr (legacyTailOutputBytes chainId) **
        bssTail ** F) := by
  intro n chainLen payloadLen prefixBytes bssTail
  let outBytes : List (BitVec 8) := List.replicate 16 0
  have hout_len : 8 < outBytes.length := by
    simp [outBytes]
  have hout_end : outBytes.length ≤ 64 := by
    simp [outBytes]
  have hout_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true := by
    intro k hk
    exact h_out_valid k (by simpa [outBytes] using hk)
  have htail_pc : (legacyTailExtension n).pcFree := legacyTailExtension_pcFree n
  have hprefix := legacyPrefixSetupCopy_spec chainId v21 outBytes cellOld
    (legacyTailExtension n ** F)
    (pcFree_sepConj htail_pc hF) hout_len hout_end hout_valid
  have hterm := legacyPrefixCopyThenTerminator_spec chainId v21 outBytes
    F hF
  have hseq := cpsTripleWithin_seq_same_cr hprefix hterm
  have hpos := tshPrefixNH_pos payloadLen.toNat
  have hprefix_len : prefixBytes.length = tshPrefixNH payloadLen.toNat := by
    rfl
  by_cases hlt : payloadLen.toNat < 72057594037927936
  · have hbr := tshPrefix_bytesRegion_apply16_eq_hdr_lt_2_56
        legacyPrefixOutPtr payloadLen.toNat hlt hpos
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [outBytes, n] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [outBytes, bssTail, payloadLen, chainLen, n,
          legacyPrefixBssTail, hlt, ↓reduceIte] at hq ⊢
        rw [hbr] at hq
        rw [hprefix_len] at ⊢
        xperm_hyp hq)
      hseq
  · have hge : 72057594037927936 ≤ payloadLen.toNat := Nat.le_of_not_lt hlt
    have hbr := tshPrefix_bytesRegion_apply16_eq_hdr_ge_2_56
        legacyPrefixOutPtr payloadLen.toNat hge payloadLen.isLt
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [outBytes, n] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [outBytes, bssTail, payloadLen, chainLen, n,
          legacyPrefixBssTail, hlt, ↓reduceIte, sepConj_emp_left'] at hq ⊢
        rw [hbr] at hq
        rw [hprefix_len] at ⊢
        xperm_hyp hq)
      hseq

/-! Compose the chain-buffer loop, its argument setup, the linked Uint encoder,
    and the prefix/suffix tail.  The frame parameters are kept explicit so
    this theorem is the bounded K146 body segment that a caller can consume
    without re-proving any of the four linked edges. -/

theorem legacyChainThenPrefixTerminator_split_spec
    (v1 v5 v6 v7 v10 v11 v12 v28 chainId v21 : Word)
    (v29 v30 v31 cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0)
    (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess
        (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    let n :=
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
    let uintFuel :=
      1 + (8 * 6 + 7 *
        (8 - RlpEncodeUintBeSAsm.reubZeros (chainBytes chainId) 0 8) + 17)
    let prefixFuel := 8 + (1 + tshPrefixFuel) + 8 + (n * (6 + 1) + 1) + 4
    cpsTripleWithin (68 + 8 + uintFuel + prefixFuel)
      (legacyH + 160) (legacyH + 340) legacyFullCode
      (((.x1 : Reg) ↦ᵣ v1) **
        ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x7 : Reg) ↦ᵣ v7) ** ((.x10 : Reg) ↦ᵣ v10) **
        ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x18 : Reg) ↦ᵣ chainId) ** ((.x28 : Reg) ↦ᵣ v28) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (List.replicate 8 0) **
        bytesRegion legacyLinkedChainEncPtr legacyChainEncOld **
        bytesRegion legacyPrefixOutPtr
          (List.replicate 16 (0 : BitVec 8)) **
        (legacyPrefixCellPtr ↦ₘ cellOld) **
        bytesRegion legacySuffixOutPtr (List.replicate n 0) **
        ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22 **
        legacyTailExtension n ** F)
      (((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
        ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 2)) **
        ((.x5 : Reg) ↦ᵣ (legacySuffixOutPtr + BitVec.ofNat 64 n)) **
        ((.x6 : Reg) ↦ᵣ (legacySuffixChainEncPtr + BitVec.ofNat 64 n)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x22 : Reg) ↦ᵣ (v21 + (BitVec.ofNat 64 n + 2))) **
        ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
        bytesRegion legacyLinkedChainEncPtr
          (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
            legacyChainEncOld.drop n) **
        bytesRegion legacyPrefixOutPtr
          (rlpListPrefix (v21 + (BitVec.ofNat 64 n + 2)).toNat) **
        (legacyPrefixCellPtr ↦ₘ
          BitVec.ofNat 64
            (rlpListPrefix (v21 + (BitVec.ofNat 64 n + 2)).toNat).length) **
        bytesRegion legacySuffixOutPtr (legacyTailOutputBytes chainId) **
        (legacyPrefixBssTail (v21 + (BitVec.ofNat 64 n + 2)) ** F)) := by
  intro n uintFuel prefixFuel
  let payloadLen : Word := v21 + (BitVec.ofNat 64 n + 2)
  let prefixBytes : List (BitVec 8) := rlpListPrefix payloadLen.toNat
  let bssTail : Assertion := legacyPrefixBssTail payloadLen
  let Fprefix : Assertion :=
    bytesRegion legacyPrefixOutPtr (List.replicate 16 (0 : BitVec 8)) **
      (legacyPrefixCellPtr ↦ₘ cellOld) **
      bytesRegion legacySuffixOutPtr (List.replicate n 0) **
      legacyTailExtension n ** F
  let Fuint : Assertion := Fprefix ** ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22
  let Farg : Assertion :=
    ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31) **
      bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** Fuint
  let Floop : Assertion :=
    ((.x1 : Reg) ↦ᵣ v1) ** ((.x10 : Reg) ↦ᵣ v10) **
      ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** Farg
  have htail_pc : (legacyTailExtension n).pcFree := legacyTailExtension_pcFree n
  have hFprefix : Fprefix.pcFree := by
    unfold Fprefix
    pcf
    all_goals first | exact htail_pc | exact hF
  have hFuint : Fuint.pcFree := by
    unfold Fuint
    exact pcFree_sepConj hFprefix
      (pcFree_sepConj pcFree_regIs pcFree_regOwn)
  have hFarg : Farg.pcFree := by
    unfold Farg
    pcf
    all_goals first | exact hFuint | exact htail_pc | exact hF |
      exact (pcFree_sepConj pcFree_regIs pcFree_regOwn)
  have hFloop : Floop.pcFree := by
    unfold Floop
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs hFarg)))
  have hloop := legacyChainLoopSetup_spec v5 v6 v7 v28 chainId Floop hFloop
    halign hover hvalid hbound
  have harg := legacyChainArgSetup_spec v1 v10 v11 v12 chainId Farg hFarg
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      simp only [Floop, Farg, Fuint, Fprefix] at hq ⊢
      xcancel_struct hq)
    hloop harg
  have hu := legacyChainUintCall_spec v1 v29 v30 v31 chainId Fuint hFuint
  have c2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      unfold legacyChainUintPre
      simp only [Fuint, Farg, Fprefix] at hq ⊢
      xcancel_struct hq)
    c1 hu
  have hp := legacyPrefixCopyThenTerminator_split_spec chainId v21 cellOld F hF
    h_out_valid
  have c3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      simp only [legacyChainUintPost, Fuint, Fprefix] at hq ⊢
      xcancel_struct hq)
    c2 hp
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [Floop, Farg, Fuint, Fprefix, n] at hp ⊢
      xcancel_struct hp)
    (fun _ hq => by
      simp only [n] at hq ⊢
      xcancel_struct hq)
    c3

/-! ## Descriptor post to KSS call pre

    The descriptor setup and the Keccak-segments leaf use the same flat table
    but expose it at different assertion shapes.  Keep the caller-owned
    regions and ABI/frame resources in one explicit frame while converting
    the three concrete descriptor registers to the ownership required by
    `kssCallerPre`.  This is only a representation bridge: it introduces no
    additional machine precondition.  These are internal decomposition
    adapters, not a caller-facing source contract: their payload equation is
    the whole-input relation supplied by the top-level `KssInputSourceSpec`
    path below. -/

abbrev legacyKssSegs (prefixBytes payloadBytes suffixBytes : List (BitVec 8))
    (inPtr hdrLen : Word) : List KssSeg :=
  [(legacyPrefixOutPtr, prefixBytes),
    (inPtr + hdrLen, payloadBytes),
    (legacySuffixOutPtr, suffixBytes)]

def legacyKssCallInputs
    (sp0 newSp v5 v6 v9 v18 v22 outputBase : Word)
    (os prefixBytes payloadBytes suffixBytes : List (BitVec 8))
    (inPtr hdrLen : Word) (source : KssSource) : Assertion :=
  ((.x2 : Reg) ↦ᵣ sp0) **
    ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
    ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
    ((.x22 : Reg) ↦ᵣ v22) ** ((.x28 : Reg) ↦ᵣ (0 : Word)) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    frameSlotsOwn kssFrame newSp **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x17 ** bytesRegion KssZk3 os **
    bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) **
    source.region legacyPrefixOutPtr prefixBytes **
    source.region (inPtr + hdrLen) payloadBytes **
    source.region legacySuffixOutPtr suffixBytes

def legacyKssBridgeFrame (vOld prefixLen : Word) (R : Assertion) : Assertion :=
  (.x1 ↦ᵣ vOld) ** (legacyPrefixCellPtr ↦ₘ prefixLen) ** R

/- The descriptor post supplies the prefix-length cell; its frame supplies only
   the saved return register and the residual `R`, so no resource is owned
   twice when this bridge is composed with the KSS call pre. -/

theorem legacyKssBridgeFrame_pcFree
    (vOld prefixLen : Word) (R : Assertion) (hR : R.pcFree) :
    (legacyKssBridgeFrame vOld prefixLen R).pcFree := by
  unfold legacyKssBridgeFrame
  exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_memIs hR)

theorem legacyKss_open_regs_28_31
    (v28 v29 v30 v31 : Word) (P : Assertion) (h : PartialState)
    (hq : (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) ** P) h) :
    (regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** P) h := by
  have h28 :
      ((.x28 ↦ᵣ v28) **
        ((.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by
    xperm_hyp hq
  have o28 := sepConj_mono_left (regIs_to_regOwn .x28 v28) h h28
  have h29 :
      ((.x29 ↦ᵣ v29) ** regOwn .x28 ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** P) h := by
    xperm_hyp o28
  have o29 := sepConj_mono_left (regIs_to_regOwn .x29 v29) h h29
  have h30 :
      ((.x30 ↦ᵣ v30) ** regOwn .x29 ** regOwn .x28 **
        (.x31 ↦ᵣ v31) ** P) h := by
    xperm_hyp o29
  have o30 := sepConj_mono_left (regIs_to_regOwn .x30 v30) h h30
  have h31 :
      ((.x31 ↦ᵣ v31) ** regOwn .x30 ** regOwn .x29 **
        regOwn .x28 ** P) h := by
    xperm_hyp o30
  have o31 := sepConj_mono_left (regIs_to_regOwn .x31 v31) h h31
  xperm_hyp o31

theorem legacyKssDescriptorPost_to_callPre
    (prefixLen inPtr hdrLen payloadLen outputBase suffixLen : Word)
    (sp0 newSp vOld v5 v6 v9 v18 v22 : Word)
    (prefixBytes payloadBytes suffixBytes input os : List (BitVec 8))
    (A R : Assertion)
    (source : KssSource := kssDefaultSource)
    (hprefixLen : BitVec.ofNat 64 prefixBytes.length = prefixLen)
    (hpayloadLen : BitVec.ofNat 64 payloadBytes.length = payloadLen)
    (hsuffixLen : BitVec.ofNat 64 suffixBytes.length = suffixLen)
    (hsourcePrefix : source.region legacyPrefixOutPtr prefixBytes =
      bytesRegion legacyPrefixOutPtr prefixBytes)
    (hsourcePayload : source.region (inPtr + hdrLen) payloadBytes =
      bytesRegion inPtr input)
    (hsourceSuffix : source.region legacySuffixOutPtr suffixBytes =
      bytesRegion legacySuffixOutPtr suffixBytes) :
    ∀ h,
      legacyKssDescriptorPost prefixLen inPtr hdrLen payloadLen outputBase
        suffixLen (A ** legacyKssCallInputs sp0 newSp v5 v6 v9 v18 v22
          outputBase os prefixBytes payloadBytes suffixBytes inPtr hdrLen source **
          ((.x1 : Reg) ↦ᵣ vOld) ** R) h →
      (legacyKssCallPre sp0 newSp legacyKssSegsBase outputBase
        (legacyKssSegs prefixBytes payloadBytes suffixBytes inPtr hdrLen) os
        v5 v6 suffixLen inPtr v9 v18 outputBase hdrLen payloadLen v22 A source **
        legacyKssBridgeFrame vOld prefixLen R) h := by
  intro h hp
  have hp0 := hp
  simp only [legacyKssDescriptorPost, legacyKssCallPre, legacyKssSregs,
    legacyKssSegs, legacyKssCallInputs, legacyKssBridgeFrame, kssCallerPre,
    kssSegsIs_cons, kssSegsIs_nil, kssFreeTemps, regOwns_cons,
    regOwns_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    sepConj_emp_right'] at hp0 ⊢
  rw [hsourcePrefix, hsourcePayload, hsourceSuffix] at hp0
  rw [show (legacyKssSegsBase + 16 : Word) + 16 = legacyKssSegsBase + 32
      from by bv_omega,
    show (legacyKssSegsBase + 32 : Word) + 8 = legacyKssSegsBase + 40
      from by bv_omega,
    show (legacyKssSegsBase + 16 : Word) + 8 = legacyKssSegsBase + 24
      from by bv_omega]
  rw [hprefixLen, hpayloadLen, hsuffixLen,
    hsourcePrefix, hsourcePayload, hsourceSuffix]
  have hzero : (0 : Word) = BitVec.ofNat 64 0 := by rfl
  rw [hzero] at hp0
  have hthree : (3 : Word) = BitVec.ofNat 64 3 := by rfl
  rw [hthree] at hp0
  let Rest : Assertion :=
    ((.x8 : Reg) ↦ᵣ inPtr) ** ((.x19 : Reg) ↦ᵣ outputBase) **
      ((.x20 : Reg) ↦ᵣ hdrLen) ** ((.x21 : Reg) ↦ᵣ payloadLen) **
      ((.x7 : Reg) ↦ᵣ suffixLen) **
      ((.x10 : Reg) ↦ᵣ legacyKssSegsBase) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 3) **
      ((.x12 : Reg) ↦ᵣ outputBase) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
      ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
      ((legacyKssSegsBase + 32) ↦ₘ legacySuffixOutPtr) **
      ((legacyKssSegsBase + 40) ↦ₘ suffixLen) ** A **
      ((.x1 : Reg) ↦ᵣ vOld) ** ((.x2 : Reg) ↦ᵣ sp0) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
      ((.x22 : Reg) ↦ᵣ v22) **
      ((.x0 : Reg) ↦ᵣ BitVec.ofNat 64 0) ** frameSlotsOwn kssFrame newSp **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x17 ** bytesRegion KssZk3 os **
      bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) **
      bytesRegion legacyPrefixOutPtr prefixBytes **
      bytesRegion inPtr input **
      bytesRegion legacySuffixOutPtr suffixBytes ** R
  have hpre :
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
        ((.x29 : Reg) ↦ᵣ prefixLen) **
        ((.x30 : Reg) ↦ᵣ legacyKssSegsBase) **
        ((.x31 : Reg) ↦ᵣ legacySuffixOutPtr) **
        ((.x8 : Reg) ↦ᵣ inPtr) ** ((.x19 : Reg) ↦ᵣ outputBase) **
        ((.x20 : Reg) ↦ᵣ hdrLen) ** ((.x21 : Reg) ↦ᵣ payloadLen) **
        ((.x7 : Reg) ↦ᵣ suffixLen) **
        ((.x10 : Reg) ↦ᵣ legacyKssSegsBase) **
          ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 3) **
        ((.x12 : Reg) ↦ᵣ outputBase) **
        (legacyPrefixCellPtr ↦ₘ prefixLen) **
        (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
        ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
        ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
        ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
        ((legacyKssSegsBase + 32) ↦ₘ legacySuffixOutPtr) **
        ((legacyKssSegsBase + 40) ↦ₘ suffixLen) ** A **
        ((.x1 : Reg) ↦ᵣ vOld) ** ((.x2 : Reg) ↦ᵣ sp0) **
        ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
        ((.x22 : Reg) ↦ᵣ v22) ** ((.x0 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
        frameSlotsOwn kssFrame newSp ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        bytesRegion KssZk3 os **
        bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) **
        bytesRegion legacyPrefixOutPtr prefixBytes **
        bytesRegion inPtr input **
        bytesRegion legacySuffixOutPtr suffixBytes ** R) h := by
      xcancel_struct hp0
  have hpre' :
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
        ((.x29 : Reg) ↦ᵣ prefixLen) **
        ((.x30 : Reg) ↦ᵣ legacyKssSegsBase) **
    ((.x31 : Reg) ↦ᵣ legacySuffixOutPtr) ** Rest) h := by
    dsimp only [Rest]
    xperm_hyp hpre
  have hp2 := legacyKss_open_regs_28_31 (BitVec.ofNat 64 0) prefixLen
    legacyKssSegsBase legacySuffixOutPtr Rest h hpre'
  dsimp only [Rest] at hp2
  rw [hzero]
  xperm_hyp hp2

/-! ## Successful status tail

    The KSS call returns with `a0 = 0`.  The two instructions after the call
    rewrite that value and jump over the common failure arm.  Keep this tail
    separate from the call adapter so the latter can be framed with the exact
    linked post produced by `zkvm_keccak256_segments`. -/

theorem legacySuccessLi_spec (v10 : Word) :
    cpsTripleWithin 1 (legacyH + 428) (legacyH + 432) legacyFullCode
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_gen_within .x10 v10 (0 : Word)
    (legacyH + 428) (by decide)
  rw [show (legacyH + 428 : Word) + 4 = legacyH + 432 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 428) 107 (.LI .x10 (0 : Word)) (by decide)
      (by decide) (by intro h; rfl)) h0

theorem legacySuccessSkipFail_spec (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 1 (legacyH + 432) legacyBodyExit legacyFullCode P P := by
  have h0 := jal_x0_spec_gen_within (8 : BitVec 21) (legacyH + 432)
  rw [show (legacyH + 432 : Word) + signExtend21 (8 : BitVec 21) =
      legacyBodyExit from by unfold legacyBodyExit legacyH; decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 432) 108 (.JAL .x0 (8 : BitVec 21))
      (by decide) (by decide) (by intro h; rfl)) h0
  have hF := cpsTripleWithin_frameL P hP l0
  exact (sepConj_emp_right' P) ▸ hF

theorem legacySuccessStatus_spec (v10 : Word) :
    cpsTripleWithin 2 (legacyH + 428) legacyBodyExit legacyFullCode
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ (0 : Word)) := by
  have hli := legacySuccessLi_spec v10
  have hjal := legacySuccessSkipFail_spec (.x10 ↦ᵣ (0 : Word)) (by pcf)
  exact cpsTripleWithin_seq_same_cr hli hjal

theorem legacyKssCallThenSuccess_spec
    (vOld sp0 segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource) :
    let ret := legacyKssJalPC + 4
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := 19 + kssBodyFuelMulti segs
    cpsTripleWithin ((1 + fuel) + 2) legacyKssJalPC legacyBodyExit legacyFullCode
      (((.x1 ↦ᵣ vOld) **
        (legacyKssCallPre sp0 newSp segsBase outputBase segs os
          v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A source ** F)))
      (((.x1 ↦ᵣ ret) **
        (legacyKssCallPost sp0 newSp ret segsBase outputBase segs
          v8 v9 v18 v19 v20 v21 v22 A source ** F))) := by
  intro ret newSp fuel
  have hcall := legacy_kss_callWithin vOld sp0 segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A F hA hF hos hcount hsegs source
  let Rest : Assertion :=
    (.x1 ↦ᵣ ret) **
      ((.x2 ↦ᵣ sp0) ** legacyKssSregs v8 v9 v18 v19 v20 v21 v22 **
        frameSlotsSaved kssFrame newSp
          (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
        ((regOwn .x11) ** (regOwn .x12) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          regOwns kssFreeTemps **
          bytesRegion KssZk3
            (kssFinalState
              (kssAbsorbed (kssMsg segs) (kssMsg segs).length)
              (kssFill (kssMsg segs).length)) **
          bytesRegion outputBase (Stateless.SpecRef.keccak256 (kssMsg segs)) **
          kssSegsIs segsBase segs source ** A ** F))
  have hRest : Rest.pcFree := by
    unfold Rest
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj (legacyKssSregs_pcFree _ _ _ _ _ _ _) ?_
    refine pcFree_sepConj
      (pcFree_frameSlotsSaved kssFrame newSp
        (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22)) ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj (by pcf) ?_
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj (kssSegsIs_pcFree segsBase segs source) ?_
    exact pcFree_sepConj hA hF
  have hsucc := legacySuccessStatus_spec (0 : Word)
  have hsuccF := cpsTripleWithin_frameR Rest hRest hsucc
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [Rest, legacyKssCallPost, legacyKssSregs, kssCallerPost_multi] at hp ⊢
      xperm_hyp hp) hcall hsuccF
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      simp only [Rest, legacyKssCallPost, legacyKssSregs, kssCallerPost_multi] at hq ⊢
      xperm_hyp hq) c

/-! ## Descriptor setup → KSS call → success

    This is the first whole tail composition.  The descriptor post is reshaped
    at the actual call boundary, then the linked KSS call and success
    reconvergence are applied without introducing a fresh callee premise. -/

theorem legacyDescriptorThenKssSuccess_spec
    (prefixLen inPtr hdrLen payloadLen outputBase suffixLen : Word)
    (vOld sp0 v5 v6 v9 v18 v22 : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (prefixBytes payloadBytes suffixBytes input os : List (BitVec 8))
    (A R : Assertion) (hA : A.pcFree) (hR : R.pcFree)
    (hprefixLen : BitVec.ofNat 64 prefixBytes.length = prefixLen)
    (hpayloadLen : BitVec.ofNat 64 payloadBytes.length = payloadLen)
    (hsuffixLen : BitVec.ofNat 64 suffixBytes.length = suffixLen)
    (hos : os.length = 200)
    (hcount : (legacyKssSegs prefixBytes payloadBytes suffixBytes inPtr hdrLen).length < 2 ^ 64)
    (hsegs : ∀ s ∈ legacyKssSegs prefixBytes payloadBytes suffixBytes inPtr hdrLen,
      s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource)
    (hsourcePrefix : source.region legacyPrefixOutPtr prefixBytes =
      bytesRegion legacyPrefixOutPtr prefixBytes)
    (hsourcePayload : source.region (inPtr + hdrLen) payloadBytes =
      bytesRegion inPtr input)
    (hsourceSuffix : source.region legacySuffixOutPtr suffixBytes =
      bytesRegion legacySuffixOutPtr suffixBytes) :
    let segs := legacyKssSegs prefixBytes payloadBytes suffixBytes inPtr hdrLen
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := 19 + kssBodyFuelMulti segs
    cpsTripleWithin (21 + ((1 + fuel) + 2)) (legacyH + 340) legacyBodyExit
      legacyFullCode
      (regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase suffixLen
          (0 : Word) legacyPrefixOutPtr legacyPrefixCellPtr old0 old1 old2 old3 old4 old5
          (A ** legacyKssCallInputs sp0 newSp v5 v6 v9 v18 v22 outputBase os
            prefixBytes payloadBytes suffixBytes inPtr hdrLen source **
            (.x1 ↦ᵣ vOld) ** R))
      (((.x1 ↦ᵣ (legacyKssJalPC + 4)) **
        legacyKssCallPost sp0 newSp (legacyKssJalPC + 4) legacyKssSegsBase outputBase segs
          inPtr v9 v18 outputBase hdrLen payloadLen v22 A source) **
        (legacyPrefixCellPtr ↦ₘ prefixLen) ** R) := by
  intro segs newSp fuel
  let Fdesc : Assertion :=
    A ** legacyKssCallInputs sp0 newSp v5 v6 v9 v18 v22 outputBase os
      prefixBytes payloadBytes suffixBytes inPtr hdrLen source **
      (.x1 ↦ᵣ vOld) ** R
  have hFdesc : Fdesc.pcFree := by
    unfold Fdesc
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_frameSlotsOwn _ _
      | exact source.pcFree _ _
      | exact bytesRegion_pcFree _ _
      | exact hA
      | exact hR
      | exact (by pcf)
  have hdesc := legacyKssDescriptorSetup_regOwn_spec prefixLen inPtr hdrLen payloadLen
    outputBase suffixLen (0 : Word) legacyPrefixOutPtr legacyPrefixCellPtr
    old0 old1 old2 old3 old4 old5 Fdesc hFdesc
  have hdescCall : cpsTripleWithin 21 (legacyH + 340) (legacyH + 424)
      legacyFullCode
      (regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase suffixLen
          (0 : Word) legacyPrefixOutPtr legacyPrefixCellPtr old0 old1 old2 old3 old4 old5
          Fdesc)
      (legacyKssCallPre sp0 newSp legacyKssSegsBase outputBase segs os
        v5 v6 suffixLen inPtr v9 v18 outputBase hdrLen payloadLen v22 A source **
        legacyKssBridgeFrame vOld prefixLen R) := by
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        exact legacyKssDescriptorPost_to_callPre prefixLen inPtr hdrLen payloadLen outputBase
          suffixLen sp0 newSp vOld v5 v6 v9 v18 v22 prefixBytes payloadBytes suffixBytes input os
          A R source hprefixLen hpayloadLen hsuffixLen hsourcePrefix hsourcePayload hsourceSuffix
          h hq)
      hdesc
  let Fcall : Assertion := (legacyPrefixCellPtr ↦ₘ prefixLen) ** R
  have hFcall : Fcall.pcFree := by
    unfold Fcall
    exact pcFree_sepConj pcFree_memIs hR
  have hkss := legacyKssCallThenSuccess_spec vOld sp0 legacyKssSegsBase outputBase segs os
    v5 v6 suffixLen inPtr v9 v18 outputBase hdrLen payloadLen v22 A Fcall hA hFcall
    hos hcount hsegs source
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [legacyKssBridgeFrame, Fcall] at hp ⊢
      xperm_hyp hp) hdescCall hkss
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Fdesc] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [Fcall] at hq ⊢
      xperm_hyp hq) hseq

/-! The first complete success-body composition.  The Nth result has already
    supplied `offVal` and `lenVal`; this theorem runs the two linked table
    loads, computes the payload length, and then consumes the chain/prefix
    tail.  The descriptor/KSS tail is deliberately left as the next boundary,
    so this lemma is useful for checking the exact resources crossing H+340. -/

theorem legacyBodyArithmeticThenChain_spec
    (v1 v5 v6 v7 v10 v11 v12 chainId v28 v29 v30 v31 v21 : Word)
    (offVal lenVal hdrLen cellOld : Word) (F : Assertion) (hF : F.pcFree)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0)
    (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess
        (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    let n :=
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
    let uintFuel :=
      1 + (8 * 6 + 7 *
        (8 - RlpEncodeUintBeSAsm.reubZeros (chainBytes chainId) 0 8) + 17)
    let prefixFuel := 8 + (1 + tshPrefixFuel) + 8 +
      (n * (6 + 1) + 1) + 4
    cpsTripleWithin (8 + (68 + 8 + uintFuel + prefixFuel))
      (legacyH + 128) (legacyH + 340) legacyFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x7 : Reg) ↦ᵣ v7) ** ((.x20 : Reg) ↦ᵣ hdrLen) **
        ((.x21 : Reg) ↦ᵣ v21) **
        (legacyLinkedNthOffPtr ↦ₘ offVal) **
        (legacyLinkedNthLenPtr ↦ₘ lenVal) **
        ((.x1 : Reg) ↦ᵣ v1) ** ((.x10 : Reg) ↦ᵣ v10) **
        ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x18 : Reg) ↦ᵣ chainId) ** ((.x28 : Reg) ↦ᵣ v28) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (List.replicate 8 0) **
        bytesRegion legacyLinkedChainEncPtr legacyChainEncOld **
        bytesRegion legacyPrefixOutPtr (List.replicate 16 0) **
        (legacyPrefixCellPtr ↦ₘ cellOld) **
        bytesRegion legacySuffixOutPtr (List.replicate n 0) **
        regOwn .x22 ** legacyTailExtension n ** F)
      (((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
        ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 2)) **
        ((.x5 : Reg) ↦ᵣ (legacySuffixOutPtr + BitVec.ofNat 64 n)) **
        ((.x6 : Reg) ↦ᵣ (legacySuffixChainEncPtr + BitVec.ofNat 64 n)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x21 : Reg) ↦ᵣ ((offVal + lenVal) - hdrLen)) **
        ((.x22 : Reg) ↦ᵣ (((offVal + lenVal) - hdrLen) +
          (BitVec.ofNat 64 n + 2))) **
        ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
        bytesRegion legacyLinkedChainEncPtr
          (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
            legacyChainEncOld.drop n) **
        bytesRegion legacyPrefixOutPtr
          (rlpListPrefix (((offVal + lenVal) - hdrLen) +
            (BitVec.ofNat 64 n + 2)).toNat) **
        (legacyPrefixCellPtr ↦ₘ
          BitVec.ofNat 64
            (rlpListPrefix (((offVal + lenVal) - hdrLen) +
              (BitVec.ofNat 64 n + 2)).toNat).length) **
        bytesRegion legacySuffixOutPtr (legacyTailOutputBytes chainId) **
        legacyPrefixBssTail (((offVal + lenVal) - hdrLen) +
          (BitVec.ofNat 64 n + 2)) **
        ((.x20 : Reg) ↦ᵣ hdrLen) **
        (legacyLinkedNthOffPtr ↦ₘ offVal) **
        (legacyLinkedNthLenPtr ↦ₘ lenVal) ** F) := by
  intro n uintFuel prefixFuel
  let Farith : Assertion :=
    ((.x1 : Reg) ↦ᵣ v1) ** ((.x10 : Reg) ↦ᵣ v10) **
      ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x18 : Reg) ↦ᵣ chainId) ** ((.x28 : Reg) ↦ᵣ v28) **
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion legacyLinkedChainPtr (List.replicate 8 0) **
      bytesRegion legacyLinkedChainEncPtr legacyChainEncOld **
      bytesRegion legacyPrefixOutPtr (List.replicate 16 0) **
      (legacyPrefixCellPtr ↦ₘ cellOld) **
      bytesRegion legacySuffixOutPtr (List.replicate n 0) **
      regOwn .x22 ** legacyTailExtension n ** F
  have hFarith : Farith.pcFree := by
    unfold Farith
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj pcFree_memIs ?_
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj (legacyTailExtension_pcFree n) ?_
    exact hF
  have harith :=
    EvmAsm.Codegen.TxSigningHashLegacyBodyCompose.legacyBodyPayloadArithmetic_spec
      v5 v6 v7 v21 offVal lenVal hdrLen Farith hFarith
  let Fchain : Assertion :=
    ((.x20 : Reg) ↦ᵣ hdrLen) **
      (legacyLinkedNthOffPtr ↦ₘ offVal) **
      (legacyLinkedNthLenPtr ↦ₘ lenVal) ** F
  have hFchain : Fchain.pcFree := by
    unfold Fchain
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_memIs ?_
    exact pcFree_sepConj pcFree_memIs hF
  have hchain := legacyChainThenPrefixTerminator_split_spec
    v1 legacyLinkedNthLenPtr (offVal + lenVal) lenVal v10 v11 v12 v28 chainId
    ((offVal + lenVal) - hdrLen) v29 v30 v31 cellOld Fchain hFchain
    halign hover hvalid hbound h_out_valid
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [Farith, Fchain, n] at hp ⊢
      xcancel_struct hp)
    harith hchain
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [Farith, n] at hp ⊢
      xcancel_struct hp)
    (fun _ hq => by
      simp only [Fchain, n] at hq ⊢
      xcancel_struct hq)
    hseq

/-! ## The K146 chain boundary and the linked KSS tail

    These small data definitions keep the descriptor composition at the same
    names as the emitted chain state.  KSS's payload segment is backed by the
    whole caller-owned input through `KssInputSourceSpec`; the generated
    prefix/suffix regions remain separate source views. -/

def legacyKssBodyChainLen (chainId : Word) : Word :=
  BitVec.ofNat 64 (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length

def legacyKssBodyPayloadEnd (chainId payloadBase : Word) : Word :=
  payloadBase + (legacyKssBodyChainLen chainId + 2)

def legacyKssBodyPrefixBytes (chainId payloadBase : Word) : List (BitVec 8) :=
  rlpListPrefix (legacyKssBodyPayloadEnd chainId payloadBase).toNat

def legacyKssBodyPrefixLen (chainId payloadBase : Word) : Word :=
  BitVec.ofNat 64 (legacyKssBodyPrefixBytes chainId payloadBase).length

def legacyKssBodySuffixBytes (chainId : Word) : List (BitVec 8) :=
  legacyTailOutputBytes chainId

def legacyKssBodySuffixLen (chainId : Word) : Word :=
  BitVec.ofNat 64
    ((RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2)

def legacyKssBodySegs (chainId payloadBase inPtr hdrLen : Word)
    (payloadBytes : List (BitVec 8)) : List KssSeg :=
  legacyKssSegs (legacyKssBodyPrefixBytes chainId payloadBase) payloadBytes
    (legacyKssBodySuffixBytes chainId) inPtr hdrLen

def legacyKssBodyProducedResidual
    (chainId payloadBase offVal lenVal : Word) : Assertion :=
  bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
    bytesRegion legacyLinkedChainEncPtr
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
        legacyChainEncOld.drop
          (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length) **
    legacyPrefixBssTail (legacyKssBodyPayloadEnd chainId payloadBase) **
    (legacyLinkedNthOffPtr ↦ₘ offVal) **
    (legacyLinkedNthLenPtr ↦ₘ lenVal)

def legacyKssBodyExtra
    (inPtr outputBase sp0 v9 : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8))
    (A R : Assertion) : Assertion :=
  ((.x8 : Reg) ↦ᵣ inPtr) ** ((.x19 : Reg) ↦ᵣ outputBase) **
    (legacyKssSegsBase ↦ₘ old0) **
    ((legacyKssSegsBase + 8) ↦ₘ old1) **
    ((legacyKssSegsBase + 16) ↦ₘ old2) **
    ((legacyKssSegsBase + 24) ↦ₘ old3) **
    ((legacyKssSegsBase + 32) ↦ₘ old4) **
    ((legacyKssSegsBase + 40) ↦ₘ old5) **
    ((.x2 : Reg) ↦ᵣ sp0) ** ((.x9 : Reg) ↦ᵣ v9) **
    frameSlotsOwn kssFrame (sp0 + signExtend12 ((-64 : BitVec 12))) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x17 ** bytesRegion KssZk3 os **
    bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) **
    bytesRegion inPtr input ** A ** R

/-! The descriptor setup and KSS call are now consumed by the actual H+340
    chain state.  No fresh callee premise is introduced: the only KSS facts
    are the existing segment geometry/source facts, and the produced chain
    buffers/table cells are retained in the residual.  This lower-level
    adapter remains source-parametric for internal decomposition; no external
    custom caller is present in the current tree. -/

theorem legacyChainDescriptorThenKssSuccess_spec
    (chainId payloadBase inPtr hdrLen outputBase sp0 v9 : Word)
    (offVal lenVal old0 old1 old2 old3 old4 old5 : Word)
    (payloadBytes input os : List (BitVec 8))
    (A R : Assertion) (hA : A.pcFree) (hR : R.pcFree)
    (hpayloadLen : BitVec.ofNat 64 payloadBytes.length = payloadBase)
    (hos : os.length = 200)
    (hcount : (legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes).length <
      2 ^ 64)
    (hsegs : ∀ s ∈ legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes,
      s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource)
    (hsourcePrefix : source.region legacyPrefixOutPtr
        (legacyKssBodyPrefixBytes chainId payloadBase) =
      bytesRegion legacyPrefixOutPtr (legacyKssBodyPrefixBytes chainId payloadBase))
    (hsourcePayload : source.region (inPtr + hdrLen) payloadBytes =
      bytesRegion inPtr input)
    (hsourceSuffix : source.region legacySuffixOutPtr
        (legacyKssBodySuffixBytes chainId) =
      bytesRegion legacySuffixOutPtr (legacyKssBodySuffixBytes chainId)) :
    cpsTripleWithin
      (21 + ((1 + (19 + kssBodyFuelMulti
        (legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes))) + 2))
      (legacyH + 340) legacyBodyExit legacyFullCode
      (((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
        ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
        ((.x7 : Reg) ↦ᵣ legacyKssBodySuffixLen chainId) **
        ((.x5 : Reg) ↦ᵣ
          (legacySuffixOutPtr + legacyKssBodyChainLen chainId)) **
        ((.x6 : Reg) ↦ᵣ
          (legacySuffixChainEncPtr + legacyKssBodyChainLen chainId)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x21 : Reg) ↦ᵣ payloadBase) **
        ((.x22 : Reg) ↦ᵣ legacyKssBodyPayloadEnd chainId payloadBase) **
        ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes chainId payloadBase) **
        (legacyPrefixCellPtr ↦ₘ
          legacyKssBodyPrefixLen chainId payloadBase) **
        bytesRegion legacySuffixOutPtr (legacyKssBodySuffixBytes chainId) **
        ((.x20 : Reg) ↦ᵣ hdrLen) **
        legacyKssBodyProducedResidual chainId payloadBase offVal lenVal **
        legacyKssBodyExtra inPtr outputBase sp0 v9
          old0 old1 old2 old3 old4 old5 input os A R)
      (((.x1 : Reg) ↦ᵣ (legacyKssJalPC + 4)) **
        legacyKssCallPost
          sp0 (sp0 + signExtend12 ((-64 : BitVec 12)))
          (legacyKssJalPC + 4) legacyKssSegsBase outputBase
          (legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes)
          inPtr v9 chainId outputBase hdrLen payloadBase
          (legacyKssBodyPayloadEnd chainId payloadBase) A source **
        (legacyPrefixCellPtr ↦ₘ legacyKssBodyPrefixLen chainId payloadBase) **
        legacyKssBodyProducedResidual chainId payloadBase offVal lenVal ** R) := by
  have hprefixLen :
      BitVec.ofNat 64 (legacyKssBodyPrefixBytes chainId payloadBase).length =
        legacyKssBodyPrefixLen chainId payloadBase := by
    rfl
  have hsuffixLen :
      BitVec.ofNat 64 (legacyKssBodySuffixBytes chainId).length =
        legacyKssBodySuffixLen chainId := by
    unfold legacyKssBodySuffixBytes legacyKssBodySuffixLen
    rw [legacyTailOutputBytes_length]
  have hcount' :
      (legacyKssSegs (legacyKssBodyPrefixBytes chainId payloadBase) payloadBytes
        (legacyKssBodySuffixBytes chainId) inPtr hdrLen).length < 2 ^ 64 := by
    simpa only [legacyKssBodySegs] using hcount
  have hsegs' :
      ∀ s ∈ legacyKssSegs (legacyKssBodyPrefixBytes chainId payloadBase) payloadBytes
        (legacyKssBodySuffixBytes chainId) inPtr hdrLen,
        s.2.length < 2 ^ 64 ∧
          (∀ i, i < s.2.length →
            s.1.toNat + i < 2 ^ 64 ∧
            isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true) := by
    simpa only [legacyKssBodySegs] using hsegs
  let Rdesc : Assertion :=
    legacyKssBodyProducedResidual chainId payloadBase offVal lenVal ** R
  have hRprod :
      (legacyKssBodyProducedResidual chainId payloadBase offVal lenVal).pcFree := by
    unfold legacyKssBodyProducedResidual
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj (legacyPrefixBssTail_pcFree _) ?_
    refine pcFree_sepConj pcFree_memIs ?_
    exact pcFree_memIs
  have hRdesc : Rdesc.pcFree := by
    unfold Rdesc
    exact pcFree_sepConj hRprod hR
  have hdesc := legacyDescriptorThenKssSuccess_spec
    (legacyKssBodyPrefixLen chainId payloadBase) inPtr hdrLen payloadBase outputBase
    (legacyKssBodySuffixLen chainId)
    (legacyPrefixJalPC + 4) sp0
    (legacySuffixOutPtr + legacyKssBodyChainLen chainId)
    (legacySuffixChainEncPtr + legacyKssBodyChainLen chainId)
    v9 chainId (legacyKssBodyPayloadEnd chainId payloadBase)
    old0 old1 old2 old3 old4 old5
    (legacyKssBodyPrefixBytes chainId payloadBase) payloadBytes
    (legacyKssBodySuffixBytes chainId) input os A Rdesc hA hRdesc
    hprefixLen hpayloadLen hsuffixLen hos hcount' hsegs'
    source hsourcePrefix hsourcePayload hsourceSuffix
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [legacyKssDescriptorRest, legacyKssCallInputs,
        legacyKssBodyProducedResidual, legacyKssBodyExtra, Rdesc] at hp ⊢
      rw [hsourcePrefix, hsourcePayload, hsourceSuffix]
      xperm_hyp hp)
    (fun _ hq => by
      simp only [legacyKssCallPost, legacyKssBodyProducedResidual,
        Rdesc] at hq ⊢
      dsimp only [legacyKssBodySegs] at hq ⊢
      xperm_hyp hq)
    hdesc

/-! The complete K146 body precondition, before the arithmetic/chain segment.
    The descriptor/table resources and the KSS caller frame occur here exactly
    once; the chain/prefix/suffix resources are consumed by the first segment
    and are not repeated in `legacyKssBodyExtra`. -/

def legacyKssBodyInitial
    (v1 v5 v6 v7 v10 v11 v12 chainId v28 v29 v30 v31 v21 : Word)
    (offVal lenVal hdrLen cellOld inPtr outputBase sp0 v9 : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8)) (A R : Assertion) : Assertion :=
  ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
    ((.x20 : Reg) ↦ᵣ hdrLen) ** ((.x21 : Reg) ↦ᵣ v21) **
    (legacyLinkedNthOffPtr ↦ₘ offVal) ** (legacyLinkedNthLenPtr ↦ₘ lenVal) **
    ((.x1 : Reg) ↦ᵣ v1) ** ((.x10 : Reg) ↦ᵣ v10) **
    ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
    ((.x18 : Reg) ↦ᵣ chainId) ** ((.x28 : Reg) ↦ᵣ v28) **
    ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
    ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion legacyLinkedChainPtr (List.replicate 8 0) **
    bytesRegion legacyLinkedChainEncPtr legacyChainEncOld **
    bytesRegion legacyPrefixOutPtr (List.replicate 16 (0 : BitVec 8)) **
    (legacyPrefixCellPtr ↦ₘ cellOld) **
    bytesRegion legacySuffixOutPtr
      (List.replicate (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length 0) **
    regOwn .x22 **
    legacyTailExtension (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length **
    legacyKssBodyExtra inPtr outputBase sp0 v9
      old0 old1 old2 old3 old4 old5 input os A R

def legacyKssBodyFinal
    (chainId payloadBase inPtr hdrLen outputBase sp0 v9 offVal lenVal : Word)
    (payloadBytes : List (BitVec 8)) (A R : Assertion)
    (source : KssSource := kssDefaultSource) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (legacyKssJalPC + 4)) **
    legacyKssCallPost
      sp0 (sp0 + signExtend12 ((-64 : BitVec 12)))
      (legacyKssJalPC + 4) legacyKssSegsBase outputBase
      (legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes)
      inPtr v9 chainId outputBase hdrLen payloadBase
      (legacyKssBodyPayloadEnd chainId payloadBase) A source **
    (legacyPrefixCellPtr ↦ₘ legacyKssBodyPrefixLen chainId payloadBase) **
    legacyKssBodyProducedResidual chainId payloadBase offVal lenVal ** R

/-! Full-body composition from the linked arithmetic entry through KSS and the
    success reconvergence.  This is a composition of the already deployed
    segment adapters; it introduces no fresh callee contract premise.  The
    source is bundled with the caller-owned input-region proof, so the
    payload owner is supplied by the caller rather than assumed as a second
    subregion. -/

theorem legacyBodyThenKssSuccess_spec
    (v1 v5 v6 v7 v10 v11 v12 chainId v28 v29 v30 v31 v21 : Word)
    (offVal lenVal hdrLen cellOld inPtr outputBase sp0 v9 : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBytes os : List (BitVec 8)) (A R : Assertion)
    (hA : A.pcFree) (hR : R.pcFree)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0)
    (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess
        (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayloadLen : BitVec.ofNat 64 payloadBytes.length =
      ((offVal + lenVal) - hdrLen))
    (hos : os.length = 200)
    (hcount :
      (legacyKssBodySegs chainId ((offVal + lenVal) - hdrLen)
        inPtr hdrLen payloadBytes).length < 2 ^ 64)
    (hsegs :
      ∀ s ∈ legacyKssBodySegs chainId ((offVal + lenVal) - hdrLen)
        inPtr hdrLen payloadBytes,
        s.2.length < 2 ^ 64 ∧
          (∀ i, i < s.2.length →
            s.1.toNat + i < 2 ^ 64 ∧
            isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (sourceSpec : KssInputSourceSpec inPtr hdrLen input payloadBytes)
    (hsourcePrefix : sourceSpec.source.region legacyPrefixOutPtr
        (legacyKssBodyPrefixBytes chainId ((offVal + lenVal) - hdrLen)) =
      bytesRegion legacyPrefixOutPtr
        (legacyKssBodyPrefixBytes chainId ((offVal + lenVal) - hdrLen)))
    (hsourceSuffix : sourceSpec.source.region legacySuffixOutPtr
        (legacyKssBodySuffixBytes chainId) =
      bytesRegion legacySuffixOutPtr (legacyKssBodySuffixBytes chainId)) :
    let n :=
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
    let uintFuel :=
      1 + (8 * 6 + 7 *
        (8 - RlpEncodeUintBeSAsm.reubZeros (chainBytes chainId) 0 8) + 17)
    let prefixFuel := 8 + (1 + tshPrefixFuel) + 8 +
      (n * (6 + 1) + 1) + 4
    cpsTripleWithin
      ((8 + (68 + 8 + uintFuel + prefixFuel)) +
        (21 + ((1 + (19 + kssBodyFuelMulti
          (legacyKssBodySegs chainId ((offVal + lenVal) - hdrLen)
            inPtr hdrLen payloadBytes))) + 2)))
      (legacyH + 128) legacyBodyExit legacyFullCode
      (legacyKssBodyInitial v1 v5 v6 v7 v10 v11 v12 chainId v28 v29 v30 v31 v21
        offVal lenVal hdrLen cellOld inPtr outputBase sp0 v9
        old0 old1 old2 old3 old4 old5 input os A R)
      (legacyKssBodyFinal chainId ((offVal + lenVal) - hdrLen)
        inPtr hdrLen outputBase sp0 v9 offVal lenVal payloadBytes A R sourceSpec.source) := by
  intro n uintFuel prefixFuel
  let payloadBase : Word := (offVal + lenVal) - hdrLen
  let Fbody : Assertion :=
    legacyKssBodyExtra inPtr outputBase sp0 v9
      old0 old1 old2 old3 old4 old5 input os A R
  have hFbody : Fbody.pcFree := by
    unfold Fbody legacyKssBodyExtra
    pcf
    all_goals assumption
  have hpayloadLen' : BitVec.ofNat 64 payloadBytes.length = payloadBase := by
    simpa [payloadBase] using hpayloadLen
  have hcount' :
      (legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes).length <
        2 ^ 64 := by
    simpa [payloadBase] using hcount
  have hsegs' :
      ∀ s ∈ legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes,
        s.2.length < 2 ^ 64 ∧
          (∀ i, i < s.2.length →
            s.1.toNat + i < 2 ^ 64 ∧
            isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true) := by
    simpa [payloadBase] using hsegs
  have harith := legacyBodyArithmeticThenChain_spec
    v1 v5 v6 v7 v10 v11 v12 chainId v28 v29 v30 v31 v21
    offVal lenVal hdrLen cellOld Fbody hFbody halign hover hvalid hbound h_out_valid
  have htail := legacyChainDescriptorThenKssSuccess_spec
    chainId payloadBase inPtr hdrLen outputBase sp0 v9 offVal lenVal
    old0 old1 old2 old3 old4 old5 payloadBytes input os A R hA hR
    hpayloadLen' hos hcount' hsegs' sourceSpec.source hsourcePrefix
    sourceSpec.input_region hsourceSuffix
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [legacyKssBodySuffixLen, legacyKssBodyChainLen,
        legacyKssBodyPayloadEnd,
        legacyKssBodyPrefixBytes, legacyKssBodyPrefixLen,
        legacyKssBodySuffixBytes, legacyKssBodyProducedResidual,
        Fbody, legacyKssBodyExtra, payloadBase] at hp ⊢
      xperm_hyp hp)
    harith htail
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [legacyKssBodyInitial, Fbody, legacyKssBodyExtra,
        legacyTailExtension] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [legacyKssBodyFinal, legacyKssBodyProducedResidual,
        legacyKssCallPost, legacyKssBodySegs, payloadBase] at hq ⊢
      xperm_hyp hq)
    hseq

/-! ## K146's canonical payload slice

    The Nth post reports a selected content offset and length, while the KSS
    source adapter is indexed by the caller's input list.  These lemmas keep
    that bridge in the K146 composition rather than changing the generic Nth
    contract or adding a free payload-equality premise. -/

theorem legacyStrictNthItem_content_ge {bytes : List (BitVec 8)} {base : Word}
    {endOff : Nat} : ∀ {index cursorOff : Nat} {next len : Word},
    EvmAsm.Codegen.RlpListNthItemSAsm.StrictNthItem bytes base
      (base + BitVec.ofNat 64 endOff) index cursorOff next len →
    cursorOff ≤ endOff →
    base.toNat + endOff + 9 < 2 ^ 64 →
    cursorOff ≤ (next - len - base).toNat := by
  intro index cursorOff next len h
  induction h with
  | zero off n l hitem =>
      intro hcursor hover
      exact (EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_spanStart
        hitem hcursor hover).2.1
  | succ idx off n l fn fl hitem hrest ih =>
      intro hcursor hover
      have hadv := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance
        hitem hcursor hover
      have hrest_ge := ih hadv.2.2 hover
      exact le_trans (Nat.le_of_lt hadv.2.1) hrest_ge

theorem legacyStrictListPayload_cursor_eq_hdrLen
    {input : List (BitVec 8)} {base : Word} {listLen cursorOff : Nat}
    {endPtr : Word} (h0 : 0 < input.length)
    (hlist : EvmAsm.Codegen.RlpListNthItemSAsm.StrictListPayload input base
      listLen cursorOff endPtr) :
    cursorOff = (legacyHdrLen input h0).toNat := by
  cases hlist with
  | short b hbyte hge hshort hcursor hlen =>
      rw [List.getElem?_eq_getElem h0] at hbyte
      have hb : input[0]'h0 = b := Option.some.inj hbyte
      subst b
      subst cursorOff
      have hlenOf : legacyHdrLen input h0 = (1 : Word) := by
        unfold legacyHdrLen legacyHdrByte
        exact legacyHdrLenOf_short _ hshort
      rw [hlenOf]
      decide
  | long b first hbyte hlong hfirst hnz hminimal hcursor hlen =>
      rw [List.getElem?_eq_getElem h0] at hbyte
      have hb : input[0]'h0 = b := Option.some.inj hbyte
      subst b
      have hlenOf : legacyHdrLen input h0 =
          (input[0]'h0).zeroExtend 64 - (246 : Word) := by
        unfold legacyHdrLen legacyHdrByte
        exact legacyHdrLenOf_long _ hlong
      rw [hlenOf]
      rw [hcursor]
      have hb8 : (input[0]'h0).toNat < 256 := by
        exact (input[0]'h0).isLt
      have hge248 : 248 ≤ (input[0]'h0).toNat := by
        have hh := hlong
        simp [BitVec.ult] at hh
        omega
      bv_omega

theorem legacyStrictNthItem_content_le {bytes : List (BitVec 8)} {base : Word}
    {endOff : Nat} : ∀ {index cursorOff : Nat} {next len : Word},
    EvmAsm.Codegen.RlpListNthItemSAsm.StrictNthItem bytes base
      (base + BitVec.ofNat 64 endOff) index cursorOff next len →
    cursorOff ≤ endOff →
    base.toNat + endOff + 9 < 2 ^ 64 →
    (next - len - base).toNat + len.toNat ≤ endOff := by
  intro index cursorOff next len h
  induction h with
  | zero off n l hitem =>
      intro hcursor hover
      exact (EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_spanStart
        hitem hcursor hover).2.2
  | succ idx off n l fn fl hitem hrest ih =>
      intro hcursor hover
      have hadv := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance
        hitem hcursor hover
      exact ih hadv.2.2 hover

theorem legacyNthSuccess_payloadSlice
    {input : List (BitVec 8)} {base hdrLen : Word}
    {listLen : Nat} {offset len : Word}
    (h0 : 0 < input.length)
    (hheader : hdrLen = legacyHdrLen input h0)
    (hslack : listLen + 9 ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (halign : base.toNat % 8 = 0)
    (hsucc : EvmAsm.Codegen.RlpListNthItemSAsm.Success input base listLen 5 offset len) :
    ∃ payload : List (BitVec 8),
      ∃ _sourceSpec : KssInputSourceSpec base hdrLen input payload,
        BitVec.ofNat 64 payload.length = (offset + len) - hdrLen := by
  obtain ⟨cursorOff, endPtr, next, hlist, hnth, hoff⟩ := hsucc
  have hend := hlist.end_eq
  subst endPtr
  have hcur := hlist.cursor_le
  have hover9 : base.toNat + listLen + 9 < 2 ^ 64 := by omega
  have hupper := legacyStrictNthItem_content_le hnth hcur hover9
  have hlower := legacyStrictNthItem_content_ge hnth hcur hover9
  have hcursor := legacyStrictListPayload_cursor_eq_hdrLen h0 hlist
  have hcursorHdr : cursorOff = hdrLen.toNat := by
    simpa [hheader] using hcursor
  have hlower' : hdrLen.toNat ≤ offset.toNat := by
    calc
      hdrLen.toNat = cursorOff := hcursorHdr.symm
      _ ≤ (next - len - base).toNat := hlower
      _ = offset.toNat := by rw [hoff]
  have hupper' : offset.toNat + len.toNat ≤ listLen := by
    simpa [hoff] using hupper
  have hinput : input.length < 2 ^ 64 := by omega
  have hsum : offset.toNat + len.toNat < 2 ^ 64 := by omega
  have hsum_word : (offset + len).toNat = offset.toNat + len.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hsum
  have hsub : ((offset + len) - hdrLen).toNat =
      offset.toNat + len.toNat - hdrLen.toNat := by
    rw [BitVec.toNat_sub, hsum_word]
    rw [show 2 ^ 64 - hdrLen.toNat + (offset.toNat + len.toNat) =
        2 ^ 64 + (offset.toNat + len.toNat - hdrLen.toNat) by omega]
    rw [Nat.mod_eq_sub_mod (by omega)]
    have hsub_lt : offset.toNat + len.toNat - hdrLen.toNat < 2 ^ 64 := by omega
    have hcancel : 2 ^ 64 + (offset.toNat + len.toNat - hdrLen.toNat) - 2 ^ 64 =
        offset.toNat + len.toNat - hdrLen.toNat := by omega
    rw [hcancel, Nat.mod_eq_of_lt hsub_lt]
  have hslice_len : hdrLen.toNat + ((offset + len) - hdrLen).toNat ≤ input.length := by
    rw [hsub]
    omega
  let payload : List (BitVec 8) :=
    (input.drop hdrLen.toNat).take ((offset + len - hdrLen).toNat)
  have hpayload_len : payload.length = ((offset + len - hdrLen).toNat) := by
    dsimp [payload]
    simp only [List.length_take, List.length_drop]
    omega
  have hpayload_len_word : BitVec.ofNat 64 payload.length =
      (offset + len) - hdrLen := by
    rw [hpayload_len]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlen : payload.length + hdrLen.toNat ≤ input.length := by
    rw [hpayload_len]
    omega
  have hpayload : (input.drop hdrLen.toNat).take payload.length = payload := by
    simp [payload]
  refine ⟨payload,
    kssInputSourceSpec_of_payload base hdrLen input payload halign hlen hover hpayload,
    hpayload_len_word⟩

#print axioms legacyNthSuccess_payloadSlice

/-! The canonical source returned above is `kssInputSource`: its payload pair is
    intentionally overridden to lend the caller's input region.  The two other
    KSS segments are linked static buffers.  This small bridge exposes the
    source equation once a pointer is proved not to be the payload pointer and
    is dword aligned; it does not add a memory premise. -/

theorem legacyKssInputSource_static_region
    {input payload bs : List (BitVec 8)} {base hdrLen p : Word}
    (halign : base.toNat % 8 = 0)
    (hlen : payload.length + hdrLen.toNat ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hbytes : ∀ i (hi : i < payload.length),
      input[hdrLen.toNat + i]'(by omega) = payload[i]'hi)
    (hptr : p ≠ base + hdrLen)
    (hzero : byteOffset p = 0) :
    (kssInputSource base hdrLen input payload halign hlen hover hbytes).region p bs =
      bytesRegion p bs := by
  by_cases hbs : bs = []
  · subst bs
    simp [kssInputSource, hptr, kssSourceRegion]
  · simp [kssInputSource, hptr, kssSourceRegion, hzero, hbs]

/-! `INPUT_MEM_END` is a named linked-layout dependency.  The production
    caller supplies this bound because the transaction slice is carved out of
    the host input zone, while `t155_buf` and its suffix are linked in RAM.
    If either layout moves, these equations must be rechecked; no generic
    `hslack` fact implies them. -/

theorem legacyKssInputSource_prefix_region_of_input_layout
    {input payload : List (BitVec 8)} {base hdrLen : Word}
    (halign : base.toNat % 8 = 0)
    (hlen : payload.length + hdrLen.toNat ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hbytes : ∀ i (hi : i < payload.length),
      input[hdrLen.toNat + i]'(by omega) = payload[i]'hi)
    (hinput_hi : base.toNat + input.length ≤ EvmAsm.Codegen.INPUT_MEM_END)
    (bs : List (BitVec 8)) :
    (kssInputSource base hdrLen input payload halign hlen hover hbytes).region
      legacyPrefixOutPtr bs = bytesRegion legacyPrefixOutPtr bs := by
  apply legacyKssInputSource_static_region halign hlen hover hbytes
  · intro heq
    have hhdr : hdrLen.toNat ≤ input.length := by omega
    have hbase_sum_hi : base.toNat + hdrLen.toNat ≤ EvmAsm.Codegen.INPUT_MEM_END := by
      omega
    have hbase_lt64 : base.toNat + hdrLen.toNat < 2 ^ 64 := by omega
    have hbase_word : (base + hdrLen).toNat = base.toNat + hdrLen.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt hbase_lt64
    have hp : legacyPrefixOutPtr.toNat = base.toNat + hdrLen.toNat := by
      calc
        legacyPrefixOutPtr.toNat = (base + hdrLen).toNat := by rw [heq]
        _ = base.toNat + hdrLen.toNat := hbase_word
    have hout : legacyPrefixOutPtr.toNat = 0xa3a2bf00 := by
      simp [legacyPrefixOutPtr, GuestAddrs.t155_buf]
    rw [hout] at hp
    simp only [EvmAsm.Codegen.INPUT_MEM_END] at hbase_sum_hi
    omega
  · simp [legacyPrefixOutPtr, GuestAddrs.t155_buf, byteOffset]

theorem legacyKssInputSource_suffix_region_of_input_layout
    {input payload : List (BitVec 8)} {base hdrLen : Word}
    (halign : base.toNat % 8 = 0)
    (hlen : payload.length + hdrLen.toNat ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hbytes : ∀ i (hi : i < payload.length),
      input[hdrLen.toNat + i]'(by omega) = payload[i]'hi)
    (hinput_hi : base.toNat + input.length ≤ EvmAsm.Codegen.INPUT_MEM_END)
    (bs : List (BitVec 8)) :
    (kssInputSource base hdrLen input payload halign hlen hover hbytes).region
      legacySuffixOutPtr bs = bytesRegion legacySuffixOutPtr bs := by
  apply legacyKssInputSource_static_region halign hlen hover hbytes
  · intro heq
    have hhdr : hdrLen.toNat ≤ input.length := by omega
    have hbase_sum_hi : base.toNat + hdrLen.toNat ≤ EvmAsm.Codegen.INPUT_MEM_END := by
      omega
    have hbase_lt64 : base.toNat + hdrLen.toNat < 2 ^ 64 := by omega
    have hbase_word : (base + hdrLen).toNat = base.toNat + hdrLen.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt hbase_lt64
    have hp : legacySuffixOutPtr.toNat = base.toNat + hdrLen.toNat := by
      calc
        legacySuffixOutPtr.toNat = (base + hdrLen).toNat := by rw [heq]
        _ = base.toNat + hdrLen.toNat := hbase_word
    have hout : legacySuffixOutPtr.toNat = 0xa3a2bf40 := by
      simp [legacySuffixOutPtr, legacyPrefixOutPtr, GuestAddrs.t155_buf]
    rw [hout] at hp
    simp only [EvmAsm.Codegen.INPUT_MEM_END] at hbase_sum_hi
    omega
  · simp [legacySuffixOutPtr, legacyPrefixOutPtr,
      GuestAddrs.t155_buf, byteOffset]

/-! The combined form is the artifact consumed by the K146 tail composition.
    Keeping both static views under one theorem prevents a caller from
    discharging one side of the linked-buffer separation and silently leaving
    the other side on the generic source premise.  The input-layout bound is
    intentionally still explicit: this theorem records the consequence of a
    caller-owned layout fact; it does not manufacture that fact from `hslack`.
-/

theorem legacyKssInputSource_static_regions_of_input_layout
    {input payload : List (BitVec 8)} {base hdrLen : Word}
    (halign : base.toNat % 8 = 0)
    (hlen : payload.length + hdrLen.toNat ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hbytes : ∀ i (hi : i < payload.length),
      input[hdrLen.toNat + i]'(by omega) = payload[i]'hi)
    (hinput_hi : base.toNat + input.length ≤ EvmAsm.Codegen.INPUT_MEM_END)
    (prefixBytes suffixBytes : List (BitVec 8)) :
    ((kssInputSource base hdrLen input payload halign hlen hover hbytes).region
      legacyPrefixOutPtr prefixBytes = bytesRegion legacyPrefixOutPtr prefixBytes) ∧
    ((kssInputSource base hdrLen input payload halign hlen hover hbytes).region
      legacySuffixOutPtr suffixBytes = bytesRegion legacySuffixOutPtr suffixBytes) := by
  constructor
  · exact legacyKssInputSource_prefix_region_of_input_layout
      halign hlen hover hbytes hinput_hi prefixBytes
  · exact legacyKssInputSource_suffix_region_of_input_layout
      halign hlen hover hbytes hinput_hi suffixBytes

/-! ## A joint, non-degenerate inhabitant of the complete body precondition

    This witness is deliberately built over the whole `legacyKssBodyInitial`
    assertion.  The register atoms, table cells, byte-region dwords, and the
    eight owned KSS frame slots are folded into one `PartialState`; proving
    them separately would not detect a resource supplied twice through an
    enclosing frame.  The two ambient assertions are `empAssertion`, but the
    witness is not degenerate: it contains the real nonempty chain, prefix,
    suffix, payload, output, and 200-byte sponge regions, as well as all frame
    cells. -/

/-! This is a constructive non-vacuity result at the exhibited parameter point;
    it does not assert that the parametric precondition is satisfiable for every
    choice of its values. -/

private inductive BodySatAtom where
  | reg (r : Reg) (v : Word)
  | ownReg (r : Reg)
  | mem (a v : Word) (valid : isValidDwordAccess a = true)
  | memOwn (a : Word) (valid : isValidDwordAccess a = true)

private def bodySatAtomAssertion : BodySatAtom → Assertion
  | .reg r v => r ↦ᵣ v
  | .ownReg r => regOwn r
  | .mem a v _ => a ↦ₘ v
  | .memOwn a _ => memOwn a

private def bodySatAtomHeap : BodySatAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .ownReg r => PartialState.singletonReg r 0
  | .mem a v _ => PartialState.singletonMem a v
  | .memOwn a _ => PartialState.singletonMem a 0

private inductive BodySatResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def bodySatResource : BodySatAtom → BodySatResource
  | .reg r _ => .reg r
  | .ownReg r => .reg r
  | .mem a _ _ => .mem a
  | .memOwn a _ => .mem a

private theorem bodySat_reg_reg_disjoint
    {r1 r2 : Reg} {v1 v2 : Word} (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]

private theorem bodySat_mem_mem_disjoint
    {a1 a2 : Word} {v1 v2 : Word} (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

private theorem bodySat_reg_mem_disjoint
    {r : Reg} {a v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem bodySat_mem_reg_disjoint
    {r : Reg} {a v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  bodySat_reg_mem_disjoint.symm

private theorem bodySat_heap_disjoint_of_resource_ne
    {x y : BodySatAtom}
    (h : bodySatResource x ≠ bodySatResource y) :
    (bodySatAtomHeap x).Disjoint (bodySatAtomHeap y) := by
  cases x <;> cases y
  · apply bodySat_reg_reg_disjoint
    simpa [bodySatResource] using h
  · apply bodySat_reg_reg_disjoint
    simpa [bodySatResource] using h
  · exact bodySat_reg_mem_disjoint
  · exact bodySat_reg_mem_disjoint
  · apply bodySat_reg_reg_disjoint
    simpa [bodySatResource] using h
  · apply bodySat_reg_reg_disjoint
    simpa [bodySatResource] using h
  · exact bodySat_reg_mem_disjoint
  · exact bodySat_reg_mem_disjoint
  · exact bodySat_mem_reg_disjoint
  · exact bodySat_mem_reg_disjoint
  · apply bodySat_mem_mem_disjoint
    simpa [bodySatResource] using h
  · apply bodySat_mem_mem_disjoint
    simpa [bodySatResource] using h
  · exact bodySat_mem_reg_disjoint
  · exact bodySat_mem_reg_disjoint
  · apply bodySat_mem_mem_disjoint
    simpa [bodySatResource] using h
  · apply bodySat_mem_mem_disjoint
    simpa [bodySatResource] using h

private def bodySatChainId : Word := BitVec.ofNat 64 1
private def bodySatOff : Word := BitVec.ofNat 64 9
private def bodySatLen : Word := BitVec.ofNat 64 0
private def bodySatHdrLen : Word := BitVec.ofNat 64 8
private def bodySatInPtr : Word := BitVec.ofNat 64 0x40000000
private def bodySatOutputBase : Word := BitVec.ofNat 64 0x50000000
private def bodySatSp0 : Word := BitVec.ofNat 64 0x60000100
private def bodySatV9 : Word := BitVec.ofNat 64 0
private def bodySatPayload : List (BitVec 8) := [0]
private def bodySatInput : List (BitVec 8) := List.replicate 8 0 ++ bodySatPayload
private def bodySatOs : List (BitVec 8) := List.replicate 200 0
private def bodySatFrameBase : Word :=
  bodySatSp0 + signExtend12 ((-64 : BitVec 12))

private def bodySatKssAddr : Nat → Word
  | 0 => KssZk3
  | n + 1 => bodySatKssAddr n + 8

private def bodySatOutputAddr : Nat → Word
  | 0 => bodySatOutputBase
  | n + 1 => bodySatOutputAddr n + 8

private def bodySatAtoms : List BodySatAtom :=
  [ .reg .x5 (0 : Word)
  , .reg .x6 (0 : Word)
  , .reg .x7 (0 : Word)
  , .reg .x20 bodySatHdrLen
  , .reg .x21 (0 : Word)
  , .mem legacyLinkedNthOffPtr bodySatOff (by decide)
  , .mem legacyLinkedNthLenPtr bodySatLen (by decide)
  , .reg .x1 (0 : Word)
  , .reg .x10 (0 : Word)
  , .reg .x11 (0 : Word)
  , .reg .x12 (0 : Word)
  , .reg .x18 bodySatChainId
  , .reg .x28 (0 : Word)
  , .reg .x29 (0 : Word)
  , .reg .x30 (0 : Word)
  , .reg .x31 (0 : Word)
  , .reg .x0 (0 : Word)
  , .mem legacyLinkedChainPtr (0 : Word) (by decide)
  , .mem legacyLinkedChainEncPtr (0 : Word) (by decide)
  , .mem (legacyLinkedChainEncPtr + 8) (0 : Word) (by decide)
  , .mem legacyPrefixOutPtr (0 : Word) (by decide)
  , .mem (legacyPrefixOutPtr + 8) (0 : Word) (by decide)
  , .mem legacyPrefixCellPtr (0 : Word) (by decide)
  , .mem legacySuffixOutPtr (0 : Word) (by decide)
  , .ownReg .x22
  , .reg .x8 bodySatInPtr
  , .reg .x19 bodySatOutputBase
  , .mem legacyKssSegsBase (0 : Word) (by decide)
  , .mem (legacyKssSegsBase + 8) (0 : Word) (by decide)
  , .mem (legacyKssSegsBase + 16) (0 : Word) (by decide)
  , .mem (legacyKssSegsBase + 24) (0 : Word) (by decide)
  , .mem (legacyKssSegsBase + 32) (0 : Word) (by decide)
  , .mem (legacyKssSegsBase + 40) (0 : Word) (by decide)
  , .reg .x2 bodySatSp0
  , .reg .x9 bodySatV9
  , .memOwn (bodySatFrameBase + signExtend12 (0 : BitVec 12)) (by decide)
  , .memOwn (bodySatFrameBase + signExtend12 (8 : BitVec 12)) (by decide)
  , .memOwn (bodySatFrameBase + signExtend12 (16 : BitVec 12)) (by decide)
  , .memOwn (bodySatFrameBase + signExtend12 (24 : BitVec 12)) (by decide)
  , .memOwn (bodySatFrameBase + signExtend12 (32 : BitVec 12)) (by decide)
  , .memOwn (bodySatFrameBase + signExtend12 (40 : BitVec 12)) (by decide)
  , .memOwn (bodySatFrameBase + signExtend12 (48 : BitVec 12)) (by decide)
  , .memOwn (bodySatFrameBase + signExtend12 (56 : BitVec 12)) (by decide)
  , .ownReg .x13
  , .ownReg .x14
  , .ownReg .x15
  , .ownReg .x16
  , .ownReg .x17
  , .mem (bodySatKssAddr 0) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 1) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 2) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 3) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 4) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 5) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 6) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 7) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 8) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 9) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 10) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 11) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 12) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 13) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 14) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 15) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 16) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 17) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 18) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 19) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 20) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 21) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 22) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 23) (0 : Word) (by decide)
  , .mem (bodySatKssAddr 24) (0 : Word) (by decide)
  , .mem (bodySatOutputAddr 0) (0 : Word) (by decide)
  , .mem (bodySatOutputAddr 1) (0 : Word) (by decide)
  , .mem (bodySatOutputAddr 2) (0 : Word) (by decide)
  , .mem (bodySatOutputAddr 3) (0 : Word) (by decide)
  , .mem bodySatInPtr (0 : Word) (by decide)
  , .mem (bodySatInPtr + 8) (0 : Word) (by decide)
  ]

private theorem bodySatAtoms_resource_pairwise :
    bodySatAtoms.Pairwise
      (fun x y => bodySatResource x ≠ bodySatResource y) := by
  unfold bodySatAtoms bodySatResource bodySatChainId bodySatHdrLen
    bodySatInPtr bodySatOutputBase bodySatSp0 bodySatV9 bodySatFrameBase
  decide

private def bodySatHeapFold : PartialState :=
  bodySatAtoms.foldr
    (fun x acc => (bodySatAtomHeap x).union acc) PartialState.empty

private theorem bodySat_hsat :
    (bodySatAtoms.foldr
      (fun x acc => bodySatAtomAssertion x ** acc) empAssertion)
      bodySatHeapFold := by
  apply sepConj_foldr_satisfiable
    bodySatAtomAssertion bodySatAtomHeap bodySatAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | ownReg r => exact ⟨0, rfl⟩
    | mem a v h => exact ⟨rfl, h⟩
    | memOwn a h =>
        refine ⟨0, ?_⟩
        exact ⟨rfl, h⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => bodySat_heap_disjoint_of_resource_ne h)
      bodySatAtoms_resource_pairwise

set_option maxRecDepth 8000 in
theorem legacyKssBodyInitial_pre_inhabited :
    ∃ h : PartialState,
      legacyKssBodyInitial
        (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word) (0 : Word) (0 : Word) bodySatChainId
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        bodySatOff bodySatLen bodySatHdrLen (0 : Word)
        bodySatInPtr bodySatOutputBase bodySatSp0 bodySatV9
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        bodySatInput bodySatOs empAssertion empAssertion h := by
  refine ⟨bodySatHeapFold, ?_⟩
  have hsat := bodySat_hsat
  simp [legacyKssBodyInitial, legacyKssBodyExtra, bodySatAtoms,
    bodySatAtomAssertion, bodySatAtomHeap, bodySatHeapFold,
    bodySatChainId, bodySatOff, bodySatLen, bodySatHdrLen, bodySatInPtr,
    bodySatOutputBase, bodySatSp0, bodySatV9, bodySatInput, bodySatPayload, bodySatOs,
    bodySatKssAddr, bodySatOutputAddr,
    bodySatFrameBase, legacyChainEncOld, bytesRegion, bytesRegionAux,
    packBytes, getByteAt, packDword, chainBytes,
    RlpEncodeUintBeSAsm.reubOut, RlpEncodeUintBeSAsm.reubStrip, encodeBytes,
    frameSlotsOwn, kssFrame, legacyTailExtension,
    sepConj_emp_left', sepConj_emp_right', sepConj_assoc'] at hsat ⊢
  xperm_hyp hsat


end EvmAsm.Codegen.TxSigningHashLegacyTailCompose
