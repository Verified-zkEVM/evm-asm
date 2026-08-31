/-
  K146 H+324 tail foundations: the KSS edge, descriptor setup, and terminator
  declarations consumed by the composition module.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyPrefixCopyCompose
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

theorem legacy_tail_chain_len_2pow48 :
    (RlpEncodeUintBeSAsm.reubOut
      (chainBytes (BitVec.ofNat 64 (2 ^ 48)))).length = 8 := by
  decide

theorem legacy_tail_chain_len_2pow40 :
    (RlpEncodeUintBeSAsm.reubOut
      (chainBytes (BitVec.ofNat 64 (2 ^ 40)))).length = 7 := by
  decide

/-! The KSS edge is lifted into the K146 linked image here rather than
    reusing the K145 code requirement.  The four ranges are disjoint in the
    deployed image, so the leaf triple remains an emitted-code fact. -/

theorem legacyKss_nth_disjoint : legacyNthCode.Disjoint legacyKssCode := by
  unfold legacyNthCode legacyKssCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [kssProgL_len]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length, kssProgL_len]; decide

theorem legacyKss_uint_disjoint : legacyUintCode.Disjoint legacyKssCode := by
  unfold legacyUintCode legacyKssCode EvmAsm.Codegen.RlpEncodeUintBeSAsm.reubCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_prog_length]; decide
  · rw [kssProgL_len]; decide
  · rw [EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_prog_length, kssProgL_len]; decide

theorem legacyKss_prefix_disjoint : legacyPrefixCode.Disjoint legacyKssCode := by
  unfold legacyPrefixCode legacyKssCode
  apply CodeReq.Disjoint.ofProg_ranges
  · decide
  · rw [kssProgL_len]; decide
  · rw [kssProgL_len]; decide

theorem legacyKss_mono : ∀ a i, legacyKssCode a = some i → legacyFullCode a = some i := by
  intro a i hi
  have hlegacy : legacyCode a = none := by
    cases legacyKss_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have hnth : legacyNthCode a = none := by
    cases legacyKss_nth_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have huint : legacyUintCode a = none := by
    cases legacyKss_uint_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have hprefix : legacyPrefixCode a = none := by
    cases legacyKss_prefix_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  change (legacyCode.union (legacyNthCode.union
    (legacyUintCode.union (legacyPrefixCode.union legacyKssCode)))) a = some i
  exact CodeReq.union_skip hlegacy
    (CodeReq.union_skip hnth
      (CodeReq.union_skip huint (CodeReq.union_skip hprefix hi)))

/-! ## The KSS edge at the K146 call site

    The generic KSS triple is already proved at its deployed entry.  These
    adapters repeat only the K145 call-site bookkeeping with the K146 PC and
    linked image: the descriptor setup below owns the six table cells, while
    this section supplies the ABI frame and `callWithin` edge. -/

abbrev legacyKssJalPC : Word := legacyH + (424 : Word)

abbrev legacyKssSegsBase : Word := legacyPrefixOutPtr + (128 : Word)

def legacyKssJalOff : BitVec 21 :=
  jalOff GuestAddrs.zkvm_keccak256_segments
    (GuestAddrs.tx_signing_hash_legacy_eip155 + 424)

theorem legacyKssJal_target :
    legacyKssJalPC + signExtend21 legacyKssJalOff = legacyKssB := by
  unfold legacyKssJalPC legacyKssJalOff legacyH legacyKssB
  decide

theorem legacyKssJal_ret_even :
    ((legacyKssJalPC + 4) &&& ~~~(1 : Word)) = legacyKssJalPC + 4 := by
  unfold legacyKssJalPC legacyH
  decide

theorem legacyKssJal_mem :
    ∀ a i, CodeReq.singleton legacyKssJalPC (.JAL .x1 legacyKssJalOff) a = some i →
      legacyFullCode a = some i := by
  intro a i hi
  have h := CodeReq.ofProg_mem_at legacyH legacyKssJalPC
    (txSigningHashLegacyEip155_prog : List Instr) 106
    (.JAL .x1 legacyKssJalOff)
    (by unfold legacyKssJalPC legacyH; decide)
    (by rw [legacy_prog_length]; decide)
    (by rfl) (by rw [legacy_prog_length]; norm_num) a i hi
  exact legacyCode_mono a i h

theorem legacyKssPrefixLen_spec (v29 prefixLen : Word) :
    cpsTripleWithin 3 (legacyH + 340) (legacyH + 352) legacyFullCode
      ((.x29 ↦ᵣ v29) ** (legacyPrefixCellPtr ↦ₘ prefixLen))
      ((.x29 ↦ᵣ prefixLen) ** (legacyPrefixCellPtr ↦ₘ prefixLen)) := by
  have h_hi :
      Codegen.laHi GuestAddrs.t155_prefix_len
          (GuestAddrs.tx_signing_hash_legacy_eip155 + 340) =
        Rv64.laHi (legacyH + 340) legacyPrefixCellPtr := by
    decide
  have h_lo :
      Codegen.laLo GuestAddrs.t155_prefix_len
          (GuestAddrs.tx_signing_hash_legacy_eip155 + 340) =
        Rv64.laLo (legacyH + 340) legacyPrefixCellPtr := by
    decide
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 340)
        (.AUIPC .x29 (Rv64.laHi (legacyH + 340) legacyPrefixCellPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 340) 85
      (.AUIPC .x29 (Codegen.laHi GuestAddrs.t155_prefix_len
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 340))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← h_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 340) + 4)
        (.ADDI .x29 .x29 (Rv64.laLo (legacyH + 340) legacyPrefixCellPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 344) 86
      (.ADDI .x29 .x29 (Codegen.laLo GuestAddrs.t155_prefix_len
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 340))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 340 : Word) + 4 = legacyH + 344 := by decide
    rw [hpc, ← h_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x29 v29 (legacyH + 340)
    legacyPrefixCellPtr (by decide) (by decide) hau had
  rw [show (legacyH + 340 : Word) + 8 = legacyH + 348 from by decide] at hla
  have hlaF := cpsTripleWithin_frameR
    (legacyPrefixCellPtr ↦ₘ prefixLen) (by exact pcFree_memIs) hla
  have hld := ld_spec_gen_same_within .x29 legacyPrefixCellPtr
    prefixLen (0 : BitVec 12) (legacyH + 348) (by decide)
  rw [show legacyPrefixCellPtr + signExtend12 (0 : BitVec 12) = legacyPrefixCellPtr
    from by decide] at hld
  have hld' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 348) 87 (.LD .x29 .x29 (0 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hld
  exact cpsTripleWithin_seq_same_cr hlaF hld'

theorem legacyKssSegsBase_spec (v30 : Word) :
    cpsTripleWithin 3 (legacyH + 352) (legacyH + 364) legacyFullCode
      (.x30 ↦ᵣ v30) (.x30 ↦ᵣ legacyKssSegsBase) := by
  have h_hi :
      Codegen.laHi GuestAddrs.t155_buf
          (GuestAddrs.tx_signing_hash_legacy_eip155 + 352) =
        Rv64.laHi (legacyH + 352) legacyPrefixOutPtr := by
    decide
  have h_lo :
      Codegen.laLo GuestAddrs.t155_buf
          (GuestAddrs.tx_signing_hash_legacy_eip155 + 352) =
        Rv64.laLo (legacyH + 352) legacyPrefixOutPtr := by
    decide
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 352)
        (.AUIPC .x30 (Rv64.laHi (legacyH + 352) legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 352) 88
      (.AUIPC .x30 (Codegen.laHi GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 352))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← h_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 352) + 4)
        (.ADDI .x30 .x30 (Rv64.laLo (legacyH + 352) legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 356) 89
      (.ADDI .x30 .x30 (Codegen.laLo GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 352))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 352 : Word) + 4 = legacyH + 356 := by decide
    rw [hpc, ← h_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x30 v30 (legacyH + 352)
    legacyPrefixOutPtr (by decide) (by decide) hau had
  rw [show (legacyH + 352 : Word) + 8 = legacyH + 360 from by decide] at hla
  have hadd := addi_spec_gen_same_within .x30 legacyPrefixOutPtr
    (128 : BitVec 12) (legacyH + 360) (by decide)
  rw [show signExtend12 (128 : BitVec 12) = (128 : Word) from by decide,
    show legacyPrefixOutPtr + (128 : Word) = legacyKssSegsBase from rfl] at hadd
  have hadd' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 360) 90 (.ADDI .x30 .x30 (128 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hadd
  exact cpsTripleWithin_seq_same_cr hla hadd'

theorem legacyKssPrefixPtr_spec (v31 : Word) :
    cpsTripleWithin 2 (legacyH + 364) (legacyH + 372) legacyFullCode
      (.x31 ↦ᵣ v31) (.x31 ↦ᵣ legacyPrefixOutPtr) := by
  have h_hi :
      Codegen.laHi GuestAddrs.t155_buf
          (GuestAddrs.tx_signing_hash_legacy_eip155 + 364) =
        Rv64.laHi (legacyH + 364) legacyPrefixOutPtr := by
    decide
  have h_lo :
      Codegen.laLo GuestAddrs.t155_buf
          (GuestAddrs.tx_signing_hash_legacy_eip155 + 364) =
        Rv64.laLo (legacyH + 364) legacyPrefixOutPtr := by
    decide
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 364)
        (.AUIPC .x31 (Rv64.laHi (legacyH + 364) legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 364) 91
      (.AUIPC .x31 (Codegen.laHi GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 364))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← h_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 364) + 4)
        (.ADDI .x31 .x31 (Rv64.laLo (legacyH + 364) legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 368) 92
      (.ADDI .x31 .x31 (Codegen.laLo GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 364))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 364 : Word) + 4 = legacyH + 368 := by decide
    rw [hpc, ← h_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x31 v31 (legacyH + 364)
    legacyPrefixOutPtr (by decide) (by decide) hau had
  rw [show (legacyH + 364 : Word) + 8 = legacyH + 372 from by decide] at hla
  exact hla

theorem legacyKssSuffixPtr_spec (v31 : Word) :
    cpsTripleWithin 3 (legacyH + 392) (legacyH + 404) legacyFullCode
      (.x31 ↦ᵣ v31) (.x31 ↦ᵣ legacySuffixOutPtr) := by
  have h_hi :
      Codegen.laHi GuestAddrs.t155_buf
          (GuestAddrs.tx_signing_hash_legacy_eip155 + 392) =
        Rv64.laHi (legacyH + 392) legacyPrefixOutPtr := by
    decide
  have h_lo :
      Codegen.laLo GuestAddrs.t155_buf
          (GuestAddrs.tx_signing_hash_legacy_eip155 + 392) =
        Rv64.laLo (legacyH + 392) legacyPrefixOutPtr := by
    decide
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 392)
        (.AUIPC .x31 (Rv64.laHi (legacyH + 392) legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 392) 98
      (.AUIPC .x31 (Codegen.laHi GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 392))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← h_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 392) + 4)
        (.ADDI .x31 .x31 (Rv64.laLo (legacyH + 392) legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 396) 99
      (.ADDI .x31 .x31 (Codegen.laLo GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 392))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 392 : Word) + 4 = legacyH + 396 := by decide
    rw [hpc, ← h_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x31 v31 (legacyH + 392)
    legacyPrefixOutPtr (by decide) (by decide) hau had
  rw [show (legacyH + 392 : Word) + 8 = legacyH + 400 from by decide] at hla
  have hadd := addi_spec_gen_same_within .x31 legacyPrefixOutPtr
    (64 : BitVec 12) (legacyH + 400) (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
    show legacyPrefixOutPtr + (64 : Word) = legacySuffixOutPtr from rfl] at hadd
  have hadd' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 400) 100 (.ADDI .x31 .x31 (64 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hadd
  exact cpsTripleWithin_seq_same_cr hla hadd'

/-! The descriptor is caller-owned storage.  The setup theorem keeps the
    descriptor cells in the assertion so the KSS adapter below receives the
    exact six-word table produced by the linked body, rather than treating the
    table as an untracked side condition. -/

theorem legacyKssDescriptorSetup_spec
    (prefixLen inPtr hdrLen payloadLen outputBase suffixLen : Word)
    (v29 v30 v31 v10 v11 v12 : Word)
    (old0 old1 old2 old3 old4 old5 : Word) (F : Assertion)
    (hF : F.pcFree) :
    cpsTripleWithin 21 (legacyH + 340) (legacyH + 424) legacyFullCode
      ((.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
        (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (legacyPrefixCellPtr ↦ₘ prefixLen) **
        (legacyKssSegsBase ↦ₘ old0) **
        ((legacyKssSegsBase + 8) ↦ₘ old1) **
        ((legacyKssSegsBase + 16) ↦ₘ old2) **
        ((legacyKssSegsBase + 24) ↦ₘ old3) **
        ((legacyKssSegsBase + 32) ↦ₘ old4) **
        ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
      ((.x29 ↦ᵣ prefixLen) ** (.x30 ↦ᵣ legacyKssSegsBase) **
        (.x31 ↦ᵣ legacySuffixOutPtr) **
        (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
        (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
        (.x10 ↦ᵣ legacyKssSegsBase) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x12 ↦ᵣ outputBase) **
        (legacyPrefixCellPtr ↦ₘ prefixLen) **
        (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
        ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
        ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
        ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
        ((legacyKssSegsBase + 32) ↦ₘ legacySuffixOutPtr) **
        ((legacyKssSegsBase + 40) ↦ₘ suffixLen) ** F) := by
  have h0 := legacyKssPrefixLen_spec v29 prefixLen
  have h1 := legacyKssSegsBase_spec v30
  have h2 := legacyKssPrefixPtr_spec v31
  have hs0 := sd_spec_gen_within .x30 .x31 legacyKssSegsBase
    legacyPrefixOutPtr old0 (0 : BitVec 12) (legacyH + 372)
  rw [show legacyKssSegsBase + signExtend12 (0 : BitVec 12) =
      legacyKssSegsBase from by decide,
    show (legacyH + 372 : Word) + 4 = legacyH + 376 from by decide] at hs0
  have hs0' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 372) 93
      (.SD .x30 .x31 (0 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) hs0
  have hs1 := sd_spec_gen_within .x30 .x29 legacyKssSegsBase
    prefixLen old1 (8 : BitVec 12) (legacyH + 376)
  rw [show legacyKssSegsBase + signExtend12 (8 : BitVec 12) =
      legacyKssSegsBase + 8 from by decide,
    show (legacyH + 376 : Word) + 4 = legacyH + 380 from by decide] at hs1
  have hs1' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 376) 94
      (.SD .x30 .x29 (8 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) hs1
  have ha := add_spec_gen_within .x31 .x8 .x20 inPtr hdrLen
    legacyPrefixOutPtr
    (legacyH + 380) (by decide)
  rw [show (legacyH + 380 : Word) + 4 = legacyH + 384 from by decide] at ha
  have ha' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 380) 95
      (.ADD .x31 .x8 .x20) (by decide) (by decide)
      (by intro h; rfl)) ha
  have hs2 := sd_spec_gen_within .x30 .x31 legacyKssSegsBase
    (inPtr + hdrLen) old2 (16 : BitVec 12) (legacyH + 384)
  rw [show legacyKssSegsBase + signExtend12 (16 : BitVec 12) =
      legacyKssSegsBase + 16 from by decide,
    show (legacyH + 384 : Word) + 4 = legacyH + 388 from by decide] at hs2
  have hs2' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 384) 96
      (.SD .x30 .x31 (16 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) hs2
  have hs3 := sd_spec_gen_within .x30 .x21 legacyKssSegsBase
    payloadLen old3 (24 : BitVec 12) (legacyH + 388)
  rw [show legacyKssSegsBase + signExtend12 (24 : BitVec 12) =
      legacyKssSegsBase + 24 from by decide,
    show (legacyH + 388 : Word) + 4 = legacyH + 392 from by decide] at hs3
  have hs3' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 388) 97
      (.SD .x30 .x21 (24 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) hs3
  have h3 := legacyKssSuffixPtr_spec v31
  have hs4 := sd_spec_gen_within .x30 .x31 legacyKssSegsBase
    legacySuffixOutPtr old4 (32 : BitVec 12) (legacyH + 404)
  rw [show legacyKssSegsBase + signExtend12 (32 : BitVec 12) =
      legacyKssSegsBase + 32 from by decide,
    show (legacyH + 404 : Word) + 4 = legacyH + 408 from by decide] at hs4
  have hs4' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 404) 101
      (.SD .x30 .x31 (32 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) hs4
  have hs5 := sd_spec_gen_within .x30 .x7 legacyKssSegsBase
    suffixLen old5 (40 : BitVec 12) (legacyH + 408)
  rw [show legacyKssSegsBase + signExtend12 (40 : BitVec 12) =
      legacyKssSegsBase + 40 from by decide,
    show (legacyH + 408 : Word) + 4 = legacyH + 412 from by decide] at hs5
  have hs5' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 408) 102
      (.SD .x30 .x7 (40 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) hs5
  have hm10 := mv_spec_gen_within .x10 .x30 legacyKssSegsBase v10
    (legacyH + 412) (by decide)
  rw [show (legacyH + 412 : Word) + 4 = legacyH + 416 from by decide] at hm10
  have hm10' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 412) 103
      (.MV .x10 .x30) (by decide) (by decide)
      (by intro h; rfl)) hm10
  have hl11 := li_spec_gen_within .x11 v11 (3 : Word)
    (legacyH + 416) (by decide)
  rw [show (legacyH + 416 : Word) + 4 = legacyH + 420 from by decide] at hl11
  have hl11' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 416) 104
      (.LI .x11 (3 : Word)) (by decide) (by decide)
      (by intro h; rfl)) hl11
  have hm12 := mv_spec_gen_within .x12 .x19 outputBase v12
    (legacyH + 420) (by decide)
  rw [show (legacyH + 420 : Word) + 4 = legacyH + 424 from by decide] at hm12
  have hm12' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 420) 105
      (.MV .x12 .x19) (by decide) (by decide)
      (by intro h; rfl)) hm12
  have h0F := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x8 ↦ᵣ inPtr) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyKssSegsBase ↦ₘ old0) ** ((legacyKssSegsBase + 8) ↦ₘ old1) **
      ((legacyKssSegsBase + 16) ↦ₘ old2) **
      ((legacyKssSegsBase + 24) ↦ₘ old3) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) h0
  have h1F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x31 ↦ᵣ v31) ** (.x8 ↦ᵣ inPtr) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ old0) ** ((legacyKssSegsBase + 8) ↦ₘ old1) **
      ((legacyKssSegsBase + 16) ↦ₘ old2) **
      ((legacyKssSegsBase + 24) ↦ₘ old3) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) h1
  have h2F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x30 ↦ᵣ legacyKssSegsBase) **
      (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ old0) ** ((legacyKssSegsBase + 8) ↦ₘ old1) **
      ((legacyKssSegsBase + 16) ↦ₘ old2) **
      ((legacyKssSegsBase + 24) ↦ₘ old3) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) h2
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h0F h1F
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 h2F
  have hs0F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x8 ↦ᵣ inPtr) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 8) ↦ₘ old1) **
      ((legacyKssSegsBase + 16) ↦ₘ old2) **
      ((legacyKssSegsBase + 24) ↦ₘ old3) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) hs0'
  have hs1F := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ legacyPrefixOutPtr) ** (.x8 ↦ᵣ inPtr) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 16) ↦ₘ old2) **
      ((legacyKssSegsBase + 24) ↦ₘ old3) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) hs1'
  have haF := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x30 ↦ᵣ legacyKssSegsBase) **
      (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ payloadLen) **
      (.x7 ↦ᵣ suffixLen) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ old2) **
      ((legacyKssSegsBase + 24) ↦ₘ old3) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) ha'
  have hs2F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x8 ↦ᵣ inPtr) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 24) ↦ₘ old3) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) hs2'
  have hs3F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x31 ↦ᵣ (inPtr + hdrLen)) **
      (.x8 ↦ᵣ inPtr) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x7 ↦ᵣ suffixLen) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) hs3'
  have h3F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x30 ↦ᵣ legacyKssSegsBase) **
      (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
      ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
      ((legacyKssSegsBase + 32) ↦ₘ old4) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) (legacyKssSuffixPtr_spec (inPtr + hdrLen))
  have hs4F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x8 ↦ᵣ inPtr) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
      ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
      ((legacyKssSegsBase + 40) ↦ₘ old5) ** F)
    (by pcf; exact hF) hs4'
  have hs5F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x31 ↦ᵣ legacySuffixOutPtr) **
      (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
      ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
      ((legacyKssSegsBase + 32) ↦ₘ legacySuffixOutPtr) ** F)
    (by pcf; exact hF) hs5'
  have hm10F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x31 ↦ᵣ legacySuffixOutPtr) **
      (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
      ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
      ((legacyKssSegsBase + 32) ↦ₘ legacySuffixOutPtr) **
      ((legacyKssSegsBase + 40) ↦ₘ suffixLen) ** F)
    (by pcf; exact hF) hm10'
  have hl11F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x30 ↦ᵣ legacyKssSegsBase) **
      (.x31 ↦ᵣ legacySuffixOutPtr) ** (.x8 ↦ᵣ inPtr) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ legacyKssSegsBase) ** (.x12 ↦ᵣ v12) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
      ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
      ((legacyKssSegsBase + 32) ↦ₘ legacySuffixOutPtr) **
      ((legacyKssSegsBase + 40) ↦ₘ suffixLen) ** F)
    (by pcf; exact hF) hl11'
  have hm12F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ prefixLen) ** (.x30 ↦ᵣ legacyKssSegsBase) **
      (.x31 ↦ᵣ legacySuffixOutPtr) ** (.x8 ↦ᵣ inPtr) **
      (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
      (.x10 ↦ᵣ legacyKssSegsBase) ** (.x11 ↦ᵣ (3 : Word)) **
      (legacyPrefixCellPtr ↦ₘ prefixLen) **
      (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
      ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
      ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
      ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
      ((legacyKssSegsBase + 32) ↦ₘ legacySuffixOutPtr) **
      ((legacyKssSegsBase + 40) ↦ₘ suffixLen) ** F)
    (by pcf; exact hF) hm12'
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c012 hs0F
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c03 hs1F
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c04 haF
  have c06 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c05 hs2F
  have c07 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c06 hs3F
  have c08 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c07 h3F
  have c09 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c08 hs4F
  have c10 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c09 hs5F
  have c11 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c10 hm10F
  have c12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c11 hl11F
  have c13 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c12 hm12F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c13

def legacyKssDescriptorRest
    (prefixLen inPtr hdrLen payloadLen outputBase suffixLen : Word)
    (v10 v11 v12 old0 old1 old2 old3 old4 old5 : Word)
    (F : Assertion) : Assertion :=
  (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
    (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
    (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
    (legacyPrefixCellPtr ↦ₘ prefixLen) **
    (legacyKssSegsBase ↦ₘ old0) **
    ((legacyKssSegsBase + 8) ↦ₘ old1) **
    ((legacyKssSegsBase + 16) ↦ₘ old2) **
    ((legacyKssSegsBase + 24) ↦ₘ old3) **
    ((legacyKssSegsBase + 32) ↦ₘ old4) **
    ((legacyKssSegsBase + 40) ↦ₘ old5) ** F

def legacyKssDescriptorPost
    (prefixLen inPtr hdrLen payloadLen outputBase suffixLen : Word)
    (F : Assertion) : Assertion :=
  (.x29 ↦ᵣ prefixLen) ** (.x30 ↦ᵣ legacyKssSegsBase) **
    (.x31 ↦ᵣ legacySuffixOutPtr) **
    (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ hdrLen) **
    (.x21 ↦ᵣ payloadLen) ** (.x7 ↦ᵣ suffixLen) **
    (.x10 ↦ᵣ legacyKssSegsBase) ** (.x11 ↦ᵣ (3 : Word)) **
    (.x12 ↦ᵣ outputBase) **
    (legacyPrefixCellPtr ↦ₘ prefixLen) **
    (legacyKssSegsBase ↦ₘ legacyPrefixOutPtr) **
    ((legacyKssSegsBase + 8) ↦ₘ prefixLen) **
    ((legacyKssSegsBase + 16) ↦ₘ (inPtr + hdrLen)) **
    ((legacyKssSegsBase + 24) ↦ₘ payloadLen) **
    ((legacyKssSegsBase + 32) ↦ₘ legacySuffixOutPtr) **
    ((legacyKssSegsBase + 40) ↦ₘ suffixLen) ** F

/-! The descriptor setup consumes owned scratch registers, so the prefix-copy
    post cannot feed it by choosing old register values.  This adapter peels
    the three `regOwn` atoms one at a time and leaves the produced descriptor
    values concrete for the following KSS call. -/

theorem legacyKssDescriptorSetup_regOwn_spec
    (prefixLen inPtr hdrLen payloadLen outputBase suffixLen : Word)
    (v10 v11 v12 old0 old1 old2 old3 old4 old5 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 21 (legacyH + 340) (legacyH + 424) legacyFullCode
      (regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase
          suffixLen v10 v11 v12 old0 old1 old2 old3 old4 old5 F)
      (legacyKssDescriptorPost prefixLen inPtr hdrLen payloadLen outputBase
        suffixLen F) := by
  have hconcrete : ∀ v29 v30 v31,
      cpsTripleWithin 21 (legacyH + 340) (legacyH + 424)
      legacyFullCode
      (((.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase
          suffixLen v10 v11 v12 old0 old1 old2 old3 old4 old5 F) **
        (.x31 ↦ᵣ v31))
      (legacyKssDescriptorPost prefixLen inPtr hdrLen payloadLen outputBase
        suffixLen F) := by
    intro v29 v30 v31
    have h := legacyKssDescriptorSetup_spec prefixLen inPtr hdrLen payloadLen
      outputBase suffixLen v29 v30 v31 v10 v11 v12
      old0 old1 old2 old3 old4 old5 F hF
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [legacyKssDescriptorRest] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [legacyKssDescriptorPost] at hq ⊢
        xperm_hyp hq) h
  have h31own : ∀ v29 v30, cpsTripleWithin 21 (legacyH + 340) (legacyH + 424)
      legacyFullCode
      ((.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase
          suffixLen v10 v11 v12 old0 old1 old2 old3 old4 old5 F **
        (regOwn (.x31 : Reg)))
      (legacyKssDescriptorPost prefixLen inPtr hdrLen payloadLen outputBase
        suffixLen F) := by
    intro v29 v30
    simpa only [sepConj_assoc'] using
      (cpsTripleWithin_of_forall_regIs_to_regOwn
        (r := .x31) (P :=
          (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
            legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase
              suffixLen v10 v11 v12 old0 old1 old2 old3 old4 old5 F)
        (fun v31 => hconcrete v29 v30 v31))
  have h30own : ∀ v29, cpsTripleWithin 21 (legacyH + 340) (legacyH + 424)
      legacyFullCode
      ((.x29 ↦ᵣ v29) **
        legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase
          suffixLen v10 v11 v12 old0 old1 old2 old3 old4 old5 F **
        regOwn .x31 ** regOwn .x30)
      (legacyKssDescriptorPost prefixLen inPtr hdrLen payloadLen outputBase
        suffixLen F) := by
    intro v29
    simpa only [sepConj_assoc'] using
      (cpsTripleWithin_of_forall_regIs_to_regOwn
        (r := .x30) (P :=
          (.x29 ↦ᵣ v29) **
            legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase
              suffixLen v10 v11 v12 old0 old1 old2 old3 old4 old5 F **
            regOwn .x31)
        (by
          intro v30
          exact cpsTripleWithin_weaken
            (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
            (h31own v29 v30)))
  have h29own := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x29) (P :=
      legacyKssDescriptorRest prefixLen inPtr hdrLen payloadLen outputBase
        suffixLen v10 v11 v12 old0 old1 old2 old3 old4 old5 F **
        regOwn .x31 ** regOwn .x30)
    (fun v29 => by
      exact cpsTripleWithin_weaken
        (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) (h30own v29))
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) h29own

theorem legacy_kss_in_fullCode
    (sp0 ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource) :
    let vals := kssEntryVals ret v8 v9 v18 v19 v20 v21 v22
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    cpsTripleWithin (19 + kssBodyFuelMulti segs) legacyKssB ret legacyFullCode
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsOwn kssFrame newSp **
        kssCallerPre segsBase outputBase segs os
          (List.replicate 32 (0 : BitVec 8)) v5 v6 v7 A source)
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost_multi segsBase outputBase segs A source) := by
  intro vals newSp
  have h := zkvm_keccak256_segments_spec_within sp0 ret segsBase outputBase
    segs os (List.replicate 32 (0 : BitVec 8))
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA halign_ret hos
    (by simp only [List.length_replicate]) hcount hsegs source
  change cpsTripleWithin (19 + kssBodyFuelMulti segs) KssB' ret kssCr _ _ at h
  exact cpsTripleWithin_extend_code legacyKss_mono h

theorem legacyKssRegs_factor (ret v8 v9 v18 v19 v20 v21 v22 : Word) :
    regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) =
      ((.x1 ↦ᵣ ret) **
        ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
          (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))) := by
  simp only [regsAt, kssFrame, kssEntryVals, List.foldr, sepConj_emp_right']

def legacyKssSregs (v8 v9 v18 v19 v20 v21 v22 : Word) : Assertion :=
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
    (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22)

theorem legacyKssSregs_pcFree (v8 v9 v18 v19 v20 v21 v22 : Word) :
    (legacyKssSregs v8 v9 v18 v19 v20 v21 v22).pcFree := by
  unfold legacyKssSregs
  repeat first | apply pcFree_sepConj | exact pcFree_regIs

def legacyKssCallPre (sp0 newSp segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (source : KssSource := kssDefaultSource) : Assertion :=
  (.x2 ↦ᵣ sp0) ** legacyKssSregs v8 v9 v18 v19 v20 v21 v22 **
    frameSlotsOwn kssFrame newSp **
    kssCallerPre segsBase outputBase segs os
      (List.replicate 32 (0 : BitVec 8)) v5 v6 v7 A source

def legacyKssCallPost (sp0 newSp ret segsBase outputBase : Word) (segs : List KssSeg)
    (v8 v9 v18 v19 v20 v21 v22 : Word) (A : Assertion)
    (source : KssSource := kssDefaultSource) : Assertion :=
  (.x2 ↦ᵣ sp0) ** legacyKssSregs v8 v9 v18 v19 v20 v21 v22 **
    frameSlotsSaved kssFrame newSp (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
    kssCallerPost_multi segsBase outputBase segs A source

theorem legacyKssCallPre_pcFree (sp0 newSp segsBase outputBase : Word)
    (segs : List KssSeg) (os : List (BitVec 8))
    (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word) (A : Assertion)
    (hA : A.pcFree) (source : KssSource := kssDefaultSource) :
    (legacyKssCallPre sp0 newSp segsBase outputBase segs os
      v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A source).pcFree := by
  unfold legacyKssCallPre
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj (legacyKssSregs_pcFree _ _ _ _ _ _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _)
        (kssCallerPre_pcFree _ _ _ _ _ _ _ _ _ hA source)))

theorem legacy_kss_ra_factored
    (sp0 ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource) :
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := 19 + kssBodyFuelMulti segs
    cpsTripleWithin fuel legacyKssB ret legacyFullCode
      (((.x1 ↦ᵣ ret) **
        legacyKssCallPre sp0 newSp segsBase outputBase segs os
          v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A source))
      (((.x1 ↦ᵣ ret) **
        legacyKssCallPost sp0 newSp ret segsBase outputBase segs
          v8 v9 v18 v19 v20 v21 v22 A source)) := by
  intro newSp fuel
  have hcore := legacy_kss_in_fullCode sp0 ret segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA halign_ret hos hcount hsegs source
  change cpsTripleWithin (19 + kssBodyFuelMulti segs) legacyKssB ret legacyFullCode
    ((.x2 ↦ᵣ sp0) **
      regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      frameSlotsOwn kssFrame newSp **
      kssCallerPre segsBase outputBase segs os
        (List.replicate 32 (0 : BitVec 8)) v5 v6 v7 A source)
    ((.x2 ↦ᵣ sp0) **
      regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      frameSlotsSaved kssFrame newSp (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      kssCallerPost_multi segsBase outputBase segs A source) at hcore
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hcore
  · unfold legacyKssCallPre legacyKssSregs at hp
    rw [legacyKssRegs_factor]
    xperm_hyp hp
  · unfold legacyKssCallPost legacyKssSregs
    rw [legacyKssRegs_factor] at hq
    xperm_hyp hq

theorem legacy_kss_callWithin
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
    cpsTripleWithin (1 + fuel) legacyKssJalPC ret legacyFullCode
      (((.x1 ↦ᵣ vOld) **
        (legacyKssCallPre sp0 newSp segsBase outputBase segs os
          v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A source ** F)))
      (((.x1 ↦ᵣ ret) **
        (legacyKssCallPost sp0 newSp ret segsBase outputBase segs
          v8 v9 v18 v19 v20 v21 v22 A source ** F))) := by
  intro ret newSp fuel
  have hret_even : (ret &&& ~~~(1 : Word)) = ret := legacyKssJal_ret_even
  have hcallee := legacy_kss_ra_factored sp0 ret segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA hret_even hos hcount hsegs source
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hP := pcFree_sepConj
    (legacyKssCallPre_pcFree sp0 newSp segsBase outputBase segs os
      v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA source) hF
  exact callWithin_spec legacyKssJalPC legacyKssB vOld legacyKssJalOff fuel
    legacyKssJal_target legacyKssJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)

/-! The byte-region representation zero-pads its final dword.  These two
    small equalities make that padding explicit when the terminator is fed by
    the prefix-copy postcondition. -/

theorem packBytes_append_zero_eq (bs : List (BitVec 8)) :
    packBytes bs = packBytes (bs ++ [0]) := by
  unfold packBytes
  congr 1
  funext i
  by_cases hi : i.val < bs.length
  · have hi' : i.val < bs.length + 1 := by omega
    simp [getByteAt, hi, hi']
  · have hi8 : i.val < 8 := i.isLt
    by_cases hi' : i.val < bs.length + 1
    · have heq : i.val = bs.length := by omega
      simp [getByteAt, heq]
    · simp [getByteAt, hi, hi']

theorem bytesRegion_append_zero_eq_of_length
    (base : Word) (bs : List (BitVec 8)) (hne : bs ≠ [])
    (h : bs.length + 1 ≤ 8) :
    bytesRegion base bs = bytesRegion base (bs ++ [0]) := by
  have hchunks : (bs.length + 7) / 8 = 1 := by
    have hlen : bs.length ≤ 7 := by omega
    interval_cases hbs : bs.length <;> simp_all
  have hchunks' : ((bs ++ [0]).length + 7) / 8 = 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  unfold bytesRegion
  rw [hchunks, hchunks']
  simp only [bytesRegionAux]
  have htake : bs.take 8 = bs :=
    (List.take_eq_self_iff bs).mpr (by omega)
  have htake' : (bs ++ [0]).take 8 = bs ++ [0] :=
    (List.take_eq_self_iff (bs ++ [0])).mpr (by simp; omega)
  rw [htake, htake']
  rw [sepConj_emp_right', sepConj_emp_right']
  exact congrArg (fun w : Word => (base ↦ₘ w))
    (packBytes_append_zero_eq bs)

theorem bytesRegion_len7_append_two_zero
    (base : Word) (bs : List (BitVec 8)) (h : bs.length = 7) :
    (bytesRegion base bs ** bytesRegion (base + 8) [0]) =
      bytesRegion base (bs ++ [0, 0]) := by
  have hfirst : bytesRegion base bs = bytesRegion base (bs ++ [0]) :=
    bytesRegion_append_zero_eq_of_length base bs (by
      intro hnil
      subst bs
      simp at h) (by omega)
  rw [hfirst]
  have hsplit := bytesRegion_append base (bs ++ [0]) [0] (by simp [h])
  have hlist : bs ++ [0, 0] = (bs ++ [0]) ++ [0] := by
    simp [List.append_assoc]
  rw [hlist, hsplit]
  have haddr : base + BitVec.ofNat 64 (bs ++ [0]).length = base + 8 := by
    simp [h]
  rw [haddr]

theorem bytesRegion_len8_append_two_zero
    (base : Word) (bs : List (BitVec 8)) (h : bs.length = 8) :
  (bytesRegion base bs ** bytesRegion (base + 8) [0]) =
      bytesRegion base (bs ++ [0, 0]) := by
  have hsplit := bytesRegion_append base bs [0, 0] (by simp [h])
  rw [hsplit]
  have haddr : base + BitVec.ofNat 64 bs.length = base + 8 := by
    simp [h]
  rw [haddr]
  have hone : bytesRegion (base + 8) [0] =
      bytesRegion (base + 8) [0, 0] := by
    exact bytesRegion_append_zero_eq_of_length (base + 8) [0]
      (by simp) (by decide)
  rw [hone]

theorem packBytes_append_two_zero_eq_of_length
    (bs : List (BitVec 8)) :
    packBytes bs = packBytes (bs ++ [0, 0]) := by
  unfold packBytes
  congr 1
  funext i
  by_cases hi : i.val < bs.length
  · have hi2 : i.val < bs.length + 2 := by omega
    simp [getByteAt, hi, hi2]
  · have hi8 : i.val < 8 := i.isLt
    by_cases hi2 : i.val < bs.length + 2
    · have hcases : i.val = bs.length ∨ i.val = bs.length + 1 := by omega
      rcases hcases with hcase | hcase
      · simp [getByteAt, hcase]
      · have hi_lt : bs.length + 1 < bs.length + 2 := by omega
        simp [getByteAt, hcase, hi_lt]
    · simp [getByteAt, hi, hi2]

theorem bytesRegion_append_two_zero_eq_of_length
    (base : Word) (bs : List (BitVec 8)) (hne : bs ≠ [])
    (h : bs.length + 2 ≤ 8) :
    bytesRegion base bs = bytesRegion base (bs ++ [0, 0]) := by
  have hlen : bs.length ≤ 6 := by omega
  have hchunks : (bs.length + 7) / 8 = 1 := by
    interval_cases hbs : bs.length <;> simp_all
  have hchunks' : ((bs ++ [0, 0]).length + 7) / 8 = 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  unfold bytesRegion
  rw [hchunks, hchunks']
  simp only [bytesRegionAux]
  have htake : bs.take 8 = bs := (List.take_eq_self_iff bs).mpr (by omega)
  have htake' : (bs ++ [0, 0]).take 8 = bs ++ [0, 0] :=
    (List.take_eq_self_iff (bs ++ [0, 0])).mpr (by simp; omega)
  rw [htake, htake']
  rw [sepConj_emp_right', sepConj_emp_right']
  exact congrArg (fun w : Word => (base ↦ₘ w))
    (packBytes_append_two_zero_eq_of_length bs)

theorem bytesRegion_append_two_zero_eq_of_length9
    (base : Word) (bs : List (BitVec 8)) (h : bs.length = 9) :
    bytesRegion base bs = bytesRegion base (bs ++ [0, 0]) := by
  have hchunks : (bs.length + 7) / 8 = 2 := by omega
  have hchunks' : ((bs ++ [0, 0]).length + 7) / 8 = 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  unfold bytesRegion
  rw [hchunks, hchunks']
  simp only [bytesRegionAux]
  have htake0' : (bs ++ [0, 0]).take 8 = bs.take 8 := by
    rw [List.take_append]
    simp [h]
  have hdrop' : (bs ++ [0, 0]).drop 8 = bs.drop 8 ++ [0, 0] := by
    rw [List.drop_append]
    simp [h]
  have hdrop_len : (bs.drop 8).length = 1 := by simp [h]
  have hdrop_take : (bs.drop 8).take 8 = bs.drop 8 :=
    (List.take_eq_self_iff _).mpr (by omega)
  have hdrop_append_take :
      (bs.drop 8 ++ [0, 0]).take 8 = bs.drop 8 ++ [0, 0] := by
    apply (List.take_eq_self_iff _).mpr
    simp [hdrop_len]
  rw [htake0', hdrop', hdrop_take, hdrop_append_take]
  exact congrArg (fun w : Word =>
      (base ↦ₘ packBytes (bs.take 8)) **
        ((base + 8 ↦ₘ w) ** empAssertion))
    (packBytes_append_two_zero_eq_of_length (bs.drop 8))

/-! The prefix-copy post owns only the logical chain bytes.  The terminator
    needs the dword containing the first terminator byte as well.  For chain
    encodings of seven or eight bytes that dword is the next caller-owned
    dword; for the zero-byte encoding it is the first dword.  All other
    lengths are already covered by the dwords in the copied window. -/

def legacyTailExtension (n : Nat) : Assertion :=
  if n = 0 then
    bytesRegion legacySuffixOutPtr [0, 0]
  else if n = 7 ∨ n = 8 then
    bytesRegion (legacySuffixOutPtr + 8) [0]
  else
    empAssertion

theorem legacyTailExtension_pcFree (n : Nat) :
    (legacyTailExtension n).pcFree := by
  unfold legacyTailExtension
  split
  · exact bytesRegion_pcFree _ _
  · split
    · exact bytesRegion_pcFree _ _
    · exact pcFree_emp

theorem legacyTail_region_bridge
    (n : Nat) (bs : List (BitVec 8))
    (hnsrc : n ≤ bs.length) (hnle : n ≤ 9) :
    (bytesRegion legacySuffixOutPtr (bs.take n) **
      legacyTailExtension n) =
      bytesRegion legacySuffixOutPtr (bs.take n ++ [0, 0]) := by
  by_cases h0 : n = 0
  · subst n
    simp [legacyTailExtension, sepConj_emp_left']
  have htake_ne : bs.take n ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_take, List.length_nil] at hlen
    omega
  by_cases hsmall : n + 2 ≤ 8
  · have htake_len : (bs.take n).length + 2 ≤ 8 := by
      rw [List.length_take]
      omega
    have hreg := bytesRegion_append_two_zero_eq_of_length
      legacySuffixOutPtr (bs.take n) htake_ne htake_len
    have hnot78 : ¬(n = 7 ∨ n = 8) := by omega
    simp only [legacyTailExtension, if_neg h0, if_neg hnot78,
      sepConj_emp_right']
    exact hreg
  by_cases h9 : n = 9
  · have hreg := bytesRegion_append_two_zero_eq_of_length9
      legacySuffixOutPtr (bs.take 9) (by
        rw [List.length_take]
        omega)
    simpa [legacyTailExtension, h9, sepConj_emp_right'] using hreg
  have h78 : n = 7 ∨ n = 8 := by omega
  rcases h78 with rfl | rfl
  · have hreg := bytesRegion_len7_append_two_zero
      legacySuffixOutPtr (bs.take 7) (by
        rw [List.length_take]
        omega)
    simpa [legacyTailExtension] using hreg
  · have hreg := bytesRegion_len8_append_two_zero
      legacySuffixOutPtr (bs.take 8) (by
        rw [List.length_take]
        omega)
    simpa [legacyTailExtension] using hreg

theorem legacyTail_set_terminators
    (n : Nat) (bs : List (BitVec 8)) (hnsrc : n ≤ bs.length) :
    (((bs.take n ++ [0, 0]).set n (BitVec.truncate 8 (128 : Word))).set
        (n + 1) (BitVec.truncate 8 (128 : Word))) =
      bs.take n ++ [BitVec.truncate 8 (128 : Word),
        BitVec.truncate 8 (128 : Word)] := by
  let xs : List (BitVec 8) := bs.take n
  have hlen : xs.length = n := by
    rw [List.length_take]
    omega
  let z : BitVec 8 := BitVec.truncate 8 (128 : Word)
  have hset0 : (xs ++ [0, 0]).set n z = xs ++ [z, 0] := by
    rw [List.set_eq_take_cons_drop _ (by simp [hlen])]
    simp [List.drop_append, hlen]
  have hset1 : (xs ++ [z, 0]).set (n + 1) z = xs ++ [z, z] := by
    have hidx : n + 1 < (xs ++ [z, 0]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.set_eq_take_cons_drop _ hidx]
    have htake : xs.take (n + 1) = xs :=
      (List.take_eq_self_iff xs).mpr (by omega)
    have hdrop : xs.drop (n + 2) = [] :=
      List.drop_eq_nil_of_le (by omega)
    have hsub : 2 ≤ n + 1 + 1 - n := by omega
    simp [List.take_append, List.drop_append, htake, hdrop,
      hlen, hsub]
  change (((xs ++ [0, 0]).set n z).set (n + 1) z) = xs ++ [z, z]
  rw [hset0, hset1]

def legacyTailOutputBytes (chainId : Word) : List (BitVec 8) :=
  let n := (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let encOld : List (BitVec 8) :=
    RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop n
  encOld.take n ++
    [BitVec.truncate 8 (128 : Word), BitVec.truncate 8 (128 : Word)]

theorem legacyTailOutputBytes_length (chainId : Word) :
    (legacyTailOutputBytes chainId).length =
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2 := by
  let n : Nat := (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  have hn : n ≤ 9 := by
    dsimp [n]
    have h := reubOut_length_le (chainBytes chainId) (by
      rw [chainBytes_length]
      decide)
    rw [chainBytes_length] at h
    omega
  dsimp [legacyTailOutputBytes, legacyChainEncOld, n]
  simp only [List.length_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil]
  have htake :
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length ≤
        (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length +
          (9 - (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length) := by
    omega
  rw [Nat.min_eq_left htake]

/-! ## The two-byte suffix terminator -/

theorem legacyTailTerminator_spec
    (suffix n : Word) (bs : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (halign : suffix.toNat % 8 = 0)
    (hfit : n.toNat + 2 ≤ bs.length)
    (hover : suffix.toNat + (n.toNat + 1) < 2 ^ 64)
    (hvalid : ∀ i, i < n.toNat + 2 →
      isValidByteAccess (suffix + BitVec.ofNat 64 i) = true)
    (hbound : n.toNat + 2 < 2 ^ 64) :
    cpsTripleWithin 4 (legacyH + 324) (legacyH + 340) legacyFullCode
      (((.x5 : Reg) ↦ᵣ (suffix + BitVec.ofNat 64 n.toNat)) **
        ((.x7 : Reg) ↦ᵣ n) ** regOwn .x31 **
        bytesRegion suffix bs ** F)
      (((.x5 : Reg) ↦ᵣ (suffix + BitVec.ofNat 64 n.toNat)) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n.toNat + 2)) **
        regOwn .x31 **
        bytesRegion suffix
          ((bs.set n.toNat (BitVec.truncate 8 (128 : Word))).set
            (n.toNat + 1) (BitVec.truncate 8 (128 : Word))) ** F) := by
  have hn : n.toNat < 2 ^ 64 := by omega
  have hn1 : n.toNat + 1 < 2 ^ 64 := by omega
  have hover0 : suffix.toNat + n.toNat < 2 ^ 64 := by omega
  have hli := li_spec_gen_own_within .x31 (128 : Word) (legacyH + 324) (by decide)
  have hli' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 324) 81 (.LI .x31 (128 : Word))
      (by decide) (by decide) (by intro h; rfl)) hli
  have hliF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (suffix + BitVec.ofNat 64 n.toNat)) **
      ((.x7 : Reg) ↦ᵣ n) ** bytesRegion suffix bs ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | assumption)
    hli'
  have hsb0 := bytesRegion_sb_within .x5 .x31 suffix (128 : Word)
    (legacyH + 328) bs n.toNat halign (by omega) hover0
    (hvalid n.toNat (by omega))
  have hsb0' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 328) 82 (.SB .x5 .x31 (0 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hsb0
  have hsb0F := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ n) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | assumption)
    hsb0'
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hsb0F
  have hsb1addr :
      (suffix + BitVec.ofNat 64 n.toNat) + signExtend12 (1 : BitVec 12) =
        suffix + BitVec.ofNat 64 (n.toNat + 1) := by
    have hone : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
    rw [hone]
    bv_omega
  have hsb1 := bytesRegion_sb_imm_within .x5 .x31 suffix
    (suffix + BitVec.ofNat 64 n.toNat) (128 : Word) (legacyH + 332)
    (bs.set n.toNat (BitVec.truncate 8 (128 : Word))) (n.toNat + 1) (1 : BitVec 12)
    halign (by simp only [List.length_set]; omega) hover
    hsb1addr (hvalid (n.toNat + 1) (by omega))
  have hsb1' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 332) 83 (.SB .x5 .x31 (1 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hsb1
  have hsb1F := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ n) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | assumption)
    hsb1'
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 hsb1F
  have hadd := addi_spec_gen_same_within .x7 n
    (2 : BitVec 12) (legacyH + 336) (by decide)
  have hadd' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 336) 84 (.ADDI .x7 .x7 (2 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hadd
  have haddF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (suffix + BitVec.ofNat 64 n.toNat)) **
      ((.x31 : Reg) ↦ᵣ (128 : Word)) **
      bytesRegion suffix
        ((bs.set n.toNat (BitVec.truncate 8 (128 : Word))).set
          (n.toNat + 1) (BitVec.truncate 8 (128 : Word))) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact bytesRegion_pcFree _ _
        | assumption)
    hadd'
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h12 haddF
  have hinc : n + signExtend12 (2 : BitVec 12) =
      BitVec.ofNat 64 (n.toNat + 2) := by
    have htwo : signExtend12 (2 : BitVec 12) = BitVec.ofNat 64 2 := by decide
    rw [htwo]
    bv_omega
  rw [hinc] at hseq
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      have hs :
          (
            ((.x31 : Reg) ↦ᵣ (128 : Word)) **
              ((.x5 : Reg) ↦ᵣ (suffix + BitVec.ofNat 64 n.toNat)) **
              ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n.toNat + 2)) **
              bytesRegion suffix
                ((bs.set n.toNat (BitVec.truncate 8 (128 : Word))).set
                  (n.toNat + 1) (BitVec.truncate 8 (128 : Word))) ** F
          ) h := by
        xperm_hyp hq
      have ho := sepConj_mono_left
        (regIs_to_regOwn .x31 (128 : Word)) h hs
      xperm_hyp ho) hseq

/-! Feed the copied chain bytes, plus the caller-owned extension dword, through
    the two stores at H+328/H+332.  The extension is consumed by the region
    bridge; the post therefore exposes the complete suffix with both 0x80
    terminator bytes and no duplicated ownership atom. -/

theorem legacyPrefixCopyThenTerminator_spec
    (chainId v21 : Word) (outBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (legacyH + 324) (legacyH + 340) legacyFullCode
      (legacyPrefixCopyPost chainId v21 outBytes
        (legacyTailExtension
          (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length ** F))
      (((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
        ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64
          ((RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2)) **
        ((.x5 : Reg) ↦ᵣ
          (legacySuffixOutPtr + BitVec.ofNat 64
            (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length)) **
        ((.x6 : Reg) ↦ᵣ
          (legacySuffixChainEncPtr + BitVec.ofNat 64
            (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 **
        ((.x21 : Reg) ↦ᵣ v21) **
        ((.x22 : Reg) ↦ᵣ
          (v21 +
            (BitVec.ofNat 64
              (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2))) **
        ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
        bytesRegion legacyLinkedChainEncPtr
          (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
            legacyChainEncOld.drop
              (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length) **
        bytesRegion legacyPrefixOutPtr
          (tshPrefixApply outBytes
            (v21 +
              (BitVec.ofNat 64
                (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2)).toNat) **
        (legacyPrefixCellPtr ↦ₘ BitVec.ofNat 64
          (tshPrefixNH
            (v21 +
              (BitVec.ofNat 64
                (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2)).toNat)) **
        bytesRegion legacySuffixOutPtr (legacyTailOutputBytes chainId) ** F) := by
  let n : Nat := (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let chainLen : Word := BitVec.ofNat 64 n
  let payloadLen : Word := v21 + (chainLen + 2)
  let encOld : List (BitVec 8) :=
    RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop n
  let inputBytes : List (BitVec 8) := encOld.take n ++ [0, 0]
  let outputBytes : List (BitVec 8) := encOld.take n ++
    [BitVec.truncate 8 (128 : Word), BitVec.truncate 8 (128 : Word)]
  have hn_le : n ≤ 9 := by
    dsimp [n]
    have h := reubOut_length_le (chainBytes chainId) (by
      rw [chainBytes_length]
      decide)
    rw [chainBytes_length] at h
    omega
  have hchainLen_toNat : chainLen.toNat = n := by
    dsimp [chainLen]
    exact toNat_ofNat_lt (by omega)
  have hn_src : n ≤ encOld.length := by
    dsimp [encOld]
    simp only [List.length_append, List.length_drop]
    omega
  have htake_len : (encOld.take n).length = n := by
    rw [List.length_take]
    omega
  have hinput_len : inputBytes.length = n + 2 := by
    dsimp [inputBytes]
    simp [htake_len]
  have houtput_eq : outputBytes = legacyTailOutputBytes chainId := by
    rfl
  have hregion := legacyTail_region_bridge n encOld hn_src hn_le
  have hset := legacyTail_set_terminators n encOld hn_src
  have hregion' := hregion
  dsimp [n, encOld] at hregion'
  have hset' := hset
  dsimp [n, encOld] at hset'
  have houtput_eq' := houtput_eq
  dsimp [outputBytes, encOld, n] at houtput_eq'
  have hregionF :
      (bytesRegion legacySuffixOutPtr (encOld.take n) **
        (legacyTailExtension n ** F)) =
      (bytesRegion legacySuffixOutPtr inputBytes ** F) := by
    rw [← sepConj_assoc']
    rw [hregion]
  have hregionF' := hregionF
  dsimp [n, encOld, inputBytes] at hregionF'
  let Fterm : Assertion :=
    ((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
      ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
      ((.x6 : Reg) ↦ᵣ
        (legacySuffixChainEncPtr + BitVec.ofNat 64 n)) **
      ((.x28 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
      ((.x21 : Reg) ↦ᵣ v21) ** ((.x22 : Reg) ↦ᵣ payloadLen) **
      ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
      bytesRegion legacyLinkedChainEncPtr encOld **
      bytesRegion legacyPrefixOutPtr
        (tshPrefixApply outBytes payloadLen.toNat) **
      (legacyPrefixCellPtr ↦ₘ BitVec.ofNat 64
        (tshPrefixNH payloadLen.toNat)) ** F
  have hFterm : Fterm.pcFree := by
    unfold Fterm
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  have hvalid : ∀ i, i < n + 2 →
      isValidByteAccess (legacySuffixOutPtr + BitVec.ofNat 64 i) = true := by
    intro i hi
    have hi11 : i ≤ 10 := by omega
    interval_cases i <;> decide
  have hover : legacySuffixOutPtr.toNat + (n + 1) < 2 ^ 64 := by
    have h : legacySuffixOutPtr.toNat + 10 < 2 ^ 64 := by decide
    omega
  have hterm := legacyTailTerminator_spec legacySuffixOutPtr chainLen inputBytes
    Fterm hFterm (by decide) (by omega)
    (by simpa [hchainLen_toNat] using hover)
    (by
      intro i hi
      apply hvalid i
      simpa [hchainLen_toNat] using hi)
    (by omega)
  rw [hchainLen_toNat] at hterm
  exact cpsTripleWithin_weaken
    (P :=
      ((.x5 : Reg) ↦ᵣ (legacySuffixOutPtr + BitVec.ofNat 64 n)) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** regOwn .x31 **
        bytesRegion legacySuffixOutPtr inputBytes ** Fterm)
    (P' := legacyPrefixCopyPost chainId v21 outBytes
      (legacyTailExtension n ** F))
    (Q :=
      ((.x5 : Reg) ↦ᵣ (legacySuffixOutPtr + BitVec.ofNat 64 n)) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 2)) ** regOwn .x31 **
        bytesRegion legacySuffixOutPtr
          (((inputBytes.set n (BitVec.truncate 8 (128 : Word))).set
            (n + 1) (BitVec.truncate 8 (128 : Word)))) ** Fterm)
    (Q' := _)
    (fun _ hp => by
      dsimp [legacyPrefixCopyPost, Fterm, inputBytes, encOld, chainLen,
        payloadLen, n] at hp ⊢
      rw [hregionF'] at hp
      xperm_hyp hp)
    (fun _ hq => by
      dsimp [Fterm, outputBytes, inputBytes, encOld, chainLen, payloadLen, n] at hq ⊢
      rw [hset'] at hq
      rw [houtput_eq'] at hq
      xperm_hyp hq)
    hterm

end EvmAsm.Codegen.TxSigningHashLegacyTailCompose
