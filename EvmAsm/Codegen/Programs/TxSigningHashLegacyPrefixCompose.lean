/-
  K146 prefix-call composition.

  The `rlp_encode_list_prefix` call is at H+260 in the linked
  `tx_signing_hash_legacy_eip155` body.  This module lifts the deployed
  per-form prefix contracts into the K146 union, then assembles their
  contiguous short/long cover at that call site.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyUintCompose
import EvmAsm.Codegen.Programs.TxSigningHashSpecPrefix

namespace EvmAsm.Codegen.TxSigningHashLegacyPrefixCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.TxSigningHashLegacySpec
open EvmAsm.Codegen.TxSigningHashLegacyCompose
open EvmAsm.Codegen.TxSigningHashLegacyChainCompose
open EvmAsm.Codegen.TxSigningHashLegacyUintCompose
open EvmAsm.Codegen.TxSigningHashLegacyLoopSpec
open EvmAsm.Codegen.TxSigningHashSpec
open EvmAsm.EL.RLP

abbrev legacyPrefixJalPC : Word := legacyH + (260 : Word)
abbrev legacyPrefixOutPtrPC : Word := legacyH + (244 : Word)
abbrev legacyPrefixCellPtrPC : Word := legacyH + (252 : Word)
abbrev legacySuffixOutPtrPC : Word := legacyH + (272 : Word)
abbrev legacySuffixChainEncPtrPC : Word := legacyH + (284 : Word)
abbrev legacyPrefixOutPtr : Word := BitVec.ofNat 64 GuestAddrs.t155_buf
abbrev legacySuffixOutPtr : Word := legacyPrefixOutPtr + (64 : Word)
abbrev legacyPrefixCellPtr : Word := BitVec.ofNat 64 GuestAddrs.t155_prefix_len
abbrev legacySuffixChainEncPtr : Word := legacyLinkedChainEncPtr

def legacyPrefixJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_encode_list_prefix
    (GuestAddrs.tx_signing_hash_legacy_eip155 + 260)

theorem legacyPrefixJal_target :
    legacyPrefixJalPC + signExtend21 legacyPrefixJalOff = legacyPrefixB := by
  unfold legacyPrefixJalPC legacyPrefixJalOff legacyH legacyPrefixB
  decide

theorem legacyPrefixJal_ret_even :
    ((legacyPrefixJalPC + 4) &&& ~~~(1 : Word)) = legacyPrefixJalPC + 4 := by
  unfold legacyPrefixJalPC legacyH
  decide

theorem legacyPrefixJal_mem :
    ∀ a i, CodeReq.singleton legacyPrefixJalPC (.JAL .x1 legacyPrefixJalOff) a = some i →
      legacyFullCode a = some i := by
  intro a i hi
  have hmem := legacy_mem_at (legacyH + 260) 65
    (.JAL .x1 (Codegen.jalOff GuestAddrs.rlp_encode_list_prefix
      (GuestAddrs.tx_signing_hash_legacy_eip155 + 260))) (by decide)
    (by decide) (by intro h; rfl)
  exact hmem a i (by
    rw [show legacyPrefixJalPC = legacyH + 260 by decide,
      show legacyPrefixJalOff = Codegen.jalOff GuestAddrs.rlp_encode_list_prefix
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 260) by rfl] at hi
    exact hi)

theorem legacy_la_prefix_out_hi :
    Codegen.laHi GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 244) =
      Rv64.laHi legacyPrefixOutPtrPC legacyPrefixOutPtr := by
  decide

theorem legacy_la_prefix_out_lo :
    Codegen.laLo GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 244) =
      Rv64.laLo legacyPrefixOutPtrPC legacyPrefixOutPtr := by
  decide

theorem legacy_la_prefix_out_range :
    laInRange legacyPrefixOutPtrPC legacyPrefixOutPtr := by
  decide

theorem legacyPrefixOutPtr_spec (v11 : Word) :
    cpsTripleWithin 2 (legacyH + 244) (legacyH + 252) legacyFullCode
      (.x11 ↦ᵣ v11) (.x11 ↦ᵣ legacyPrefixOutPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 244)
        (.AUIPC .x11 (Rv64.laHi legacyPrefixOutPtrPC legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 244) 61
      (.AUIPC .x11 (Codegen.laHi GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 244))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_prefix_out_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 244) + 4)
        (.ADDI .x11 .x11 (Rv64.laLo legacyPrefixOutPtrPC legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 248) 62
      (.ADDI .x11 .x11 (Codegen.laLo GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 244))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 244 : Word) + 4 = legacyH + 248 := by decide
    rw [hpc, ← legacy_la_prefix_out_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x11 v11 legacyPrefixOutPtrPC
    legacyPrefixOutPtr (by decide) legacy_la_prefix_out_range hau had
  rw [show (legacyH + 244 : Word) + 8 = legacyH + 252 from by decide] at hla
  exact hla

theorem legacy_la_prefix_cell_hi :
    Codegen.laHi GuestAddrs.t155_prefix_len
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 252) =
      Rv64.laHi legacyPrefixCellPtrPC legacyPrefixCellPtr := by
  decide

theorem legacy_la_prefix_cell_lo :
    Codegen.laLo GuestAddrs.t155_prefix_len
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 252) =
      Rv64.laLo legacyPrefixCellPtrPC legacyPrefixCellPtr := by
  decide

theorem legacy_la_prefix_cell_range :
    laInRange legacyPrefixCellPtrPC legacyPrefixCellPtr := by
  decide

theorem legacyPrefixCellPtr_spec (v12 : Word) :
    cpsTripleWithin 2 (legacyH + 252) (legacyH + 260) legacyFullCode
      (.x12 ↦ᵣ v12) (.x12 ↦ᵣ legacyPrefixCellPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 252)
        (.AUIPC .x12 (Rv64.laHi legacyPrefixCellPtrPC legacyPrefixCellPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 252) 63
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.t155_prefix_len
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 252))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_prefix_cell_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 252) + 4)
        (.ADDI .x12 .x12 (Rv64.laLo legacyPrefixCellPtrPC legacyPrefixCellPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 256) 64
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.t155_prefix_len
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 252))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 252 : Word) + 4 = legacyH + 256 := by decide
    rw [hpc, ← legacy_la_prefix_cell_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x12 v12 legacyPrefixCellPtrPC
    legacyPrefixCellPtr (by decide) legacy_la_prefix_cell_range hau had
  rw [show (legacyH + 252 : Word) + 8 = legacyH + 260 from by decide] at hla
  exact hla

/-! ## Suffix-loop argument setup at H+272 -/

theorem legacy_la_suffix_out_hi :
    Codegen.laHi GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 272) =
      Rv64.laHi legacySuffixOutPtrPC legacyPrefixOutPtr := by
  decide

theorem legacy_la_suffix_out_lo :
    Codegen.laLo GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 272) =
      Rv64.laLo legacySuffixOutPtrPC legacyPrefixOutPtr := by
  decide

theorem legacy_la_suffix_out_range :
    laInRange legacySuffixOutPtrPC legacyPrefixOutPtr := by
  decide

/-- The suffix destination is `t155_buf + 64`, materialised at H+272. -/
theorem legacySuffixOutPtr_spec (v5 : Word) :
    cpsTripleWithin 3 (legacyH + 272) (legacyH + 284) legacyFullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ legacySuffixOutPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 272)
        (.AUIPC .x5 (Rv64.laHi legacySuffixOutPtrPC legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 272) 68
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 272))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_suffix_out_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 272) + 4)
        (.ADDI .x5 .x5 (Rv64.laLo legacySuffixOutPtrPC legacyPrefixOutPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 276) 69
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.t155_buf
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 272))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 272 : Word) + 4 = legacyH + 276 := by decide
    rw [hpc, ← legacy_la_suffix_out_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x5 v5 legacySuffixOutPtrPC
    legacyPrefixOutPtr (by decide) legacy_la_suffix_out_range hau had
  rw [show (legacyH + 272 : Word) + 8 = legacyH + 280 from by decide] at hla
  have hadd := addi_spec_gen_same_within .x5 legacyPrefixOutPtr
    (64 : BitVec 12) (legacyH + 280) (by decide)
  rw [show legacyPrefixOutPtr + signExtend12 (64 : BitVec 12) =
      legacySuffixOutPtr by rfl] at hadd
  have hadd' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 280) 70 (.ADDI .x5 .x5 (64 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hadd
  exact cpsTripleWithin_seq_same_cr hla hadd'

theorem legacy_la_suffix_chain_enc_hi :
    Codegen.laHi GuestAddrs.t155_chain_enc
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 284) =
      Rv64.laHi legacySuffixChainEncPtrPC legacySuffixChainEncPtr := by
  decide

theorem legacy_la_suffix_chain_enc_lo :
    Codegen.laLo GuestAddrs.t155_chain_enc
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 284) =
      Rv64.laLo legacySuffixChainEncPtrPC legacySuffixChainEncPtr := by
  decide

theorem legacy_la_suffix_chain_enc_range :
    laInRange legacySuffixChainEncPtrPC legacySuffixChainEncPtr := by
  decide

theorem legacySuffixChainEncPtr_spec (v6 : Word) :
    cpsTripleWithin 2 (legacyH + 284) (legacyH + 292) legacyFullCode
      (.x6 ↦ᵣ v6) (.x6 ↦ᵣ legacySuffixChainEncPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 284)
        (.AUIPC .x6 (Rv64.laHi legacySuffixChainEncPtrPC legacySuffixChainEncPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 284) 71
      (.AUIPC .x6 (Codegen.laHi GuestAddrs.t155_chain_enc
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 284))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_suffix_chain_enc_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 284) + 4)
        (.ADDI .x6 .x6 (Rv64.laLo legacySuffixChainEncPtrPC legacySuffixChainEncPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 288) 72
      (.ADDI .x6 .x6 (Codegen.laLo GuestAddrs.t155_chain_enc
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 284))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 284 : Word) + 4 = legacyH + 288 := by decide
    rw [hpc, ← legacy_la_suffix_chain_enc_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x6 v6 legacySuffixChainEncPtrPC
    legacySuffixChainEncPtr (by decide) legacy_la_suffix_chain_enc_range hau had
  rw [show (legacyH + 284 : Word) + 8 = legacyH + 292 from by decide] at hla
  exact hla

/-! ## Prefix body in the K146 code requirement

    The reusable K145 prefix theorems are tied to K145's `fullCode`, whose
    caller and Nth entries live at different linked addresses.  The K146
    composition therefore starts from the deployed prefix-only contracts and
    lifts those directly into `legacyFullCode`; importing a K145 `fullCode`
    triple here would be a false code-membership bridge. -/

theorem legacy_prefix_short_in_code
    (len outPtr cellPtr raVal v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 8 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_short_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v6 v7 outBytes cellOld
    h_len h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_of_lt_56 outBytes len.toNat h_len h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (1 : Word) := by
    rw [tshPrefixNH_of_lt_56 len.toNat h_len]; rfl
  simpa [legacyPrefixCode, happly, hnh] using h

def legacyPrefixLongPre
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word) : Assertion :=
  (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
   ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
   ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
   ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
   ((.x0 : Reg) ↦ᵣ (0 : Word)) **
   bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))

def legacyPrefixLongPost
    (len outPtr cellPtr raVal : Word)
    (outBytes : List (BitVec 8)) : Assertion :=
  (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
   ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
   regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
   ((.x0 : Reg) ↦ᵣ (0 : Word)) **
   bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
   (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)))

theorem legacy_prefix_long1_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 56 ≤ len.toNat)
    (h_len_hi : len.toNat < 256)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 1 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 22 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_long1_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_long1 outBytes len.toNat h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (2 : Word) := by
    rw [tshPrefixNH_long1 len.toNat h_len_lo h_len_hi]; rfl
  simpa [legacyPrefixCode, happly, hnh] using h

theorem legacy_prefix_long2_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 256 ≤ len.toNat)
    (h_len_hi : len.toNat < 65536)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 2 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 32 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (legacyPrefixLongPre len outPtr cellPtr raVal v5 v28 v29 v30 v31 outBytes cellOld)
      (legacyPrefixLongPost len outPtr cellPtr raVal outBytes) := by
  have h := RlpEncodeListPrefixLong2Spec.rlp_encode_list_prefix_long2_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_long2 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (3 : Word) := by
    rw [tshPrefixNH_long2 len.toNat h_len_lo h_len_hi]; rfl
  simpa [legacyPrefixCode, legacyPrefixLongPre, legacyPrefixLongPost, happly, hnh] using h

theorem legacy_prefix_long3_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 65536 ≤ len.toNat)
    (h_len_hi : len.toNat < 16777216)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 3 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 42 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (legacyPrefixLongPre len outPtr cellPtr raVal v5 v28 v29 v30 v31 outBytes cellOld)
      (legacyPrefixLongPost len outPtr cellPtr raVal outBytes) := by
  have h := RlpEncodeListPrefixLong3Spec.rlp_encode_list_prefix_long3_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_long3 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (4 : Word) := by
    rw [tshPrefixNH_long3 len.toNat h_len_lo h_len_hi]; rfl
  simpa [legacyPrefixCode, legacyPrefixLongPre, legacyPrefixLongPost, happly, hnh] using h

theorem legacy_prefix_long4_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 16777216 ≤ len.toNat)
    (h_len_hi : len.toNat < 4294967296)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 4 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 52 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (legacyPrefixLongPre len outPtr cellPtr raVal v5 v28 v29 v30 v31 outBytes cellOld)
      (legacyPrefixLongPost len outPtr cellPtr raVal outBytes) := by
  have h := RlpEncodeListPrefixLong4Spec.rlp_encode_list_prefix_long4_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_long4 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (5 : Word) := by
    rw [tshPrefixNH_long4 len.toNat h_len_lo h_len_hi]; rfl
  simpa [legacyPrefixCode, legacyPrefixLongPre, legacyPrefixLongPost, happly, hnh] using h

theorem legacy_prefix_long5_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 4294967296 ≤ len.toNat)
    (h_len_hi : len.toNat < 1099511627776)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 5 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 62 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (legacyPrefixLongPre len outPtr cellPtr raVal v5 v28 v29 v30 v31 outBytes cellOld)
      (legacyPrefixLongPost len outPtr cellPtr raVal outBytes) := by
  have h := RlpEncodeListPrefixLong5Spec.rlp_encode_list_prefix_long5_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_long5 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (6 : Word) := by
    rw [tshPrefixNH_long5 len.toNat h_len_lo h_len_hi]; rfl
  simpa [legacyPrefixCode, legacyPrefixLongPre, legacyPrefixLongPost, happly, hnh] using h

theorem legacy_prefix_long6_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 1099511627776 ≤ len.toNat)
    (h_len_hi : len.toNat < 281474976710656)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 6 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 72 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (legacyPrefixLongPre len outPtr cellPtr raVal v5 v28 v29 v30 v31 outBytes cellOld)
      (legacyPrefixLongPost len outPtr cellPtr raVal outBytes) := by
  have h := RlpEncodeListPrefixLong6Spec.rlp_encode_list_prefix_long6_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_long6 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (7 : Word) := by
    rw [tshPrefixNH_long6 len.toNat h_len_lo h_len_hi]; rfl
  simpa [legacyPrefixCode, legacyPrefixLongPre, legacyPrefixLongPost, happly, hnh] using h

theorem legacy_prefix_long7_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 281474976710656 ≤ len.toNat)
    (h_len_hi : len.toNat < 72057594037927936)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 7 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 82 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (legacyPrefixLongPre len outPtr cellPtr raVal v5 v28 v29 v30 v31 outBytes cellOld)
      (legacyPrefixLongPost len outPtr cellPtr raVal outBytes) := by
  have h := RlpEncodeListPrefixLong7Spec.rlp_encode_list_prefix_long7_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_long7 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (8 : Word) := by
    rw [tshPrefixNH_long7 len.toNat h_len_lo h_len_hi]; rfl
  simpa [legacyPrefixCode, legacyPrefixLongPre, legacyPrefixLongPost, happly, hnh] using h

theorem legacy_prefix_long8_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 72057594037927936 ≤ len.toNat)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 90 legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (legacyPrefixLongPre len outPtr cellPtr raVal v5 v28 v29 v30 v31 outBytes cellOld)
      (legacyPrefixLongPost len outPtr cellPtr raVal outBytes) := by
  have h := RlpEncodeListPrefixLong8Spec.rlp_encode_list_prefix_long8_pinned_spec_within
    legacyPrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_long8 outBytes len h_len_lo len.isLt h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (9 : Word) := by
    rw [tshPrefixNH_long8 len.toNat h_len_lo len.isLt]; rfl
  simpa [legacyPrefixCode, legacyPrefixLongPre, legacyPrefixLongPost, happly, hnh] using h

theorem legacy_prefix_long_any_in_code
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 56 ≤ len.toNat)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin tshPrefixFuel legacyPrefixB (raVal &&& ~~~1) legacyPrefixCode
      (legacyPrefixLongPre len outPtr cellPtr raVal v5 v28 v29 v30 v31 outBytes cellOld)
      (legacyPrefixLongPost len outPtr cellPtr raVal outBytes) := by
  have hlen1 : 1 < outBytes.length := by omega
  have hlen2 : 2 < outBytes.length := by omega
  have hlen3 : 3 < outBytes.length := by omega
  have hlen4 : 4 < outBytes.length := by omega
  have hlen5 : 5 < outBytes.length := by omega
  have hlen6 : 6 < outBytes.length := by omega
  have hlen7 : 7 < outBytes.length := by omega
  by_cases c1 : len.toNat < 256
  · exact cpsTripleWithin_mono_nSteps (by decide : 22 ≤ tshPrefixFuel)
      (legacy_prefix_long1_in_code len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld h_len_lo c1 h_out_align hlen1 h_out_valid)
  by_cases c2 : len.toNat < 65536
  · exact cpsTripleWithin_mono_nSteps (by decide : 32 ≤ tshPrefixFuel)
      (legacy_prefix_long2_in_code len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c2 h_out_align hlen2 h_out_valid)
  by_cases c3 : len.toNat < 16777216
  · exact cpsTripleWithin_mono_nSteps (by decide : 42 ≤ tshPrefixFuel)
      (legacy_prefix_long3_in_code len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c3 h_out_align hlen3 h_out_valid)
  by_cases c4 : len.toNat < 4294967296
  · exact cpsTripleWithin_mono_nSteps (by decide : 52 ≤ tshPrefixFuel)
      (legacy_prefix_long4_in_code len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c4 h_out_align hlen4 h_out_valid)
  by_cases c5 : len.toNat < 1099511627776
  · exact cpsTripleWithin_mono_nSteps (by decide : 62 ≤ tshPrefixFuel)
      (legacy_prefix_long5_in_code len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c5 h_out_align hlen5 h_out_valid)
  by_cases c6 : len.toNat < 281474976710656
  · exact cpsTripleWithin_mono_nSteps (by decide : 72 ≤ tshPrefixFuel)
      (legacy_prefix_long6_in_code len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c6 h_out_align hlen6 h_out_valid)
  by_cases c7 : len.toNat < 72057594037927936
  · exact cpsTripleWithin_mono_nSteps (by decide : 82 ≤ tshPrefixFuel)
      (legacy_prefix_long7_in_code len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c7 h_out_align hlen7 h_out_valid)
  exact legacy_prefix_long8_in_code len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld (by omega) h_out_align h_out_len h_out_valid

theorem legacy_prefix_short_apply_callWithin
    (vOld len outPtr cellPtr v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := legacyPrefixJalPC + 4
    cpsTripleWithin (1 + 8) legacyPrefixJalPC ret legacyFullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) := by
  intro ret
  have hret_eq : (ret &&& ~~~(1 : Word)) = ret := legacyPrefixJal_ret_even
  have hcore := legacy_prefix_short_in_code len outPtr cellPtr ret v5 v6 v7
    outBytes cellOld h_len h_out_align h_out_len h_out_valid
  rw [hret_eq] at hcore
  have hcallee0 := cpsTripleWithin_extend_code legacyPrefix_mono hcore
  have hcallee : cpsTripleWithin 8 legacyPrefixB ret legacyFullCode
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hP : ((((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  exact callWithin_spec legacyPrefixJalPC legacyPrefixB vOld legacyPrefixJalOff 8
    legacyPrefixJal_target legacyPrefixJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)

theorem legacy_prefix_long_any_callWithin
    (vOld len outPtr cellPtr v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_len_lo : 56 ≤ len.toNat)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := legacyPrefixJalPC + 4
    cpsTripleWithin (1 + tshPrefixFuel) legacyPrefixJalPC ret legacyFullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x28 **
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) := by
  intro ret
  have hret_eq : (ret &&& ~~~(1 : Word)) = ret := legacyPrefixJal_ret_even
  have hcore := legacy_prefix_long_any_in_code len outPtr cellPtr ret v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_out_align h_out_len h_out_valid
  rw [hret_eq] at hcore
  have hcallee0 := cpsTripleWithin_extend_code legacyPrefix_mono hcore
  have hcallee : cpsTripleWithin tshPrefixFuel legacyPrefixB ret legacyFullCode
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x28 **
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))))) := by
    simpa [legacyPrefixLongPre, legacyPrefixLongPost] using hcallee0
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hret : ret = legacyPrefixJalPC + 4 := by rfl
  rw [hret] at hcalleeF
  have hP : ((((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  exact callWithin_spec legacyPrefixJalPC legacyPrefixB vOld legacyPrefixJalOff tshPrefixFuel
    legacyPrefixJal_target legacyPrefixJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)

private theorem legacy_open_regs_28_31 (v28 v29 v30 v31 : Word) (P : Assertion) (h : _)
    (hq : ((.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P) h) :
    (regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** P) h := by
  have s28 : ((.x28 ↦ᵣ v28) **
      ((.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by xperm_hyp hq
  have o28 := sepConj_mono_left (regIs_to_regOwn .x28 v28) h s28
  have s29 : ((.x29 ↦ᵣ v29) **
      (regOwn .x28 ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by xperm_hyp o28
  have o29 := sepConj_mono_left (regIs_to_regOwn .x29 v29) h s29
  have s30 : ((.x30 ↦ᵣ v30) **
      (regOwn .x29 ** regOwn .x28 ** (.x31 ↦ᵣ v31) ** P)) h := by xperm_hyp o29
  have o30 := sepConj_mono_left (regIs_to_regOwn .x30 v30) h s30
  have s31 : ((.x31 ↦ᵣ v31) **
      (regOwn .x30 ** regOwn .x29 ** regOwn .x28 ** P)) h := by xperm_hyp o30
  have o31 := sepConj_mono_left (regIs_to_regOwn .x31 v31) h s31
  xperm_hyp o31

private theorem legacy_open_regs_6_7 (v6 v7 : Word) (P : Assertion) (h : _)
    (hq : ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** P) h) :
    (regOwn .x6 ** regOwn .x7 ** P) h := by
  have s6 : ((.x6 ↦ᵣ v6) ** ((.x7 ↦ᵣ v7) ** P)) h := by xperm_hyp hq
  have o6 := sepConj_mono_left (regIs_to_regOwn .x6 v6) h s6
  have s7 : ((.x7 ↦ᵣ v7) ** (regOwn .x6 ** P)) h := by xperm_hyp o6
  have o7 := sepConj_mono_left (regIs_to_regOwn .x7 v7) h s7
  xperm_hyp o7

/-- The short/long prefix call is a single K146 call site.

    The two deployed prefix contracts use different temporary registers: the
    short form owns `x5-x7`, while the long forms own `x5,x28-x31`.  The
    caller has both sets in its frame, so each branch is lifted back to the
    common post with all seven temporaries owned. -/
theorem legacy_prefix_any_callWithin
    (vOld len outPtr cellPtr v5 v6 v7 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := legacyPrefixJalPC + 4
    cpsTripleWithin (1 + tshPrefixFuel) legacyPrefixJalPC ret legacyFullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) := by
  intro ret
  by_cases hshort : len.toNat < 56
  · let Fshort : Assertion :=
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) ** F
    have hFshort : Fshort.pcFree := by
      unfold Fshort
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF
    have hC := legacy_prefix_short_apply_callWithin vOld len outPtr cellPtr v5 v6 v7
      outBytes cellOld Fshort hFshort hshort h_out_align (by omega) h_out_valid
    refine cpsTripleWithin_mono_nSteps (by decide : 1 + 8 ≤ 1 + tshPrefixFuel) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [Fshort] at hp ⊢
        xperm_hyp hp)
      (fun h hq => by
        simp only [Fshort, ret] at hq ⊢
        have hq' :
            ((.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
              ((.x1 ↦ᵣ ret) **
                ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ cellPtr) **
                 regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
                 (.x0 ↦ᵣ (0 : Word)) **
                 bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
                 (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) h := by
          xperm_hyp hq
        have opened := legacy_open_regs_28_31 v28 v29 v30 v31 _ h hq'
        xperm_hyp opened) hC
  · let Flong : Assertion :=
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** F
    have hFlong : Flong.pcFree := by
      unfold Flong
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF
    have hL := legacy_prefix_long_any_callWithin vOld len outPtr cellPtr v5 v28 v29 v30 v31
      outBytes cellOld Flong hFlong (by omega) h_out_align h_out_len h_out_valid
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [Flong] at hp ⊢
        xperm_hyp hp)
      (fun h hq => by
        simp only [Flong, ret] at hq ⊢
        have hq' :
            ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
              ((.x1 ↦ᵣ ret) **
                ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ cellPtr) **
                 regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
                 regOwn .x31 **
                 (.x0 ↦ᵣ (0 : Word)) **
                 bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
                 (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) h := by
          xperm_hyp hq
        have opened := legacy_open_regs_6_7 v6 v7 _ h hq'
        xperm_hyp opened) hL

/-- Owned-register form of the K146 prefix call.

    The setup preceding the call leaves the prefix temporaries owned rather
    than valued.  Peel those ownership atoms only after proving the call for
    every concrete valuation; the deployed short/long branch theorem above
    then supplies the common output. -/
theorem legacy_prefix_any_callWithin_own
    (vOld len outPtr cellPtr v28 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := legacyPrefixJalPC + 4
    cpsTripleWithin (1 + tshPrefixFuel) legacyPrefixJalPC ret legacyFullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x28 : Reg) ↦ᵣ v28) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)) **
       regOwns [.x5, .x6, .x7, .x29, .x30, .x31])
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 **
         regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) := by
  intro ret
  let P0 : Assertion :=
    ((.x1 : Reg) ↦ᵣ vOld) ** ((.x10 : Reg) ↦ᵣ len) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F
  let Q0 : Assertion :=
    ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
      (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F
  have hP0 : P0.pcFree := by
    dsimp [P0]
    pcf
    exact hF
  have hforall : ∀ vf : Reg → Word,
      cpsTripleWithin (1 + tshPrefixFuel) legacyPrefixJalPC ret legacyFullCode
        (P0 ** regAtomsOf vf [.x5, .x6, .x7, .x29, .x30, .x31]) Q0 := by
    intro vf
    have h := legacy_prefix_any_callWithin vOld len outPtr cellPtr
      (vf .x5) (vf .x6) (vf .x7) v28 (vf .x29) (vf .x30) (vf .x31)
      outBytes cellOld F hF h_out_align h_out_len h_out_valid
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [P0, regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right'] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [Q0] at hq ⊢
        xperm_hyp hq) h
  have hpeel := cpsTripleWithin_peel_regOwns
    [.x5, .x6, .x7, .x29, .x30, .x31] (by decide) hforall
  simpa [P0, Q0] using hpeel

def legacyPrefixSetupPost (chainId v21 : Word) (F : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
  ((.x10 : Reg) ↦ᵣ (v21 +
    (BitVec.ofNat 64
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2))) **
  ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
  ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
  ((.x21 : Reg) ↦ᵣ v21) **
  ((.x22 : Reg) ↦ᵣ (v21 +
    (BitVec.ofNat 64
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2))) **
  ((.x28 : Reg) ↦ᵣ
    (BitVec.ofNat 64
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2)) **
  ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
  regOwn .x31 ** bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
  bytesRegion legacyLinkedChainEncPtr
    (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop
        (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length) ** F

theorem legacyPrefixSetup_spec
    (chainId v21 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (legacyH + 228) (legacyH + 260) legacyFullCode
      (legacyChainUintPost chainId F **
        ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22)
      (legacyPrefixSetupPost chainId v21 F) := by
  let chainLen : Word := BitVec.ofNat 64
    (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let chainEncBytes : List (BitVec 8) :=
    RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      EvmAsm.Codegen.TxSigningHashLegacyUintCompose.legacyChainEncOld.drop
        (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let legacyChainEncOld := chainEncBytes
  let payloadLen : Word := v21 + (chainLen + 2)
  let P0 : Assertion :=
    ((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
    ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
    ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
    ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
    bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F
  have hfor : ∀ v22 v28, cpsTripleWithin 8 (legacyH + 228) (legacyH + 260)
      legacyFullCode ((P0 ** ((.x22 : Reg) ↦ᵣ v22)) ** ((.x28 : Reg) ↦ᵣ v28))
      (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
       ((.x10 : Reg) ↦ᵣ payloadLen) ** ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
       ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) ** ((.x21 : Reg) ↦ᵣ v21) **
       ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** ((.x18 : Reg) ↦ᵣ chainId) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
       bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F) := by
    intro v22 v28
    have h0 := mv_spec_gen_within .x28 .x10 chainLen v28
      (legacyH + 228) (by decide)
    have h0' := cpsTripleWithin_extend_code
      (legacy_mem_at (legacyH + 228) 57 (.MV .x28 .x10)
        (by decide) (by decide) (by intro h; rfl)) h0
    have h0F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
       ((.x11 : Reg) ↦ᵣ (8 : Word)) **
       ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
       ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
       ((.x22 : Reg) ↦ᵣ v22) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
       bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
      (by pcf; exact hF) h0'
    have h0W : cpsTripleWithin 1 (legacyH + 228) (legacyH + 232)
        legacyFullCode ((P0 ** ((.x22 : Reg) ↦ᵣ v22)) ** ((.x28 : Reg) ↦ᵣ v28))
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ v22) ** ((.x28 : Reg) ↦ᵣ chainLen) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F) := by
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) h0F
    have h1 := addi_spec_gen_same_within .x28 chainLen
      (2 : BitVec 12) (legacyH + 232) (by decide)
    rw [show chainLen + signExtend12 (2 : BitVec 12) = chainLen + 2 by
      rw [show signExtend12 (2 : BitVec 12) = (2 : Word) by decide]] at h1
    have h1' := cpsTripleWithin_extend_code
      (legacy_mem_at (legacyH + 232) 58 (.ADDI .x28 .x28 (2 : BitVec 12))
        (by decide) (by decide) (by intro h; rfl)) h1
    have h1F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
       ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
       ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
       ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
       ((.x22 : Reg) ↦ᵣ v22) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
       bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
      (by pcf; exact hF) h1'
    have h1W : cpsTripleWithin 1 (legacyH + 232) (legacyH + 236)
        legacyFullCode
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
       ((.x22 : Reg) ↦ᵣ v22) ** ((.x28 : Reg) ↦ᵣ chainLen) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ v22) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F) := by
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) h1F
    have h2 := add_spec_gen_within .x22 .x21 .x28 v21 (chainLen + 2) v22
      (legacyH + 236) (by decide)
    rw [show v21 + (chainLen + 2) = payloadLen by rfl] at h2
    have h2' := cpsTripleWithin_extend_code
      (legacy_mem_at (legacyH + 236) 59 (.ADD .x22 .x21 .x28)
        (by decide) (by decide) (by intro h; rfl)) h2
    have h2F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
       ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
       ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
       ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
       bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
      (by pcf; exact hF) h2'
    have h2W : cpsTripleWithin 1 (legacyH + 236) (legacyH + 240)
        legacyFullCode
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ v22) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F) := by
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) h2F
    have h3 := mv_spec_gen_within .x10 .x22 payloadLen chainLen
      (legacyH + 240) (by decide)
    have h3' := cpsTripleWithin_extend_code
      (legacy_mem_at (legacyH + 240) 60 (.MV .x10 .x22)
        (by decide) (by decide) (by intro h; rfl)) h3
    have h3F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
       ((.x11 : Reg) ↦ᵣ (8 : Word)) **
       ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
       ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
       ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
       bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
      (by pcf; exact hF) h3'
    have h3W : cpsTripleWithin 1 (legacyH + 240) (legacyH + 244)
        legacyFullCode
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ chainLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ payloadLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F) := by
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) h3F
    have h4 := legacyPrefixOutPtr_spec (8 : Word)
    have h4F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
       ((.x10 : Reg) ↦ᵣ payloadLen) **
       ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
       ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
       ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
       bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
      (by pcf; exact hF) h4
    have h4W : cpsTripleWithin 2 (legacyH + 244) (legacyH + 252)
        legacyFullCode
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ payloadLen) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ payloadLen) ** ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F) := by
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) h4F
    have h5 := legacyPrefixCellPtr_spec legacyLinkedChainEncPtr
    have h5F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
       ((.x10 : Reg) ↦ᵣ payloadLen) ** ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
       ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
       ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
       bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
      (by pcf; exact hF) h5
    have h5W : cpsTripleWithin 2 (legacyH + 252) (legacyH + 260)
        legacyFullCode
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ payloadLen) ** ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
         ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
        (((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
         ((.x10 : Reg) ↦ᵣ payloadLen) ** ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
         ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
         ((.x18 : Reg) ↦ᵣ chainId) ** ((.x21 : Reg) ↦ᵣ v21) **
         ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
         bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F) := by
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) 
        (fun _ hq => by xperm_hyp hq) h5F
    have hseq01 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) h0W h1W
    have hseq012 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hseq01 h2W
    have hseq0123 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hseq012 h3W
    have hseq0124 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hseq0123 h4W
    have hseq := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hseq0124 h5W
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by xperm_hyp hq) hseq
  have hown28 (v22 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x28) (fun v28 => hfor v22 v28)
  have hfor22 (v22 : Word) :=
    cpsTripleWithin_weaken
      (P := (P0 ** ((.x22 : Reg) ↦ᵣ v22)) ** regOwn .x28)
      (P' := (P0 ** regOwn .x28) ** ((.x22 : Reg) ↦ᵣ v22))
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (hown28 v22)
  have hown22 := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x22) (fun v22 => hfor22 v22)
  have hweak := cpsTripleWithin_weaken
    (P := (P0 ** regOwn .x28) ** regOwn .x22)
    (P' := legacyChainUintPost chainId F **
      ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22)
    (Q := ((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
      ((.x10 : Reg) ↦ᵣ payloadLen) ** ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
      ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) ** ((.x21 : Reg) ↦ᵣ v21) **
      ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x28 : Reg) ↦ᵣ (chainLen + 2)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
      bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F)
    (Q' := legacyPrefixSetupPost chainId v21 F)
    (fun _ hp => by
      dsimp [P0, legacyChainUintPost] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp [legacyPrefixSetupPost, payloadLen, chainLen] at hq ⊢
      xperm_hyp hq) hown22
  simpa [legacyPrefixSetupPost, payloadLen, chainLen] using hweak

/-- Compose the chain-id setup with the following deployed prefix call.

    The setup leaves `x5-x7` and `x29-x31` owned and materialises `x28` as
    the payload-prefix offset.  The owned-register adapter above is exactly
    the bridge needed to feed that state to the short/long prefix dispatcher. -/
theorem legacyPrefixSetupPrefix_spec
    (chainId v21 : Word) (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (8 + (1 + tshPrefixFuel))
      (legacyH + 228) (legacyPrefixJalPC + 4) legacyFullCode
      (legacyChainUintPost chainId
          (bytesRegion legacyPrefixOutPtr outBytes **
            (legacyPrefixCellPtr ↦ₘ cellOld) ** F) **
        ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22)
      (((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
        ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
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
                (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length + 2)).toNat)) ** F) := by
  let chainLen : Word := BitVec.ofNat 64
    (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let payloadLen : Word := v21 + (chainLen + 2)
  let encOld : List (BitVec 8) :=
    RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop
        (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let Fsetup : Assertion :=
    bytesRegion legacyPrefixOutPtr outBytes **
      (legacyPrefixCellPtr ↦ₘ cellOld) ** F
  have hFsetup : Fsetup.pcFree := by
    dsimp [Fsetup]
    pcf
    exact hF
  have hsetup := legacyPrefixSetup_spec chainId v21 Fsetup hFsetup
  let Fown : Assertion :=
    ((.x21 : Reg) ↦ᵣ v21) **
      ((.x22 : Reg) ↦ᵣ payloadLen) **
      ((.x18 : Reg) ↦ᵣ chainId) **
      bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
      bytesRegion legacyLinkedChainEncPtr encOld ** F
  have hFown : Fown.pcFree := by
    dsimp [Fown]
    pcf
    exact hF
  have hcall := legacy_prefix_any_callWithin_own
    (legacyUintJalPC + 4) payloadLen legacyPrefixOutPtr legacyPrefixCellPtr
    (chainLen + 2) outBytes cellOld Fown hFown
    (by decide) h_out_len h_out_valid
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [legacyPrefixSetupPost, Fsetup, Fown, payloadLen, chainLen, encOld] at hp ⊢
      simp only [sepConj_emp_right'] at hp ⊢
      xperm_hyp hp)
    hsetup hcall
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [legacyPrefixSetupPost, Fsetup, Fown, payloadLen, chainLen, encOld] at hp ⊢
      xperm_hyp hp)
      (fun _ hq => by
      dsimp [legacyPrefixSetupPost, Fsetup, Fown, payloadLen, chainLen, encOld] at hq ⊢
      xperm_hyp hq) hseq

/-! ## Suffix-loop argument setup at H+264 -/

/-- The arithmetic and pointer setup immediately before the suffix-copy loop.

    This is kept at concrete register values so the following loop can consume
    the resulting `x5`, `x6`, and `x28` values directly.  The owned-register
    adapter below is the caller-facing form. -/
theorem legacyPrefixSuffixSetup_concrete_spec
    (payloadLen v21 chainLen v5 v6 v7 v28 : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_payload : payloadLen = v21 + (chainLen + 2)) :
    cpsTripleWithin 8 (legacyH + 264) (legacyH + 296) legacyFullCode
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ v7) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) ** F)
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
        ((.x6 : Reg) ↦ᵣ legacySuffixChainEncPtr) **
        ((.x28 : Reg) ↦ᵣ chainLen) ** F) := by
  have hsub := sub_spec_gen_within .x7 .x22 .x21 payloadLen v21 v7
    (legacyH + 264) (by decide)
  have hsubVal : payloadLen - v21 = chainLen + 2 := by
    rw [h_payload]
    bv_omega
  rw [hsubVal] at hsub
  have hsub' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 264) 66 (.SUB .x7 .x22 .x21)
      (by decide) (by decide) (by intro h; rfl)) hsub
  have hsubF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x28 : Reg) ↦ᵣ v28) ** F)
    (by pcf; exact hF) hsub'
  have hsubW : cpsTripleWithin 1 (legacyH + 264) (legacyH + 268)
      legacyFullCode
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ v7) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) ** F)
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ (chainLen + 2)) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsubF
  have hadd := addi_spec_gen_same_within .x7 (chainLen + 2)
    (-2 : BitVec 12) (legacyH + 268) (by decide)
  have haddVal : (chainLen + 2) + signExtend12 (-2 : BitVec 12) = chainLen := by
    rw [show signExtend12 (-2 : BitVec 12) = (-2 : Word) by decide]
    bv_omega
  rw [haddVal] at hadd
  have hadd' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 268) 67 (.ADDI .x7 .x7 (-2 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hadd
  have haddF := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x28 : Reg) ↦ᵣ v28) ** F)
    (by pcf; exact hF) hadd'
  have haddW : cpsTripleWithin 1 (legacyH + 268) (legacyH + 272)
      legacyFullCode
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ (chainLen + 2)) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) ** F)
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) haddF
  have h5 := legacySuffixOutPtr_spec v5
  have h5F := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
      ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x28 : Reg) ↦ᵣ v28) ** F)
    (by pcf; exact hF) h5
  have h5W : cpsTripleWithin 3 (legacyH + 272) (legacyH + 284)
      legacyFullCode
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) ** F)
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h5F
  have h6 := legacySuffixChainEncPtr_spec v6
  have h6F := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
      ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
      ((.x28 : Reg) ↦ᵣ v28) ** F)
    (by pcf; exact hF) h6
  have h6W : cpsTripleWithin 2 (legacyH + 284) (legacyH + 292)
      legacyFullCode
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) ** F)
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
        ((.x6 : Reg) ↦ᵣ legacySuffixChainEncPtr) **
        ((.x28 : Reg) ↦ᵣ v28) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h6F
  have hmv := mv_spec_gen_within .x28 .x7 chainLen v28
    (legacyH + 292) (by decide)
  have hmv' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 292) 73 (.MV .x28 .x7)
      (by decide) (by decide) (by intro h; rfl)) hmv
  have hmvF := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
      ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
      ((.x6 : Reg) ↦ᵣ legacySuffixChainEncPtr) ** F)
    (by pcf; exact hF) hmv'
  have hmvW : cpsTripleWithin 1 (legacyH + 292) (legacyH + 296)
      legacyFullCode
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
        ((.x6 : Reg) ↦ᵣ legacySuffixChainEncPtr) **
        ((.x28 : Reg) ↦ᵣ v28) ** F)
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
        ((.x6 : Reg) ↦ᵣ legacySuffixChainEncPtr) **
        ((.x28 : Reg) ↦ᵣ chainLen) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hmvF
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsubW haddW
  have h012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 h5W
  have h0123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h012 h6W
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h0123 hmvW

/-- Caller-facing form of the suffix setup.  The four temporaries are owned at
    the prefix post and are peeled only after the concrete setup has been
    proved for every valuation. -/
theorem legacyPrefixSuffixSetup_own_spec
    (payloadLen v21 chainLen : Word) (F : Assertion) (hF : F.pcFree)
    (h_payload : payloadLen = v21 + (chainLen + 2)) :
    cpsTripleWithin 8 (legacyH + 264) (legacyH + 296) legacyFullCode
      ((((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) ** F) **
        regOwns [.x5, .x6, .x7, .x28])
      (((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
        ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
        ((.x6 : Reg) ↦ᵣ legacySuffixChainEncPtr) **
        ((.x28 : Reg) ↦ᵣ chainLen) ** F) := by
  let P0 : Assertion :=
    ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) ** F
  let Q0 : Assertion :=
    ((.x22 : Reg) ↦ᵣ payloadLen) ** ((.x21 : Reg) ↦ᵣ v21) **
      ((.x7 : Reg) ↦ᵣ chainLen) ** ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
      ((.x6 : Reg) ↦ᵣ legacySuffixChainEncPtr) **
      ((.x28 : Reg) ↦ᵣ chainLen) ** F
  have hP0 : P0.pcFree := by
    dsimp [P0]
    pcf
    exact hF
  have hforall : ∀ vf : Reg → Word,
      cpsTripleWithin 8 (legacyH + 264) (legacyH + 296) legacyFullCode
        (P0 ** regAtomsOf vf [.x5, .x6, .x7, .x28]) Q0 := by
    intro vf
    have h := legacyPrefixSuffixSetup_concrete_spec payloadLen v21 chainLen
      (vf .x5) (vf .x6) (vf .x7) (vf .x28) F hF h_payload
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [P0, regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right'] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [Q0] at hq ⊢
        xperm_hyp hq) h
  have hpeel := cpsTripleWithin_peel_regOwns
    [.x5, .x6, .x7, .x28] (by decide) hforall
  simpa [P0, Q0] using hpeel

def legacyPrefixSuffixPost
    (chainId v21 : Word) (outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  let chainLen : Word := BitVec.ofNat 64
    (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let payloadLen : Word := v21 + (chainLen + 2)
  let encOld : List (BitVec 8) :=
    RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop
        (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  ((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
    ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
    ((.x7 : Reg) ↦ᵣ chainLen) **
    ((.x5 : Reg) ↦ᵣ legacySuffixOutPtr) **
    ((.x6 : Reg) ↦ᵣ legacySuffixChainEncPtr) **
    ((.x28 : Reg) ↦ᵣ chainLen) **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    ((.x21 : Reg) ↦ᵣ v21) ** ((.x22 : Reg) ↦ᵣ payloadLen) **
    ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
    bytesRegion legacyLinkedChainEncPtr encOld **
    bytesRegion legacyPrefixOutPtr
      (tshPrefixApply outBytes payloadLen.toNat) **
    (legacyPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F

/-- Prefix setup followed by the suffix-loop argument setup. -/
theorem legacyPrefixSetupSuffix_spec
    (chainId v21 : Word) (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (8 + (1 + tshPrefixFuel) + 8)
      (legacyH + 228) (legacyH + 296) legacyFullCode
      (legacyChainUintPost chainId
          (bytesRegion legacyPrefixOutPtr outBytes **
            (legacyPrefixCellPtr ↦ₘ cellOld) ** F) **
        ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22)
      (legacyPrefixSuffixPost chainId v21 outBytes F) := by
  let chainLen : Word := BitVec.ofNat 64
    (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let payloadLen : Word := v21 + (chainLen + 2)
  let encOld : List (BitVec 8) :=
    RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop
        (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let Fsetup : Assertion :=
    bytesRegion legacyPrefixOutPtr outBytes **
      (legacyPrefixCellPtr ↦ₘ cellOld) ** F
  have hFsetup : Fsetup.pcFree := by
    dsimp [Fsetup]
    pcf
    exact hF
  have hprefix := legacyPrefixSetupPrefix_spec chainId v21 outBytes cellOld
    F hF h_out_len h_out_valid
  let Fsuffix : Assertion :=
    ((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
      ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
      bytesRegion legacyLinkedChainEncPtr encOld **
      bytesRegion legacyPrefixOutPtr
        (tshPrefixApply outBytes payloadLen.toNat) **
      (legacyPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) ** F
  have hFsuffix : Fsuffix.pcFree := by
    dsimp [Fsuffix]
    pcf
    exact hF
  have hsuffix := legacyPrefixSuffixSetup_own_spec payloadLen v21 chainLen
    Fsuffix hFsuffix (by rfl)
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [legacyPrefixSetupPost, Fsetup, Fsuffix, payloadLen, chainLen, encOld]
        at hp ⊢
      simp only [sepConj_emp_right'] at hp ⊢
      xperm_hyp hp)
    hprefix hsuffix
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by
      dsimp [legacyPrefixSuffixPost, Fsuffix, payloadLen, chainLen, encOld] at hq ⊢
      xperm_hyp hq) hseq

end EvmAsm.Codegen.TxSigningHashLegacyPrefixCompose
