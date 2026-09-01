/-
  K146 successful-arm body continuation.

  The dispatcher/Nth-call composition lives in
  `TxSigningHashLegacyCompose`.  This module starts at the first instruction
  after a successful Nth result and keeps the linked cell reloads and
  payload-length arithmetic explicit.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyCompose

namespace EvmAsm.Codegen.TxSigningHashLegacyBodyCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashLegacySpec
open EvmAsm.Codegen.TxSigningHashLegacyCompose

abbrev legacyBodyOffPtrPC : Word := legacyH + 128
abbrev legacyBodyLenPtrPC : Word := legacyH + 140

theorem legacy_la_body_off_hi :
    Codegen.laHi GuestAddrs.t155_offset_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 128) =
      Rv64.laHi legacyBodyOffPtrPC legacyLinkedNthOffPtr := by
  decide

theorem legacy_la_body_off_lo :
    Codegen.laLo GuestAddrs.t155_offset_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 128) =
      Rv64.laLo legacyBodyOffPtrPC legacyLinkedNthOffPtr := by
  decide

theorem legacy_la_body_off_range :
    laInRange legacyBodyOffPtrPC legacyLinkedNthOffPtr := by
  decide

theorem legacyBodyOffPtr_spec (v5 : Word) :
    cpsTripleWithin 2 (legacyH + 128) (legacyH + 136) legacyFullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ legacyLinkedNthOffPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 128)
        (.AUIPC .x5 (Rv64.laHi legacyBodyOffPtrPC legacyLinkedNthOffPtr)) a = some i →
        legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 128) 32
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.t155_offset_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 128))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_body_off_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 128) + 4)
        (.ADDI .x5 .x5 (Rv64.laLo legacyBodyOffPtrPC legacyLinkedNthOffPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 132) 33
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.t155_offset_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 128))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 128 : Word) + 4 = legacyH + 132 := by decide
    rw [hpc, ← legacy_la_body_off_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x5 v5 legacyBodyOffPtrPC
    legacyLinkedNthOffPtr (by decide) legacy_la_body_off_range hau had
  rw [show (legacyH + 128 : Word) + 8 = legacyH + 136 from by decide] at hla
  exact hla

theorem legacy_la_body_len_hi :
    Codegen.laHi GuestAddrs.t155_length_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 140) =
      Rv64.laHi legacyBodyLenPtrPC legacyLinkedNthLenPtr := by
  decide

theorem legacy_la_body_len_lo :
    Codegen.laLo GuestAddrs.t155_length_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 140) =
      Rv64.laLo legacyBodyLenPtrPC legacyLinkedNthLenPtr := by
  decide

theorem legacy_la_body_len_range :
    laInRange legacyBodyLenPtrPC legacyLinkedNthLenPtr := by
  decide

theorem legacyBodyLenPtr_spec (v5 : Word) :
    cpsTripleWithin 2 (legacyH + 140) (legacyH + 148) legacyFullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ legacyLinkedNthLenPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 140)
        (.AUIPC .x5 (Rv64.laHi legacyBodyLenPtrPC legacyLinkedNthLenPtr)) a = some i →
        legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 140) 35
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.t155_length_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 140))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_body_len_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 140) + 4)
        (.ADDI .x5 .x5 (Rv64.laLo legacyBodyLenPtrPC legacyLinkedNthLenPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 144) 36
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.t155_length_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 140))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 140 : Word) + 4 = legacyH + 144 := by decide
    rw [hpc, ← legacy_la_body_len_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x5 v5 legacyBodyLenPtrPC
    legacyLinkedNthLenPtr (by decide) legacy_la_body_len_range hau had
  rw [show (legacyH + 140 : Word) + 8 = legacyH + 148 from by decide] at hla
  exact hla

theorem legacyBodyOffLoad_spec (oldOff offVal : Word) :
    cpsTripleWithin 1 (legacyH + 136) (legacyH + 140) legacyFullCode
      ((.x5 ↦ᵣ legacyLinkedNthOffPtr) ** (.x6 ↦ᵣ oldOff) **
        (legacyLinkedNthOffPtr ↦ₘ offVal))
      ((.x5 ↦ᵣ legacyLinkedNthOffPtr) ** (.x6 ↦ᵣ offVal) **
        (legacyLinkedNthOffPtr ↦ₘ offVal)) := by
  have hld := ld_spec_gen_within .x6 .x5 legacyLinkedNthOffPtr oldOff offVal
    (0 : BitVec 12) (legacyH + 136) (by decide)
  rw [show legacyLinkedNthOffPtr + signExtend12 (0 : BitVec 12) =
      legacyLinkedNthOffPtr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide]
    bv_omega] at hld
  have hld' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 136) 34
      (.LD .x6 .x5 (0 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) hld
  exact hld'

theorem legacyBodyLenLoad_spec (oldLen lenVal : Word) :
    cpsTripleWithin 1 (legacyH + 148) (legacyH + 152) legacyFullCode
      ((.x5 ↦ᵣ legacyLinkedNthLenPtr) ** (.x7 ↦ᵣ oldLen) **
        (legacyLinkedNthLenPtr ↦ₘ lenVal))
      ((.x5 ↦ᵣ legacyLinkedNthLenPtr) ** (.x7 ↦ᵣ lenVal) **
        (legacyLinkedNthLenPtr ↦ₘ lenVal)) := by
  have hld := ld_spec_gen_within .x7 .x5 legacyLinkedNthLenPtr oldLen lenVal
    (0 : BitVec 12) (legacyH + 148) (by decide)
  rw [show legacyLinkedNthLenPtr + signExtend12 (0 : BitVec 12) =
      legacyLinkedNthLenPtr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide]
    bv_omega] at hld
  have hld' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 148) 37
      (.LD .x7 .x5 (0 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) hld
  exact hld'

theorem legacyBodyPayloadArithmetic_spec
    (v5 v6 v7 v21 offVal lenVal hdrLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (legacyH + 128) (legacyH + 160) legacyFullCode
      ((((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F))
      ((((.x5 ↦ᵣ legacyLinkedNthLenPtr) **
          (.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal) **
          (.x20 ↦ᵣ hdrLen) **
          (.x21 ↦ᵣ ((offVal + lenVal) - hdrLen)) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)) := by
  have h0 := legacyBodyOffPtr_spec v5
  have h0F := cpsTripleWithin_frameR
    (((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ v21) ** (legacyLinkedNthOffPtr ↦ₘ offVal) **
      (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)
    (by pcf; exact hF) h0
  have h0W : cpsTripleWithin 2 (legacyH + 128) (legacyH + 136)
      legacyFullCode
      ((((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F))
      ((((.x5 ↦ᵣ legacyLinkedNthOffPtr) ** (.x6 ↦ᵣ v6) **
          (.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := legacyBodyOffLoad_spec v6 offVal
  have h1F := cpsTripleWithin_frameR
    (((.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
      (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)
    (by pcf; exact hF) h1
  have h1W : cpsTripleWithin 1 (legacyH + 136) (legacyH + 140)
      legacyFullCode
      ((((.x5 ↦ᵣ legacyLinkedNthOffPtr) ** (.x6 ↦ᵣ v6) **
          (.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F))
      ((((.x5 ↦ᵣ legacyLinkedNthOffPtr) ** (.x6 ↦ᵣ offVal) **
          (.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have h2 := legacyBodyLenPtr_spec legacyLinkedNthOffPtr
  have h2F := cpsTripleWithin_frameR
    (((.x6 ↦ᵣ offVal) ** (.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ v21) ** (legacyLinkedNthOffPtr ↦ₘ offVal) **
      (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)
    (by pcf; exact hF) h2
  have h2W : cpsTripleWithin 2 (legacyH + 140) (legacyH + 148)
      legacyFullCode
      ((((.x5 ↦ᵣ legacyLinkedNthOffPtr) ** (.x6 ↦ᵣ offVal) **
          (.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F))
      ((((.x5 ↦ᵣ legacyLinkedNthLenPtr) ** (.x6 ↦ᵣ offVal) **
          (.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  have h3 := legacyBodyLenLoad_spec v7 lenVal
  have h3F := cpsTripleWithin_frameR
    (((.x6 ↦ᵣ offVal) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
      (legacyLinkedNthOffPtr ↦ₘ offVal)) ** F)
    (by pcf; exact hF) h3
  have h3W : cpsTripleWithin 1 (legacyH + 148) (legacyH + 152)
      legacyFullCode
      ((((.x5 ↦ᵣ legacyLinkedNthLenPtr) ** (.x6 ↦ᵣ offVal) **
          (.x7 ↦ᵣ v7) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F))
      ((((.x5 ↦ᵣ legacyLinkedNthLenPtr) ** (.x6 ↦ᵣ offVal) **
          (.x7 ↦ᵣ lenVal) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h3F
  have h4 := add_spec_gen_rd_eq_rs1_within .x6 .x7 offVal lenVal
    (legacyH + 152) (by decide)
  have h4' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 152) 38
      (.ADD .x6 .x6 .x7) (by decide) (by decide)
      (by intro h; rfl)) h4
  have h4F := cpsTripleWithin_frameR
    (((.x5 ↦ᵣ legacyLinkedNthLenPtr) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ v21) ** (legacyLinkedNthOffPtr ↦ₘ offVal) **
      (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)
    (by pcf; exact hF) h4'
  have h4W : cpsTripleWithin 1 (legacyH + 152) (legacyH + 156)
      legacyFullCode
      ((((.x5 ↦ᵣ legacyLinkedNthLenPtr) ** (.x6 ↦ᵣ offVal) **
          (.x7 ↦ᵣ lenVal) ** (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F))
      ((((.x5 ↦ᵣ legacyLinkedNthLenPtr) **
          (.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal) **
          (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h4F
  have h5 := sub_spec_gen_within .x21 .x6 .x20
    (offVal + lenVal) hdrLen v21
    (legacyH + 156) (by decide)
  have h5' := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 156) 39
      (.SUB .x21 .x6 .x20) (by decide) (by decide)
      (by intro h; rfl)) h5
  have h5F := cpsTripleWithin_frameR
    (((.x5 ↦ᵣ legacyLinkedNthLenPtr) ** (.x7 ↦ᵣ lenVal) **
      (legacyLinkedNthOffPtr ↦ₘ offVal) **
      (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)
    (by pcf; exact hF) h5'
  have h5W : cpsTripleWithin 1 (legacyH + 156) (legacyH + 160)
      legacyFullCode
      ((((.x5 ↦ᵣ legacyLinkedNthLenPtr) **
          (.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal) **
          (.x20 ↦ᵣ hdrLen) ** (.x21 ↦ᵣ v21) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F))
      ((((.x5 ↦ᵣ legacyLinkedNthLenPtr) **
          (.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal) **
          (.x20 ↦ᵣ hdrLen) **
          (.x21 ↦ᵣ ((offVal + lenVal) - hdrLen)) **
          (legacyLinkedNthOffPtr ↦ₘ offVal) **
          (legacyLinkedNthLenPtr ↦ₘ lenVal)) ** F)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h5F
  have h01 := cpsTripleWithin_seq_same_cr h0W h1W
  have h012 := cpsTripleWithin_seq_same_cr h01 h2W
  have h0123 := cpsTripleWithin_seq_same_cr h012 h3W
  have h01234 := cpsTripleWithin_seq_same_cr h0123 h4W
  exact cpsTripleWithin_seq_same_cr h01234 h5W

end EvmAsm.Codegen.TxSigningHashLegacyBodyCompose
