/-
  Walk body setup after frame (#11799): pc11→pc35.

  11-16 MV save ABI into x8/x9/x18-21
  17-26 copy 32B root hash from a0 → mw_lookup_hash
  27-34 wl ABI (a0=witness, a1=witLen, a2=hash, a3/a4=off/len BSS)
  STOPS before JAL witness_lookup_by_hash at pc35 (SEPARATE residual).
-/

import EvmAsm.Codegen.Programs.MptWalkLeafHp
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec

set_option maxRecDepth 8000

private theorem la_setup_hash_hi :
    laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 68) =
      EvmAsm.Rv64.laHi (pc 17) MwLookupHash := by
  unfold pc walkB MwLookupHash EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_setup_hash_lo :
    laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 68) =
      EvmAsm.Rv64.laLo (pc 17) MwLookupHash := by
  unfold pc walkB MwLookupHash EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_setup_hash_range : laInRange (pc 17) MwLookupHash := by
  unfold pc walkB MwLookupHash laInRange; decide

private theorem la_setup_wl_hash_hi :
    laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 116) =
      EvmAsm.Rv64.laHi (pc 29) MwLookupHash := by
  unfold pc walkB MwLookupHash EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_setup_wl_hash_lo :
    laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 116) =
      EvmAsm.Rv64.laLo (pc 29) MwLookupHash := by
  unfold pc walkB MwLookupHash EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_setup_wl_hash_range : laInRange (pc 29) MwLookupHash := by
  unfold pc walkB MwLookupHash laInRange; decide

private theorem la_setup_wl_off_hi :
    laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 124) =
      EvmAsm.Rv64.laHi (pc 31) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_setup_wl_off_lo :
    laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 124) =
      EvmAsm.Rv64.laLo (pc 31) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_setup_wl_off_range : laInRange (pc 31) MwLookupOff := by
  unfold pc walkB MwLookupOff laInRange; decide

private theorem la_setup_wl_len_hi :
    laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 132) =
      EvmAsm.Rv64.laHi (pc 33) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_setup_wl_len_lo :
    laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 132) =
      EvmAsm.Rv64.laLo (pc 33) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_setup_wl_len_range : laInRange (pc 33) MwLookupLen := by
  unfold pc walkB MwLookupLen laInRange; decide

private theorem pc_add8_su (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem signExtend12_0s : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem signExtend12_8s : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem signExtend12_16s : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem signExtend12_24s : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide

/-- ABI save MVs pc11→pc17. -/
theorem setup_abi_mvs
    (v8 v9 v18 v19 v20 v21 : Word)
    (witBase witLen pathPtr pathLen valOut valOutLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 6 (pc 11) (pc 17) fullCode
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
       (.x11 ↦ᵣ witBase) ** (.x12 ↦ᵣ witLen) **
       (.x13 ↦ᵣ pathPtr) ** (.x14 ↦ᵣ pathLen) **
       (.x15 ↦ᵣ valOut) ** (.x16 ↦ᵣ valOutLen) ** F)
      ((.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** (.x18 ↦ᵣ pathPtr) **
       (.x19 ↦ᵣ pathLen) ** (.x20 ↦ᵣ valOut) ** (.x21 ↦ᵣ valOutLen) **
       (.x11 ↦ᵣ witBase) ** (.x12 ↦ᵣ witLen) **
       (.x13 ↦ᵣ pathPtr) ** (.x14 ↦ᵣ pathLen) **
       (.x15 ↦ᵣ valOut) ** (.x16 ↦ᵣ valOutLen) ** F) := by
  have h0 := mv_spec_gen_within .x8 .x11 witBase v8 (pc 11) (by decide)
  have h0c := cpsTripleWithin_extend_code
    (walkMem (pc 11) 11 (.MV .x8 .x11)
      (by decide) (by unfold pc walkB; decide) rfl) h0
  rw [pc_succ 11] at h0c
  have h0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
     (.x21 ↦ᵣ v21) ** (.x12 ↦ᵣ witLen) ** (.x13 ↦ᵣ pathPtr) **
     (.x14 ↦ᵣ pathLen) ** (.x15 ↦ᵣ valOut) ** (.x16 ↦ᵣ valOutLen) ** F)
    (by pcf; exact hF) h0c
  have h1 := mv_spec_gen_within .x9 .x12 witLen v9 (pc 12) (by decide)
  have h1c := cpsTripleWithin_extend_code
    (walkMem (pc 12) 12 (.MV .x9 .x12)
      (by decide) (by unfold pc walkB; decide) rfl) h1
  rw [pc_succ 12] at h1c
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ witBase) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
     (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ witBase) ** (.x13 ↦ᵣ pathPtr) **
     (.x14 ↦ᵣ pathLen) ** (.x15 ↦ᵣ valOut) ** (.x16 ↦ᵣ valOutLen) ** F)
    (by pcf; exact hF) h1c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0F h1F
  have h2 := mv_spec_gen_within .x18 .x13 pathPtr v18 (pc 13) (by decide)
  have h2c := cpsTripleWithin_extend_code
    (walkMem (pc 13) 13 (.MV .x18 .x13)
      (by decide) (by unfold pc walkB; decide) rfl) h2
  rw [pc_succ 13] at h2c
  have h2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
     (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ witBase) ** (.x12 ↦ᵣ witLen) **
     (.x14 ↦ᵣ pathLen) ** (.x15 ↦ᵣ valOut) ** (.x16 ↦ᵣ valOutLen) ** F)
    (by pcf; exact hF) h2c
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2F
  have h3 := mv_spec_gen_within .x19 .x14 pathLen v19 (pc 14) (by decide)
  have h3c := cpsTripleWithin_extend_code
    (walkMem (pc 14) 14 (.MV .x19 .x14)
      (by decide) (by unfold pc walkB; decide) rfl) h3
  rw [pc_succ 14] at h3c
  have h3F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** (.x18 ↦ᵣ pathPtr) ** (.x20 ↦ᵣ v20) **
     (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ witBase) ** (.x12 ↦ᵣ witLen) **
     (.x13 ↦ᵣ pathPtr) ** (.x15 ↦ᵣ valOut) ** (.x16 ↦ᵣ valOutLen) ** F)
    (by pcf; exact hF) h3c
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3F
  have h4 := mv_spec_gen_within .x20 .x15 valOut v20 (pc 15) (by decide)
  have h4c := cpsTripleWithin_extend_code
    (walkMem (pc 15) 15 (.MV .x20 .x15)
      (by decide) (by unfold pc walkB; decide) rfl) h4
  rw [pc_succ 15] at h4c
  have h4F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** (.x18 ↦ᵣ pathPtr) **
     (.x19 ↦ᵣ pathLen) ** (.x21 ↦ᵣ v21) **
     (.x11 ↦ᵣ witBase) ** (.x12 ↦ᵣ witLen) **
     (.x13 ↦ᵣ pathPtr) ** (.x14 ↦ᵣ pathLen) ** (.x16 ↦ᵣ valOutLen) ** F)
    (by pcf; exact hF) h4c
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 h4F
  have h5 := mv_spec_gen_within .x21 .x16 valOutLen v21 (pc 16) (by decide)
  have h5c := cpsTripleWithin_extend_code
    (walkMem (pc 16) 16 (.MV .x21 .x16)
      (by decide) (by unfold pc walkB; decide) rfl) h5
  rw [pc_succ 16] at h5c
  have h5F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** (.x18 ↦ᵣ pathPtr) **
     (.x19 ↦ᵣ pathLen) ** (.x20 ↦ᵣ valOut) **
     (.x11 ↦ᵣ witBase) ** (.x12 ↦ᵣ witLen) **
     (.x13 ↦ᵣ pathPtr) ** (.x14 ↦ᵣ pathLen) ** (.x15 ↦ᵣ valOut) ** F)
    (by pcf; exact hF) h5c
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01234 h5F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- la mw_lookup_hash into x5 (pc17→pc19). -/
theorem setup_la_hash_dst
    (v5 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 17) (pc 19) fullCode
      ((.x5 ↦ᵣ v5) ** F)
      ((.x5 ↦ᵣ MwLookupHash) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 17) MwLookupHash
    (by decide) la_setup_hash_range
    (walkMem (pc 17) 17
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 17) MwLookupHash))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_setup_hash_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 18)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 17) MwLookupHash)) a = some i := by
        simpa [pc_succ 17] using hs
      exact walkMem (pc 18) 18
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 17) MwLookupHash))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_setup_hash_lo]; rfl) a i hs')
  rw [pc_add8_su 17] at hla
  exact cpsTripleWithin_frameR F hF hla

/-! One dword LD root+off / SD lookup+off (specialized PCs). -/
theorem setup_hash_dword0
    (rootPtr dword oldDst v6 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 19) (pc 21) fullCode
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ v6) **
       (rootPtr ↦ₘ dword) ** (MwLookupHash ↦ₘ oldDst) ** F)
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ dword) **
       (rootPtr ↦ₘ dword) ** (MwLookupHash ↦ₘ dword) ** F) := by
  have hld0 := ld_spec_gen_within .x6 .x10 rootPtr v6 dword
    (0 : BitVec 12) (pc 19) (by decide)
  rw [signExtend12_0s, show (rootPtr + 0 : Word) = rootPtr from by bv_omega,
      pc_succ 19] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 19) 19 (.LD .x6 .x10 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwLookupHash) ** (MwLookupHash ↦ₘ oldDst) ** F)
    (by pcf; exact hF) hld
  have hsd0 := sd_spec_gen_within .x5 .x6 MwLookupHash dword oldDst
    (0 : BitVec 12) (pc 20)
  rw [signExtend12_0s, show (MwLookupHash + 0 : Word) = MwLookupHash from by bv_omega,
      pc_succ 20] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 20) 20 (.SD .x5 .x6 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ rootPtr) ** (rootPtr ↦ₘ dword) ** F)
    (by pcf; exact hF) hsd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hldF hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

theorem setup_hash_dword1
    (rootPtr dword oldDst v6 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 21) (pc 23) fullCode
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ v6) **
       ((rootPtr + 8) ↦ₘ dword) ** ((MwLookupHash + 8) ↦ₘ oldDst) ** F)
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ dword) **
       ((rootPtr + 8) ↦ₘ dword) ** ((MwLookupHash + 8) ↦ₘ dword) ** F) := by
  have hld0 := ld_spec_gen_within .x6 .x10 rootPtr v6 dword
    (8 : BitVec 12) (pc 21) (by decide)
  rw [signExtend12_8s, pc_succ 21] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 21) 21 (.LD .x6 .x10 (8 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwLookupHash) ** ((MwLookupHash + 8) ↦ₘ oldDst) ** F)
    (by pcf; exact hF) hld
  have hsd0 := sd_spec_gen_within .x5 .x6 MwLookupHash dword oldDst
    (8 : BitVec 12) (pc 22)
  rw [signExtend12_8s, pc_succ 22] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 22) 22 (.SD .x5 .x6 (8 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ rootPtr) ** ((rootPtr + 8) ↦ₘ dword) ** F)
    (by pcf; exact hF) hsd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hldF hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

theorem setup_hash_dword2
    (rootPtr dword oldDst v6 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 23) (pc 25) fullCode
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ v6) **
       ((rootPtr + 16) ↦ₘ dword) ** ((MwLookupHash + 16) ↦ₘ oldDst) ** F)
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ dword) **
       ((rootPtr + 16) ↦ₘ dword) ** ((MwLookupHash + 16) ↦ₘ dword) ** F) := by
  have hld0 := ld_spec_gen_within .x6 .x10 rootPtr v6 dword
    (16 : BitVec 12) (pc 23) (by decide)
  rw [signExtend12_16s, pc_succ 23] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 23) 23 (.LD .x6 .x10 (16 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwLookupHash) ** ((MwLookupHash + 16) ↦ₘ oldDst) ** F)
    (by pcf; exact hF) hld
  have hsd0 := sd_spec_gen_within .x5 .x6 MwLookupHash dword oldDst
    (16 : BitVec 12) (pc 24)
  rw [signExtend12_16s, pc_succ 24] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 24) 24 (.SD .x5 .x6 (16 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ rootPtr) ** ((rootPtr + 16) ↦ₘ dword) ** F)
    (by pcf; exact hF) hsd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hldF hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

theorem setup_hash_dword3
    (rootPtr dword oldDst v6 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 25) (pc 27) fullCode
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ v6) **
       ((rootPtr + 24) ↦ₘ dword) ** ((MwLookupHash + 24) ↦ₘ oldDst) ** F)
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ dword) **
       ((rootPtr + 24) ↦ₘ dword) ** ((MwLookupHash + 24) ↦ₘ dword) ** F) := by
  have hld0 := ld_spec_gen_within .x6 .x10 rootPtr v6 dword
    (24 : BitVec 12) (pc 25) (by decide)
  rw [signExtend12_24s, pc_succ 25] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 25) 25 (.LD .x6 .x10 (24 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwLookupHash) ** ((MwLookupHash + 24) ↦ₘ oldDst) ** F)
    (by pcf; exact hF) hld
  have hsd0 := sd_spec_gen_within .x5 .x6 MwLookupHash dword oldDst
    (24 : BitVec 12) (pc 26)
  rw [signExtend12_24s, pc_succ 26] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 26) 26 (.SD .x5 .x6 (24 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ rootPtr) ** ((rootPtr + 24) ↦ₘ dword) ** F)
    (by pcf; exact hF) hsd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hldF hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- Copy 32B root hash (pc19→pc27). -/
theorem setup_hash_copy32
    (rootPtr d0 d1 d2 d3 o0 o1 o2 o3 v6 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 19) (pc 27) fullCode
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ v6) **
       (rootPtr ↦ₘ d0) ** ((rootPtr + 8) ↦ₘ d1) **
       ((rootPtr + 16) ↦ₘ d2) ** ((rootPtr + 24) ↦ₘ d3) **
       (MwLookupHash ↦ₘ o0) ** ((MwLookupHash + 8) ↦ₘ o1) **
       ((MwLookupHash + 16) ↦ₘ o2) ** ((MwLookupHash + 24) ↦ₘ o3) ** F)
      ((.x10 ↦ᵣ rootPtr) ** (.x5 ↦ᵣ MwLookupHash) ** (.x6 ↦ᵣ d3) **
       (rootPtr ↦ₘ d0) ** ((rootPtr + 8) ↦ₘ d1) **
       ((rootPtr + 16) ↦ₘ d2) ** ((rootPtr + 24) ↦ₘ d3) **
       (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 8) ↦ₘ d1) **
       ((MwLookupHash + 16) ↦ₘ d2) ** ((MwLookupHash + 24) ↦ₘ d3) ** F) := by
  have h0 := setup_hash_dword0 rootPtr d0 o0 v6
    (((rootPtr + 8) ↦ₘ d1) ** ((rootPtr + 16) ↦ₘ d2) ** ((rootPtr + 24) ↦ₘ d3) **
     ((MwLookupHash + 8) ↦ₘ o1) ** ((MwLookupHash + 16) ↦ₘ o2) **
     ((MwLookupHash + 24) ↦ₘ o3) ** F)
    (by pcf; exact hF)
  have h1 := setup_hash_dword1 rootPtr d1 o1 d0
    ((rootPtr ↦ₘ d0) ** ((rootPtr + 16) ↦ₘ d2) ** ((rootPtr + 24) ↦ₘ d3) **
     (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 16) ↦ₘ o2) **
     ((MwLookupHash + 24) ↦ₘ o3) ** F)
    (by pcf; exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0 h1
  have h2 := setup_hash_dword2 rootPtr d2 o2 d1
    ((rootPtr ↦ₘ d0) ** ((rootPtr + 8) ↦ₘ d1) ** ((rootPtr + 24) ↦ₘ d3) **
     (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 8) ↦ₘ d1) **
     ((MwLookupHash + 24) ↦ₘ o3) ** F)
    (by pcf; exact hF)
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2
  have h3 := setup_hash_dword3 rootPtr d3 o3 d2
    ((rootPtr ↦ₘ d0) ** ((rootPtr + 8) ↦ₘ d1) ** ((rootPtr + 16) ↦ₘ d2) **
     (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 8) ↦ₘ d1) **
     ((MwLookupHash + 16) ↦ₘ d2) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- wl ABI materialize a0..a4 (pc27→pc35). -/
theorem setup_wl_abi
    (v10 v11 v12 v13 v14 witBase witLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 27) (pc 35) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** F)
      ((.x10 ↦ᵣ witBase) ** (.x11 ↦ᵣ witLen) ** (.x12 ↦ᵣ MwLookupHash) **
       (.x13 ↦ᵣ MwLookupOff) ** (.x14 ↦ᵣ MwLookupLen) **
       (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** F) := by
  have h0 := mv_spec_gen_within .x10 .x8 witBase v10 (pc 27) (by decide)
  have h0c := cpsTripleWithin_extend_code
    (walkMem (pc 27) 27 (.MV .x10 .x8)
      (by decide) (by unfold pc walkB; decide) rfl) h0
  rw [pc_succ 27] at h0c
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x9 ↦ᵣ witLen) ** F)
    (by pcf; exact hF) h0c
  have h1 := mv_spec_gen_within .x11 .x9 witLen v11 (pc 28) (by decide)
  have h1c := cpsTripleWithin_extend_code
    (walkMem (pc 28) 28 (.MV .x11 .x9)
      (by decide) (by unfold pc walkB; decide) rfl) h1
  rw [pc_succ 28] at h1c
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ witBase) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x8 ↦ᵣ witBase) ** F)
    (by pcf; exact hF) h1c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0F h1F
  have h2 := la_materialize_within (cr := fullCode) .x12 v12 (pc 29) MwLookupHash
    (by decide) la_setup_wl_hash_range
    (walkMem (pc 29) 29
      (.AUIPC .x12 (EvmAsm.Rv64.laHi (pc 29) MwLookupHash))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_setup_wl_hash_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 30)
          (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (pc 29) MwLookupHash)) a = some i := by
        simpa [pc_succ 29] using hs
      exact walkMem (pc 30) 30
        (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (pc 29) MwLookupHash))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_setup_wl_hash_lo]; rfl) a i hs')
  rw [pc_add8_su 29] at h2
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ witBase) ** (.x11 ↦ᵣ witLen) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** F)
    (by pcf; exact hF) h2
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2F
  have h3 := la_materialize_within (cr := fullCode) .x13 v13 (pc 31) MwLookupOff
    (by decide) la_setup_wl_off_range
    (walkMem (pc 31) 31
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 31) MwLookupOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_setup_wl_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 32)
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 31) MwLookupOff)) a = some i := by
        simpa [pc_succ 31] using hs
      exact walkMem (pc 32) 32
        (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 31) MwLookupOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_setup_wl_off_lo]; rfl) a i hs')
  rw [pc_add8_su 31] at h3
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ witBase) ** (.x11 ↦ᵣ witLen) ** (.x12 ↦ᵣ MwLookupHash) **
     (.x14 ↦ᵣ v14) ** (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** F)
    (by pcf; exact hF) h3
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3F
  have h4 := la_materialize_within (cr := fullCode) .x14 v14 (pc 33) MwLookupLen
    (by decide) la_setup_wl_len_range
    (walkMem (pc 33) 33
      (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 33) MwLookupLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_setup_wl_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 34)
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 33) MwLookupLen)) a = some i := by
        simpa [pc_succ 33] using hs
      exact walkMem (pc 34) 34
        (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 33) MwLookupLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_setup_wl_len_lo]; rfl) a i hs')
  rw [pc_add8_su 33] at h4
  have h4F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ witBase) ** (.x11 ↦ᵣ witLen) ** (.x12 ↦ᵣ MwLookupHash) **
     (.x13 ↦ᵣ MwLookupOff) ** (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) ** F)
    (by pcf; exact hF) h4
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 h4F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
