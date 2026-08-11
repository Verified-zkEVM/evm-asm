/-
  Branch hash-hop prep (#11799): pc79→pc95, stops BEFORE
  `witness_lookup_by_hash` (SEPARATE residual — pure only).

  Geometry (idx):
  79-80 la x5,mw_child_offset; 81 ld x6,0(x5); 82 add x7,x23,x6
  83-84 la x28,mw_lookup_hash
  85-94 4× (ld x29,off(x7); sd x28,x29,off) off=0,8,16,24
  95+ ABI setup + JAL witness_lookup — NOT PROVED HERE
-/

import EvmAsm.Codegen.Programs.MptWalkBranchChild
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private theorem la_hash_off_hi :
    laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 316) =
      EvmAsm.Rv64.laHi (pc 79) MwChildOff := by
  unfold pc walkB MwChildOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_hash_off_lo :
    laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 316) =
      EvmAsm.Rv64.laLo (pc 79) MwChildOff := by
  unfold pc walkB MwChildOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_hash_off_range : laInRange (pc 79) MwChildOff := by
  unfold pc walkB MwChildOff laInRange; decide

private theorem la_lookup_hash_hi :
    laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 332) =
      EvmAsm.Rv64.laHi (pc 83) MwLookupHash := by
  unfold pc walkB MwLookupHash EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_lookup_hash_lo :
    laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 332) =
      EvmAsm.Rv64.laLo (pc 83) MwLookupHash := by
  unfold pc walkB MwLookupHash EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_lookup_hash_range : laInRange (pc 83) MwLookupHash := by
  unfold pc walkB MwLookupHash laInRange; decide

private theorem signExtend12_0' : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem signExtend12_8' : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem signExtend12_16' : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem signExtend12_24' : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide

private theorem pc_add8 (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

/-! Load child offset and form hash pointer x7 = node + off (pc79→pc83). -/
theorem branch_hash_ptr
    (v5 v6 v7 nodeBase childOff : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 79) (pc 83) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x23 ↦ᵣ nodeBase) ** (MwChildOff ↦ₘ childOff) ** F)
      ((.x5 ↦ᵣ MwChildOff) ** (.x6 ↦ᵣ childOff) **
       (.x7 ↦ᵣ (nodeBase + childOff)) **
       (.x23 ↦ᵣ nodeBase) ** (MwChildOff ↦ₘ childOff) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 79) MwChildOff
    (by decide) la_hash_off_range
    (walkMem (pc 79) 79
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 79) MwChildOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_hash_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 80)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 79) MwChildOff)) a = some i := by
        simpa [pc_succ 79] using hs
      exact walkMem (pc 80) 80
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 79) MwChildOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_hash_off_lo]; rfl) a i hs')
  rw [pc_add8 79] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x23 ↦ᵣ nodeBase) **
     (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF) hla
  -- LD focus rs1+rd+mem
  have hld0 := ld_spec_gen_within .x6 .x5 MwChildOff v6 childOff
    (0 : BitVec 12) (pc 81) (by decide)
  rw [signExtend12_0', show (MwChildOff + 0 : Word) = MwChildOff from by bv_omega,
      pc_succ 81] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 81) 81 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (.x23 ↦ᵣ nodeBase) ** F) (by pcf; exact hF) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  -- ADD x7 = x23 + x6; focus rs1+rs2+rd
  have hadd0 := add_spec_gen_within .x7 .x23 .x6 nodeBase childOff v7
    (pc 82) (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 82) 82 (.ADD .x7 .x23 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 82] at hadd
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwChildOff) ** (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF) hadd
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 haddF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c012

/-! la x28, mw_lookup_hash (pc83→pc85). -/
theorem branch_hash_la_dst
    (v28 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 83) (pc 85) fullCode
      ((.x28 ↦ᵣ v28) ** F)
      ((.x28 ↦ᵣ MwLookupHash) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x28 v28 (pc 83) MwLookupHash
    (by decide) la_lookup_hash_range
    (walkMem (pc 83) 83
      (.AUIPC .x28 (EvmAsm.Rv64.laHi (pc 83) MwLookupHash))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_lookup_hash_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 84)
          (.ADDI .x28 .x28 (EvmAsm.Rv64.laLo (pc 83) MwLookupHash)) a = some i := by
        simpa [pc_succ 83] using hs
      exact walkMem (pc 84) 84
        (.ADDI .x28 .x28 (EvmAsm.Rv64.laLo (pc 83) MwLookupHash))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_lookup_hash_lo]; rfl) a i hs')
  rw [pc_add8 83] at hla
  have hlaF := cpsTripleWithin_frameR F hF hla
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hlaF

/-! One dword: LD hashPtr+off → SD lookup+off. -/
theorem branch_hash_dword0
    (hashPtr dword oldDst v29 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 85) (pc 87) fullCode
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ v29) **
       (hashPtr ↦ₘ dword) ** (MwLookupHash ↦ₘ oldDst) ** F)
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ dword) **
       (hashPtr ↦ₘ dword) ** (MwLookupHash ↦ₘ dword) ** F) := by
  have hld0 := ld_spec_gen_within .x29 .x7 hashPtr v29 dword
    (0 : BitVec 12) (pc 85) (by decide)
  rw [signExtend12_0', show (hashPtr + 0 : Word) = hashPtr from by bv_omega,
      pc_succ 85] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 85) 85 (.LD .x29 .x7 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ MwLookupHash) ** (MwLookupHash ↦ₘ oldDst) ** F)
    (by pcf; exact hF) hld
  have hsd0 := sd_spec_gen_within .x28 .x29 MwLookupHash dword oldDst
    (0 : BitVec 12) (pc 86)
  rw [signExtend12_0', show (MwLookupHash + 0 : Word) = MwLookupHash from by bv_omega,
      pc_succ 86] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 86) 86 (.SD .x28 .x29 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ hashPtr) ** (hashPtr ↦ₘ dword) ** F)
    (by pcf; exact hF) hsd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hldF hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

theorem branch_hash_dword1
    (hashPtr dword oldDst v29 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 87) (pc 89) fullCode
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ v29) **
       ((hashPtr + 8) ↦ₘ dword) ** ((MwLookupHash + 8) ↦ₘ oldDst) ** F)
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ dword) **
       ((hashPtr + 8) ↦ₘ dword) ** ((MwLookupHash + 8) ↦ₘ dword) ** F) := by
  have hld0 := ld_spec_gen_within .x29 .x7 hashPtr v29 dword
    (8 : BitVec 12) (pc 87) (by decide)
  rw [signExtend12_8', pc_succ 87] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 87) 87 (.LD .x29 .x7 (8 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ MwLookupHash) ** ((MwLookupHash + 8) ↦ₘ oldDst) ** F)
    (by pcf; exact hF) hld
  have hsd0 := sd_spec_gen_within .x28 .x29 MwLookupHash dword oldDst
    (8 : BitVec 12) (pc 88)
  rw [signExtend12_8', pc_succ 88] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 88) 88 (.SD .x28 .x29 (8 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ hashPtr) ** ((hashPtr + 8) ↦ₘ dword) ** F)
    (by pcf; exact hF) hsd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hldF hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

theorem branch_hash_dword2
    (hashPtr dword oldDst v29 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 89) (pc 91) fullCode
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ v29) **
       ((hashPtr + 16) ↦ₘ dword) ** ((MwLookupHash + 16) ↦ₘ oldDst) ** F)
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ dword) **
       ((hashPtr + 16) ↦ₘ dword) ** ((MwLookupHash + 16) ↦ₘ dword) ** F) := by
  have hld0 := ld_spec_gen_within .x29 .x7 hashPtr v29 dword
    (16 : BitVec 12) (pc 89) (by decide)
  rw [signExtend12_16', pc_succ 89] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 89) 89 (.LD .x29 .x7 (16 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ MwLookupHash) ** ((MwLookupHash + 16) ↦ₘ oldDst) ** F)
    (by pcf; exact hF) hld
  have hsd0 := sd_spec_gen_within .x28 .x29 MwLookupHash dword oldDst
    (16 : BitVec 12) (pc 90)
  rw [signExtend12_16', pc_succ 90] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 90) 90 (.SD .x28 .x29 (16 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ hashPtr) ** ((hashPtr + 16) ↦ₘ dword) ** F)
    (by pcf; exact hF) hsd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hldF hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

theorem branch_hash_dword3
    (hashPtr dword oldDst v29 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 91) (pc 93) fullCode
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ v29) **
       ((hashPtr + 24) ↦ₘ dword) ** ((MwLookupHash + 24) ↦ₘ oldDst) ** F)
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ dword) **
       ((hashPtr + 24) ↦ₘ dword) ** ((MwLookupHash + 24) ↦ₘ dword) ** F) := by
  have hld0 := ld_spec_gen_within .x29 .x7 hashPtr v29 dword
    (24 : BitVec 12) (pc 91) (by decide)
  rw [signExtend12_24', pc_succ 91] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 91) 91 (.LD .x29 .x7 (24 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ MwLookupHash) ** ((MwLookupHash + 24) ↦ₘ oldDst) ** F)
    (by pcf; exact hF) hld
  have hsd0 := sd_spec_gen_within .x28 .x29 MwLookupHash dword oldDst
    (24 : BitVec 12) (pc 92)
  rw [signExtend12_24', pc_succ 92] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 92) 92 (.SD .x28 .x29 (24 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ hashPtr) ** ((hashPtr + 24) ↦ₘ dword) ** F)
    (by pcf; exact hF) hsd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hldF hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-! 4× dword copy hash → mw_lookup_hash (pc85→pc93). Last SD at pc92. -/
theorem branch_hash_copy32
    (hashPtr d0 d1 d2 d3 o0 o1 o2 o3 v29 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 85) (pc 93) fullCode
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ v29) **
       (hashPtr ↦ₘ d0) ** ((hashPtr + 8) ↦ₘ d1) **
       ((hashPtr + 16) ↦ₘ d2) ** ((hashPtr + 24) ↦ₘ d3) **
       (MwLookupHash ↦ₘ o0) ** ((MwLookupHash + 8) ↦ₘ o1) **
       ((MwLookupHash + 16) ↦ₘ o2) ** ((MwLookupHash + 24) ↦ₘ o3) ** F)
      ((.x7 ↦ᵣ hashPtr) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ d3) **
       (hashPtr ↦ₘ d0) ** ((hashPtr + 8) ↦ₘ d1) **
       ((hashPtr + 16) ↦ₘ d2) ** ((hashPtr + 24) ↦ₘ d3) **
       (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 8) ↦ₘ d1) **
       ((MwLookupHash + 16) ↦ₘ d2) ** ((MwLookupHash + 24) ↦ₘ d3) ** F) := by
  have h0 := branch_hash_dword0 hashPtr d0 o0 v29
    (((hashPtr + 8) ↦ₘ d1) ** ((hashPtr + 16) ↦ₘ d2) ** ((hashPtr + 24) ↦ₘ d3) **
     ((MwLookupHash + 8) ↦ₘ o1) ** ((MwLookupHash + 16) ↦ₘ o2) **
     ((MwLookupHash + 24) ↦ₘ o3) ** F)
    (by pcf; exact hF)
  have h1 := branch_hash_dword1 hashPtr d1 o1 d0
    ((hashPtr ↦ₘ d0) ** ((hashPtr + 16) ↦ₘ d2) ** ((hashPtr + 24) ↦ₘ d3) **
     (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 16) ↦ₘ o2) **
     ((MwLookupHash + 24) ↦ₘ o3) ** F)
    (by pcf; exact hF)
  have h2 := branch_hash_dword2 hashPtr d2 o2 d1
    ((hashPtr ↦ₘ d0) ** ((hashPtr + 8) ↦ₘ d1) ** ((hashPtr + 24) ↦ₘ d3) **
     (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 8) ↦ₘ d1) **
     ((MwLookupHash + 24) ↦ₘ o3) ** F)
    (by pcf; exact hF)
  have h3 := branch_hash_dword3 hashPtr d3 o3 d2
    ((hashPtr ↦ₘ d0) ** ((hashPtr + 8) ↦ₘ d1) ** ((hashPtr + 16) ↦ₘ d2) **
     (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 8) ↦ₘ d1) **
     ((MwLookupHash + 16) ↦ₘ d2) ** F)
    (by pcf; exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0 h1
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c0123

private theorem la_wl_hash_hi :
    laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 380) =
      EvmAsm.Rv64.laHi (pc 95) MwLookupHash := by
  unfold pc walkB MwLookupHash EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_wl_hash_lo :
    laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 380) =
      EvmAsm.Rv64.laLo (pc 95) MwLookupHash := by
  unfold pc walkB MwLookupHash EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_wl_hash_range : laInRange (pc 95) MwLookupHash := by
  unfold pc walkB MwLookupHash laInRange; decide

private theorem la_wl_off_hi :
    laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 388) =
      EvmAsm.Rv64.laHi (pc 97) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_wl_off_lo :
    laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 388) =
      EvmAsm.Rv64.laLo (pc 97) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_wl_off_range : laInRange (pc 97) MwLookupOff := by
  unfold pc walkB MwLookupOff laInRange; decide

private theorem la_wl_len_hi :
    laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 396) =
      EvmAsm.Rv64.laHi (pc 99) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_wl_len_lo :
    laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 396) =
      EvmAsm.Rv64.laLo (pc 99) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_wl_len_range : laInRange (pc 99) MwLookupLen := by
  unfold pc walkB MwLookupLen laInRange; decide

/-! Witness-lookup ABI setup only (pc93→pc101). STOPS before JAL at pc101.
    a0=s0 witness base, a1=s1 witness len, a2=lookup_hash, a3=off BSS, a4=len BSS. -/
theorem branch_hash_wl_abi
    (s0 s1 v10 v11 v12 v13 v14 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 93) (pc 101) fullCode
      ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
      ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x10 ↦ᵣ s0) ** (.x11 ↦ᵣ s1) **
       (.x12 ↦ᵣ MwLookupHash) ** (.x13 ↦ᵣ MwLookupOff) **
       (.x14 ↦ᵣ MwLookupLen) ** F) := by
  -- MV x10,x8 — focus rd+rs
  have hmv10 := mv_spec_gen_within .x10 .x8 s0 v10 (pc 93) (by decide)
  have hmv10c := cpsTripleWithin_extend_code
    (walkMem (pc 93) 93 (.MV .x10 .x8)
      (by decide) (by unfold pc walkB; decide) rfl) hmv10
  rw [pc_succ 93] at hmv10c
  have hmv10F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ s1) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
    (by pcf; exact hF) hmv10c
  -- MV x11,x9
  have hmv11 := mv_spec_gen_within .x11 .x9 s1 v11 (pc 94) (by decide)
  have hmv11c := cpsTripleWithin_extend_code
    (walkMem (pc 94) 94 (.MV .x11 .x9)
      (by decide) (by unfold pc walkB; decide) rfl) hmv11
  rw [pc_succ 94] at hmv11c
  have hmv11F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ s0) ** (.x10 ↦ᵣ s0) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
    (by pcf; exact hF) hmv11c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hmv10F hmv11F
  -- la x12 lookup_hash
  have hla12 := la_materialize_within (cr := fullCode) .x12 v12 (pc 95) MwLookupHash
    (by decide) la_wl_hash_range
    (walkMem (pc 95) 95
      (.AUIPC .x12 (EvmAsm.Rv64.laHi (pc 95) MwLookupHash))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_wl_hash_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 96)
          (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (pc 95) MwLookupHash)) a = some i := by
        simpa [pc_succ 95] using hs
      exact walkMem (pc 96) 96
        (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (pc 95) MwLookupHash))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_wl_hash_lo]; rfl) a i hs')
  rw [pc_add8 95] at hla12
  have hla12F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
     (.x10 ↦ᵣ s0) ** (.x11 ↦ᵣ s1) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
    (by pcf; exact hF) hla12
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hla12F
  -- la x13 lookup_offset
  have hla13 := la_materialize_within (cr := fullCode) .x13 v13 (pc 97) MwLookupOff
    (by decide) la_wl_off_range
    (walkMem (pc 97) 97
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 97) MwLookupOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_wl_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 98)
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 97) MwLookupOff)) a = some i := by
        simpa [pc_succ 97] using hs
      exact walkMem (pc 98) 98
        (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 97) MwLookupOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_wl_off_lo]; rfl) a i hs')
  rw [pc_add8 97] at hla13
  have hla13F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
     (.x10 ↦ᵣ s0) ** (.x11 ↦ᵣ s1) **
     (.x12 ↦ᵣ MwLookupHash) ** (.x14 ↦ᵣ v14) ** F)
    (by pcf; exact hF) hla13
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hla13F
  -- la x14 lookup_length
  have hla14 := la_materialize_within (cr := fullCode) .x14 v14 (pc 99) MwLookupLen
    (by decide) la_wl_len_range
    (walkMem (pc 99) 99
      (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 99) MwLookupLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_wl_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 100)
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 99) MwLookupLen)) a = some i := by
        simpa [pc_succ 99] using hs
      exact walkMem (pc 100) 100
        (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 99) MwLookupLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_wl_len_lo]; rfl) a i hs')
  rw [pc_add8 99] at hla14
  have hla14F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
     (.x10 ↦ᵣ s0) ** (.x11 ↦ᵣ s1) **
     (.x12 ↦ᵣ MwLookupHash) ** (.x13 ↦ᵣ MwLookupOff) ** F)
    (by pcf; exact hF) hla14
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 hla14F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! Full hash-hop prep pc79→pc101: form ptr, la dst, copy 32B, ABI setup.
    Fuel 4+2+8+8 = 22. STOPS before witness_lookup JAL. -/
theorem branch_hash_prep
    (v5 v6 v7 v28 v29 v10 v11 v12 v13 v14 : Word)
    (nodeBase childOff s0 s1 : Word)
    (d0 d1 d2 d3 o0 o1 o2 o3 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 22 (pc 79) (pc 101) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x23 ↦ᵣ nodeBase) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (MwChildOff ↦ₘ childOff) **
       ((nodeBase + childOff) ↦ₘ d0) **
       (((nodeBase + childOff) + 8) ↦ₘ d1) **
       (((nodeBase + childOff) + 16) ↦ₘ d2) **
       (((nodeBase + childOff) + 24) ↦ₘ d3) **
       (MwLookupHash ↦ₘ o0) ** ((MwLookupHash + 8) ↦ₘ o1) **
       ((MwLookupHash + 16) ↦ₘ o2) ** ((MwLookupHash + 24) ↦ₘ o3) ** F)
      ((.x5 ↦ᵣ MwChildOff) ** (.x6 ↦ᵣ childOff) **
       (.x7 ↦ᵣ (nodeBase + childOff)) **
       (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x10 ↦ᵣ s0) ** (.x11 ↦ᵣ s1) **
       (.x12 ↦ᵣ MwLookupHash) ** (.x13 ↦ᵣ MwLookupOff) **
       (.x14 ↦ᵣ MwLookupLen) **
       (.x23 ↦ᵣ nodeBase) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ d3) **
       (MwChildOff ↦ₘ childOff) **
       ((nodeBase + childOff) ↦ₘ d0) **
       (((nodeBase + childOff) + 8) ↦ₘ d1) **
       (((nodeBase + childOff) + 16) ↦ₘ d2) **
       (((nodeBase + childOff) + 24) ↦ₘ d3) **
       (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 8) ↦ₘ d1) **
       ((MwLookupHash + 16) ↦ₘ d2) ** ((MwLookupHash + 24) ↦ₘ d3) ** F) := by
  let hashPtr := nodeBase + childOff
  have hptr := branch_hash_ptr v5 v6 v7 nodeBase childOff
    ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (hashPtr ↦ₘ d0) ** ((hashPtr + 8) ↦ₘ d1) **
     ((hashPtr + 16) ↦ₘ d2) ** ((hashPtr + 24) ↦ₘ d3) **
     (MwLookupHash ↦ₘ o0) ** ((MwLookupHash + 8) ↦ₘ o1) **
     ((MwLookupHash + 16) ↦ₘ o2) ** ((MwLookupHash + 24) ↦ₘ o3) ** F)
    (by pcf; exact hF)
  have hla := branch_hash_la_dst v28
    ((.x5 ↦ᵣ MwChildOff) ** (.x6 ↦ᵣ childOff) ** (.x7 ↦ᵣ hashPtr) **
     (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** (.x29 ↦ᵣ v29) **
     (MwChildOff ↦ₘ childOff) **
     (hashPtr ↦ₘ d0) ** ((hashPtr + 8) ↦ₘ d1) **
     ((hashPtr + 16) ↦ₘ d2) ** ((hashPtr + 24) ↦ₘ d3) **
     (MwLookupHash ↦ₘ o0) ** ((MwLookupHash + 8) ↦ₘ o1) **
     ((MwLookupHash + 16) ↦ₘ o2) ** ((MwLookupHash + 24) ↦ₘ o3) ** F)
    (by pcf; exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hptr hla
  have hcopy := branch_hash_copy32 hashPtr d0 d1 d2 d3 o0 o1 o2 o3 v29
    ((.x5 ↦ᵣ MwChildOff) ** (.x6 ↦ᵣ childOff) **
     (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF)
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hcopy
  have habi := branch_hash_wl_abi s0 s1 v10 v11 v12 v13 v14
    ((.x5 ↦ᵣ MwChildOff) ** (.x6 ↦ᵣ childOff) ** (.x7 ↦ᵣ hashPtr) **
     (.x23 ↦ᵣ nodeBase) ** (.x28 ↦ᵣ MwLookupHash) ** (.x29 ↦ᵣ d3) **
     (MwChildOff ↦ₘ childOff) **
     (hashPtr ↦ₘ d0) ** ((hashPtr + 8) ↦ₘ d1) **
     ((hashPtr + 16) ↦ₘ d2) ** ((hashPtr + 24) ↦ₘ d3) **
     (MwLookupHash ↦ₘ d0) ** ((MwLookupHash + 8) ↦ₘ d1) **
     ((MwLookupHash + 16) ↦ₘ d2) ** ((MwLookupHash + 24) ↦ₘ d3) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 habi
  -- unfold hashPtr in goal
  change cpsTripleWithin 22 (pc 79) (pc 101) fullCode _ _
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
