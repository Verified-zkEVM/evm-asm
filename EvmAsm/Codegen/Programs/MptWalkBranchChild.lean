/-
  Branch arm post-nth child dispatch (#11799).

  After rlp_list_nth_item returns (pc 65):
    ADDI x22+1; BNE status fail;
    la+ld child_len; BEQ empty → status1;
    LI 32; BEQ hash32 → hash hop (witness_lookup residual);
    else inlined (len≠0∧≠32) EXCLUDED BY GATE.

  This file covers advance + status + empty entry + hash32 entry.
  Inlined arm is not proved (domain gate).
  Hash hop body stops before witness_lookup_by_hash (SEPARATE residual).
-/

import EvmAsm.Codegen.Programs.MptWalkBranchNth
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! ## PC targets -/

private theorem bne_nth_fail_off :
    pc 66 + signExtend13 (936 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem beq_empty_off :
    pc 70 + signExtend13 (908 : BitVec 13) = pc 297 := by
  unfold pc walkB signExtend13; decide

private theorem beq_hash_off :
    pc 72 + signExtend13 (28 : BitVec 13) = pc 79 := by
  unfold pc walkB signExtend13; decide

private theorem la_child_len_post_hi :
    laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 268) =
      EvmAsm.Rv64.laHi (pc 67) MwChildLen := by
  unfold pc walkB MwChildLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_child_len_post_lo :
    laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 268) =
      EvmAsm.Rv64.laLo (pc 67) MwChildLen := by
  unfold pc walkB MwChildLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_child_len_post_range : laInRange (pc 67) MwChildLen := by
  unfold pc walkB MwChildLen laInRange; decide

/-- Advance path position after successful nth (pc65→pc66). -/
theorem branch_path_advance
    (posW : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 65) (pc 66) fullCode
      ((.x22 ↦ᵣ posW) ** F)
      ((.x22 ↦ᵣ (posW + (1 : Word))) ** F) := by
  have h := addi_spec_gen_same_within .x22 posW (1 : BitVec 12) (pc 65) (by decide)
  have hc := cpsTripleWithin_extend_code
    (walkMem (pc 65) 65 (.ADDI .x22 .x22 (1 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) h
  rw [pc_succ 65] at hc
  exact cpsTripleWithin_frameR F hF hc

/-- Nth status ≠ 0: taken BNE to fail entry (pc300). -/
theorem branch_nth_status_fail
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 66) (pc 300) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 936
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 66)
  rw [bne_nth_fail_off, show pc 66 + 4 = pc 67 from pc_succ 66] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 66) 66 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htkF

/-- Nth status = 0: fall through. -/
theorem branch_nth_status_ok
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 66) (pc 67) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 936
  have hbne := bne_spec_gen_within .x10 .x0 off (0 : Word) (0 : Word) (pc 66)
  rw [bne_nth_fail_off, show pc 66 + 4 = pc 67 from pc_succ 66] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 66) 66 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-- Load child length into x6 (pc67→pc70): la + ld. -/
theorem branch_load_child_len
    (v5 v6 childLen : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 67) (pc 70) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (MwChildLen ↦ₘ childLen) ** F)
      ((.x5 ↦ᵣ MwChildLen) ** (.x6 ↦ᵣ childLen) **
       (MwChildLen ↦ₘ childLen) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 67) MwChildLen
    (by decide) la_child_len_post_range
    (walkMem (pc 67) 67
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 67) MwChildLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_child_len_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 68)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 67) MwChildLen)) a = some i := by
        simpa [pc_succ 67] using hs
      exact walkMem (pc 68) 68
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 67) MwChildLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_child_len_post_lo]; rfl) a i hs')
  rw [show pc 67 + 8 = pc 69 from by unfold pc; bv_omega] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (MwChildLen ↦ₘ childLen) ** F)
    (by pcf; exact hF) hla
  -- LD focus = rs1+rd+mem; frame only F
  have hld0 := ld_spec_gen_within .x6 .x5 MwChildLen v6 childLen
    (0 : BitVec 12) (pc 69) (by decide)
  rw [signExtend12_0, show (MwChildLen + 0 : Word) = MwChildLen from by bv_omega,
      pc_succ 69] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 69) 69 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- Child length = 0: taken BEQ → empty entry pc297. -/
theorem branch_child_empty
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 70) (pc 297) fullCode
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 908
  have hb := beq_spec_gen_within .x6 .x0 off (0 : Word) (0 : Word) (pc 70)
  rw [beq_empty_off, show pc 70 + 4 = pc 71 from pc_succ 70] at hb
  have hbe := cpsBranchWithin_extend_code
    (walkMem (pc 70) 70 (.BEQ .x6 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hb
  have htk := cpsBranchWithin_takenStripPure2 hbe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htkF

/-- Child length ≠ 0: fall through toward hash/inlined. -/
theorem branch_child_nempty
    (childLen : Word) (hne : childLen ≠ 0)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 70) (pc 71) fullCode
      ((.x6 ↦ᵣ childLen) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x6 ↦ᵣ childLen) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 908
  have hb := beq_spec_gen_within .x6 .x0 off childLen (0 : Word) (pc 70)
  rw [beq_empty_off, show pc 70 + 4 = pc 71 from pc_succ 70] at hb
  have hbe := cpsBranchWithin_extend_code
    (walkMem (pc 70) 70 (.BEQ .x6 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hb
  have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hne ((sepConj_pure_right _).1 hQ).2)
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-- LI x7, 32 then BEQ taken → hash32 entry pc79. -/
theorem branch_child_hash32
    (v7 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 71) (pc 79) fullCode
      ((.x6 ↦ᵣ (32 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x6 ↦ᵣ (32 : Word)) ** (.x7 ↦ᵣ (32 : Word)) **
       (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hli := li_spec_gen_within .x7 v7 (32 : Word) (pc 71) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (walkMem (pc 71) 71 (.LI .x7 (32 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) hli
  rw [pc_succ 71] at hlic
  -- LI focuses x7; frame x6+x0+F
  have hliF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (32 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hlic
  let off : BitVec 13 := 28
  have hb := beq_spec_gen_within .x6 .x7 off (32 : Word) (32 : Word) (pc 72)
  rw [beq_hash_off, show pc 72 + 4 = pc 73 from pc_succ 72] at hb
  have hbe := cpsBranchWithin_extend_code
    (walkMem (pc 72) 72 (.BEQ .x6 .x7 off)
      (by decide) (by unfold pc walkB; decide) rfl) hb
  have htk := cpsBranchWithin_takenStripPure2 hbe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  -- BEQ focuses x6+x7; frame x0+F
  have htkF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** F) (by pcf; exact hF) htk
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hliF htkF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-!
  Domain note: inlined path is the BEQ-ntaken fallthrough at pc72 when
  childLen ≠ 0 ∧ childLen ≠ 32. EXCLUDED BY GATE — not proved here.
  Hash hop body from pc79 calls witness_lookup_by_hash — SEPARATE residual.
-/

/-! After nth success (pc65): advance pos, status ok, load len=32, take hash arm → pc79.
    Fuel: 1 (ADDI) + 1 (BNE ok) + 3 (la+ld) + 1 (nempty) + 2 (hash32) = 8. -/
set_option maxRecDepth 8000 in
theorem branch_after_nth_ok_to_hash32
    (v22 v5 v6 v7 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 65) (pc 79) fullCode
      ((.x22 ↦ᵣ v22) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (MwChildLen ↦ₘ (32 : Word)) ** F)
      ((.x22 ↦ᵣ (v22 + 1)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ MwChildLen) ** (.x6 ↦ᵣ (32 : Word)) ** (.x7 ↦ᵣ (32 : Word)) **
       (MwChildLen ↦ₘ (32 : Word)) ** F) := by
  -- ADDI x22+1
  have h1 := branch_path_advance v22
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (MwChildLen ↦ₘ (32 : Word)) ** F)
    (by pcf; exact hF)
  -- BNE status ok
  have h2 := branch_nth_status_ok
    ((.x22 ↦ᵣ (v22 + 1)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (MwChildLen ↦ₘ (32 : Word)) ** F)
    (by pcf; exact hF)
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h1 h2
  -- load child len
  have h3 := branch_load_child_len v5 v6 (32 : Word)
    ((.x22 ↦ᵣ (v22 + 1)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x7 ↦ᵣ v7) ** F)
    (by pcf; exact hF)
  have c123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c12 h3
  -- nempty
  have h4 := branch_child_nempty (32 : Word) (by decide)
    ((.x22 ↦ᵣ (v22 + 1)) ** (.x10 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwChildLen) ** (.x7 ↦ᵣ v7) **
     (MwChildLen ↦ₘ (32 : Word)) ** F)
    (by pcf; exact hF)
  have c1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c123 h4
  -- hash32
  have h5 := branch_child_hash32 v7
    ((.x22 ↦ᵣ (v22 + 1)) ** (.x10 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwChildLen) ** (MwChildLen ↦ₘ (32 : Word)) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c1234 h5
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! After nth success: advance, status ok, load len=0 → empty entry pc297.
    Fuel: 1+1+3+1 = 6. -/
set_option maxRecDepth 8000 in
theorem branch_after_nth_ok_to_empty
    (v22 v5 v6 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 6 (pc 65) (pc 297) fullCode
      ((.x22 ↦ᵣ v22) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (MwChildLen ↦ₘ (0 : Word)) ** F)
      ((.x22 ↦ᵣ (v22 + 1)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ MwChildLen) ** (.x6 ↦ᵣ (0 : Word)) **
       (MwChildLen ↦ₘ (0 : Word)) ** F) := by
  have h1 := branch_path_advance v22
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
     (MwChildLen ↦ₘ (0 : Word)) ** F)
    (by pcf; exact hF)
  have h2 := branch_nth_status_ok
    ((.x22 ↦ᵣ (v22 + 1)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
     (MwChildLen ↦ₘ (0 : Word)) ** F)
    (by pcf; exact hF)
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h1 h2
  have h3 := branch_load_child_len v5 v6 (0 : Word)
    ((.x22 ↦ᵣ (v22 + 1)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF)
  have c123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c12 h3
  have h4 := branch_child_empty
    ((.x22 ↦ᵣ (v22 + 1)) ** (.x10 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwChildLen) ** (MwChildLen ↦ₘ (0 : Word)) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c123 h4
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
