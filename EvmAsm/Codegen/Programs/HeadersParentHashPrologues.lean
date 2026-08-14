/-
  EvmAsm.Codegen.Programs.HeadersParentHashPrologues

  Prologue path lemmas for the `headers_parent_hash` whole-routine
  triple (see `HeadersParentHashSpec.lean` for the routine contract):
  the two fail-fast guards (`b0 < 192`, `249 < b0`) and the short-form /
  long-form prefix prologues, each landing at instruction 15 with the
  cursor/length registers set for the checks + copy-loop phase.
-/

import EvmAsm.Codegen.Programs.HeadersParentHashSpec
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen

open EvmAsm.Rv64
-- ---------------------------------------------------------------------------
-- Prologue (instructions 0..14) path lemmas

private theorem hphSE2 : signExtend13 (brOff (GuestAddrs.headers_parent_hash + 128)
    (GuestAddrs.headers_parent_hash + 8)) = (120 : Word) := by decide
private theorem hphA2t : hphBase + 8 + (120 : Word) = hphBase + 128 := by bv_omega
private theorem hphA2f : hphBase + 8 + 4 = hphBase + 12 := by bv_omega
private theorem hphSE4 : signExtend13 (36 : BitVec 13) = (36 : Word) := by decide
private theorem hphA4t : hphBase + 16 + (36 : Word) = hphBase + 52 := by bv_omega
private theorem hphA4f : hphBase + 16 + 4 = hphBase + 20 := by bv_omega
private theorem hphSE8 : signExtend13 (brOff (GuestAddrs.headers_parent_hash + 128)
    (GuestAddrs.headers_parent_hash + 32)) = (96 : Word) := by decide
private theorem hphA8t : hphBase + 32 + (96 : Word) = hphBase + 128 := by bv_omega
private theorem hphA8f : hphBase + 32 + 4 = hphBase + 36 := by bv_omega
private theorem hphSE21_12 : signExtend21 (12 : BitVec 21) = (12 : Word) := by decide
private theorem hphA12 : hphBase + 48 + (12 : Word) = hphBase + 60 := by bv_omega
private theorem hphSE12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem hph_sub1 (w : Word) : w + signExtend12 (-1 : BitVec 12) = w - (1 : Word) := by
  rw [show signExtend12 (-1 : BitVec 12) = (0xFFFFFFFFFFFFFFFF : Word) from by decide]
  bv_omega
private theorem hph_ofNat1 : (1 : Word) = BitVec.ofNat 64 1 := by decide

/-- Low guard fails (`b0 < 192`): instructions 0, 1, 2 (taken), 32, 33 — 5 steps. -/
theorem hph_fail_low_spec_within
    (retHdr thisPtr thisLen : Word) (v5 v6 v7 v28 : Word)
    (thisBytes claimedBytes : List (BitVec 8))
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hclaimed : claimedBytes.length = 32)
    (hret : retHdr &&& ~~~(1 : Word) = retHdr)
    (h0 : 0 < thisBytes.length)
    (hb0lt : headersParentHash_b0 thisBytes < 192) :
    cpsTripleWithin 5 hphBase retHdr hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ headersParentHash_status thisBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        bytesRegion hphClaimed (headersParentHash_out thisBytes claimedBytes) **
        bytesRegion thisPtr thisBytes ** regOwn .x11 ** regOwn .x12) := by
  have _ := hsover
  have _ := hclaimed
  have hmono0 : ∀ a i, CodeReq.singleton hphBase (.LBU .x5 .x10 0) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 0
      (hphBase + 4 * 0) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono1 : ∀ a i, CodeReq.singleton (hphBase + 4) (.LI .x6 (192 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 1
      (hphBase + 4 * 1) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono2 : ∀ a i, CodeReq.singleton (hphBase + 8)
      (.BLTU .x5 .x6 (brOff (GuestAddrs.headers_parent_hash + 128)
        (GuestAddrs.headers_parent_hash + 8))) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 2
      (hphBase + 4 * 2) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono32 : ∀ a i, CodeReq.singleton (hphBase + 128) (.LI .x10 (1 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 32
      (hphBase + 4 * 32) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono33 : ∀ a i, CodeReq.singleton (hphBase + 132) (.JALR .x0 .x1 0) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 33
      (hphBase + 4 * 33) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hAddr0 : thisPtr + BitVec.ofNat 64 0 = thisPtr := by
    rw [show BitVec.ofNat 64 0 = (0 : Word) from by decide]; bv_omega
  -- instruction 0: LBU x5 ← thisBytes[0]
  have hLbu0 := bytesRegion_lbu_within .x5 .x10 thisPtr v5 hphBase thisBytes 0
    (by decide) hsalign h0 (by omega) (hsvalid 0 h0)
  rw [hAddr0] at hLbu0
  have hLbu : cpsTripleWithin 1 hphBase (hphBase + 4) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono0 (cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed)) **
          ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes)) (by pcFree) hLbu0))
  -- instruction 1: LI x6, 192
  have h192 : cpsTripleWithin 1 (hphBase + 4) (hphBase + 8) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono1
      (li_spec_gen_within .x6 v6 (192 : Word) (hphBase + 4) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 2: BLTU x5, x6 (b0 < 192?) — taken
  have hBr0 := bltu_spec_gen_within .x5 .x6
    (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 8))
    ((thisBytes[0]'h0).zeroExtend 64) (192 : Word) (hphBase + 8)
  rw [hphSE2, hphA2t, hphA2f] at hBr0
  have hult : BitVec.ult ((thisBytes[0]'h0).zeroExtend 64) (192 : Word) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show (192 : Word).toNat = 192 from by decide,
      Nat.mod_eq_of_lt (show headersParentHash_b0 thisBytes < 2 ^ 64 from
      (hphB0_lt_256 thisBytes).trans (by decide))]
    exact hb0lt
  have hTaken0 := cpsBranchWithin_takenStripPure2 hBr0 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
    exact h_pure.2 hult)
  have hTaken_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hTaken0
  have hTaken : cpsTripleWithin 1 (hphBase + 8) (hphBase + 128) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono2 hTaken_fr)
  -- the fail epilogue (instructions 32, 33)
  have hFail : cpsTripleWithin 2 (hphBase + 128) retHdr hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h1 : cpsTripleWithin 1 (hphBase + 128) (hphBase + 132) hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
          (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
          (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
      have h0l := cpsTripleWithin_extend_code hmono32
        (li_spec_gen_within .x10 thisPtr (1 : Word) (hphBase + 128) (by decide))
      have h0f := cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
          (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (192 : Word)) **
          (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hp => by xperm_hyp hp) h0f
    have hRet0 := cpsTripleWithin_extend_code hmono33
      (EvmAsm.Evm64.ret_spec_within' (hphBase + 132) retHdr)
    rw [hret] at hRet0
    have hRet : cpsTripleWithin 1 (hphBase + 132) retHdr hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
          (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
          (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
      cpsTripleWithin_frameR
        (((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
          (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ (192 : Word)) **
          (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree)
        hRet0
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1 hRet
    exact cpsTripleWithin_mono_nSteps (show 1 + 1 ≤ 2 from by omega) s1
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hLbu h192
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hTaken
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hFail
  have hok : headersParentHash_ok thisBytes = false := by
    simp only [headersParentHash_ok,
      decide_eq_false (show ¬ 192 ≤ headersParentHash_b0 thisBytes from by omega),
      Bool.false_and]
  exact cpsTripleWithin_mono_nSteps (show 1 + 1 + 1 + 2 ≤ 5 from by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
      rw [hphStatus_false hok, hphOut_false hok]
      have hq' := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
        (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
        (sepConj_mono (fun _ x => x) (fun _ x => x))))))))) h hq
      xperm_hyp hq') s3)

/-- High guard fails (`248 ≤ b0` and `249 < b0`): instructions 0..8 (branch at 8
    taken), 32, 33 — 11 steps. -/
theorem hph_fail_high_spec_within
    (retHdr thisPtr thisLen : Word) (v5 v6 v7 v28 : Word)
    (thisBytes claimedBytes : List (BitVec 8))
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hclaimed : claimedBytes.length = 32)
    (hret : retHdr &&& ~~~(1 : Word) = retHdr)
    (h0 : 0 < thisBytes.length)
    (hb0ge : 248 ≤ headersParentHash_b0 thisBytes)
    (hb0hi : 249 < headersParentHash_b0 thisBytes) :
    cpsTripleWithin 11 hphBase retHdr hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ headersParentHash_status thisBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        bytesRegion hphClaimed (headersParentHash_out thisBytes claimedBytes) **
        bytesRegion thisPtr thisBytes ** regOwn .x11 ** regOwn .x12) := by
  have hmono0 : ∀ a i, CodeReq.singleton hphBase (.LBU .x5 .x10 0) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 0
      (hphBase + 4 * 0) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono1 : ∀ a i, CodeReq.singleton (hphBase + 4) (.LI .x6 (192 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 1
      (hphBase + 4 * 1) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono2 : ∀ a i, CodeReq.singleton (hphBase + 8)
      (.BLTU .x5 .x6 (brOff (GuestAddrs.headers_parent_hash + 128)
        (GuestAddrs.headers_parent_hash + 8))) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 2
      (hphBase + 4 * 2) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono3 : ∀ a i, CodeReq.singleton (hphBase + 12) (.LI .x6 (248 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 3
      (hphBase + 4 * 3) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono4 : ∀ a i, CodeReq.singleton (hphBase + 16)
      (.BLTU .x5 .x6 (36 : BitVec 13)) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 4
      (hphBase + 4 * 4) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono5 : ∀ a i, CodeReq.singleton (hphBase + 20) (.LI .x6 (247 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 5
      (hphBase + 4 * 5) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono6 : ∀ a i, CodeReq.singleton (hphBase + 24) (.SUB .x7 .x5 .x6) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 6
      (hphBase + 4 * 6) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono7 : ∀ a i, CodeReq.singleton (hphBase + 28) (.LI .x28 (2 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 7
      (hphBase + 4 * 7) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono8 : ∀ a i, CodeReq.singleton (hphBase + 32)
      (.BLTU .x28 .x7 (brOff (GuestAddrs.headers_parent_hash + 128)
        (GuestAddrs.headers_parent_hash + 32))) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 8
      (hphBase + 4 * 8) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono32 : ∀ a i, CodeReq.singleton (hphBase + 128) (.LI .x10 (1 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 32
      (hphBase + 4 * 32) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono33 : ∀ a i, CodeReq.singleton (hphBase + 132) (.JALR .x0 .x1 0) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 33
      (hphBase + 4 * 33) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hAddr0 : thisPtr + BitVec.ofNat 64 0 = thisPtr := by
    rw [show BitVec.ofNat 64 0 = (0 : Word) from by decide]; bv_omega
  have hb0lt256 := hphB0_lt_256 thisBytes
  have _ := hsover
  have _ := hclaimed
  have _ := hb0ge
  -- instruction 0: LBU x5 ← thisBytes[0]
  have hLbu0 := bytesRegion_lbu_within .x5 .x10 thisPtr v5 hphBase thisBytes 0
    (by decide) hsalign h0 (by omega) (hsvalid 0 h0)
  rw [hAddr0] at hLbu0
  have hLbu : cpsTripleWithin 1 hphBase (hphBase + 4) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono0 (cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed)) **
          ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes)) (by pcFree) hLbu0))
  -- instruction 1: LI x6, 192
  have h192 : cpsTripleWithin 1 (hphBase + 4) (hphBase + 8) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono1
      (li_spec_gen_within .x6 v6 (192 : Word) (hphBase + 4) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 2: BLTU x5, x6 (b0 < 192?) — not taken
  have hBr0 := bltu_spec_gen_within .x5 .x6
    (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 8))
    ((thisBytes[0]'h0).zeroExtend 64) (192 : Word) (hphBase + 8)
  rw [hphSE2, hphA2t, hphA2f] at hBr0
  have hnotult2 : ¬ BitVec.ult ((thisBytes[0]'h0).zeroExtend 64) (192 : Word) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show (192 : Word).toNat = 192 from by decide,
      Nat.mod_eq_of_lt (show headersParentHash_b0 thisBytes < 2 ^ 64 from hb0lt256.trans (by decide))]
    omega
  have hNt20 := cpsBranchWithin_ntakenStripPure2 hBr0 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
    exact hnotult2 h_pure.2)
  have hNt2_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hNt20
  have hNt2 : cpsTripleWithin 1 (hphBase + 8) (hphBase + 12) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono2 hNt2_fr)
  -- instruction 3: LI x6, 248
  have h248 : cpsTripleWithin 1 (hphBase + 12) (hphBase + 16) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono3
      (li_spec_gen_within .x6 (192 : Word) (248 : Word) (hphBase + 12) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 4: BLTU x5, x6 (b0 < 248?) — not taken
  have hBr4 := bltu_spec_gen_within .x5 .x6 (36 : BitVec 13)
    ((thisBytes[0]'h0).zeroExtend 64) (248 : Word) (hphBase + 16)
  rw [hphSE4, hphA4t, hphA4f] at hBr4
  have hnotult4 : ¬ BitVec.ult ((thisBytes[0]'h0).zeroExtend 64) (248 : Word) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show (248 : Word).toNat = 248 from by decide,
      Nat.mod_eq_of_lt (show headersParentHash_b0 thisBytes < 2 ^ 64 from hb0lt256.trans (by decide))]
    omega
  have hNt40 := cpsBranchWithin_ntakenStripPure2 hBr4 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
    exact hnotult4 h_pure.2)
  have hNt4_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hNt40
  have hNt4 : cpsTripleWithin 1 (hphBase + 16) (hphBase + 20) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono4 hNt4_fr)
  -- instruction 5: LI x6, 247
  have h247 : cpsTripleWithin 1 (hphBase + 20) (hphBase + 24) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono5
      (li_spec_gen_within .x6 (248 : Word) (247 : Word) (hphBase + 20) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 6: SUB x7, x5, x6 (lol = b0 - 247)
  have hSub : cpsTripleWithin 1 (hphBase + 24) (hphBase + 28) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono6
      (sub_spec_gen_within .x7 .x5 .x6 ((thisBytes[0]'h0).zeroExtend 64) (247 : Word) v7
        (hphBase + 24) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed)) **
        ((.x28 ↦ᵣ v28) ** bytesRegion hphClaimed claimedBytes **
          bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 7: LI x28, 2
  have h2li : cpsTripleWithin 1 (hphBase + 28) (hphBase + 32) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono7
      (li_spec_gen_within .x28 v28 (2 : Word) (hphBase + 28) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 8: BLTU x28, x7 (2 < b0 - 247?) — taken (249 < b0)
  have hBr8 := bltu_spec_gen_within .x28 .x7
    (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 32))
    (2 : Word) ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word)) (hphBase + 32)
  rw [hphSE8, hphA8t, hphA8f] at hBr8
  have hult8 : BitVec.ult (2 : Word) ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word)) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, show (2 : Word).toNat = 2 from by decide]
    bv_omega
  have hTaken80 := cpsBranchWithin_takenStripPure2 hBr8 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
    exact h_pure.2 hult8)
  have hTaken8_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ (247 : Word))) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree)
    hTaken80
  have hTaken8 : cpsTripleWithin 1 (hphBase + 32) (hphBase + 128) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono8 hTaken8_fr)
  -- the fail epilogue (instructions 32, 33)
  have hFail : cpsTripleWithin 2 (hphBase + 128) retHdr hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h1 : cpsTripleWithin 1 (hphBase + 128) (hphBase + 132) hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
          (.x6 ↦ᵣ (247 : Word)) **
          (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
          (.x6 ↦ᵣ (247 : Word)) **
          (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
      have h0l := cpsTripleWithin_extend_code hmono32
        (li_spec_gen_within .x10 thisPtr (1 : Word) (hphBase + 128) (by decide))
      have h0f := cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
          (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (247 : Word)) **
          (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hp => by xperm_hyp hp) h0f
    have hRet0 := cpsTripleWithin_extend_code hmono33
      (EvmAsm.Evm64.ret_spec_within' (hphBase + 132) retHdr)
    rw [hret] at hRet0
    have hRet : cpsTripleWithin 1 (hphBase + 132) retHdr hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
          (.x6 ↦ᵣ (247 : Word)) **
          (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
          (.x6 ↦ᵣ (247 : Word)) **
          (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
      cpsTripleWithin_frameR
        (((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
          (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ (247 : Word)) **
          (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree)
        hRet0
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1 hRet
    exact cpsTripleWithin_mono_nSteps (show 1 + 1 ≤ 2 from by omega) s1
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hLbu h192
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hNt2
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 h248
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hNt4
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 h247
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hSub
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 h2li
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hTaken8
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s8 hFail
  have hok : headersParentHash_ok thisBytes = false := by
    simp only [headersParentHash_ok,
      decide_eq_false (show ¬ headersParentHash_b0 thisBytes ≤ 249 from by omega),
      Bool.and_false, Bool.false_and]
  exact cpsTripleWithin_mono_nSteps
    (show 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 2 ≤ 11 from by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
      rw [hphStatus_false hok, hphOut_false hok]
      have hq' := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
        (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
        (sepConj_mono (fun _ x => x) (fun _ x => x))))))))) h hq
      xperm_hyp hq') s9)

/-- Short-form prologue (`192 ≤ b0 < 248`): instructions 0, 1, 2 (nt), 3, 4
    (taken), 13, 14 — 7 steps, landing at instruction 15 with `skip = 1`. -/
theorem hph_prologue_short_spec_within
    (retHdr thisPtr thisLen : Word) (v5 v6 v7 v28 : Word)
    (thisBytes claimedBytes : List (BitVec 8))
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (h0 : 0 < thisBytes.length)
    (hb0lo : 192 ≤ headersParentHash_b0 thisBytes)
    (hb0lt248 : headersParentHash_b0 thisBytes < 248) :
    cpsTripleWithin 7 hphBase (hphBase + 60) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 1)) **
        (.x11 ↦ᵣ (thisLen - (1 : Word))) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
  have hmono0 : ∀ a i, CodeReq.singleton hphBase (.LBU .x5 .x10 0) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 0
      (hphBase + 4 * 0) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono1 : ∀ a i, CodeReq.singleton (hphBase + 4) (.LI .x6 (192 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 1
      (hphBase + 4 * 1) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono2 : ∀ a i, CodeReq.singleton (hphBase + 8)
      (.BLTU .x5 .x6 (brOff (GuestAddrs.headers_parent_hash + 128)
        (GuestAddrs.headers_parent_hash + 8))) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 2
      (hphBase + 4 * 2) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono3 : ∀ a i, CodeReq.singleton (hphBase + 12) (.LI .x6 (248 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 3
      (hphBase + 4 * 3) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono4 : ∀ a i, CodeReq.singleton (hphBase + 16)
      (.BLTU .x5 .x6 (36 : BitVec 13)) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 4
      (hphBase + 4 * 4) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono13 : ∀ a i, CodeReq.singleton (hphBase + 52) (.ADDI .x10 .x10 (1 : BitVec 12))
      a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 13
      (hphBase + 4 * 13) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono14 : ∀ a i, CodeReq.singleton (hphBase + 56) (.ADDI .x11 .x11 (-1 : BitVec 12))
      a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 14
      (hphBase + 4 * 14) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hAddr0 : thisPtr + BitVec.ofNat 64 0 = thisPtr := by
    rw [show BitVec.ofNat 64 0 = (0 : Word) from by decide]; bv_omega
  have _ := hsover
  -- instruction 0: LBU x5 ← thisBytes[0]
  have hLbu0 := bytesRegion_lbu_within .x5 .x10 thisPtr v5 hphBase thisBytes 0
    (by decide) hsalign h0 (by omega) (hsvalid 0 h0)
  rw [hAddr0] at hLbu0
  have hLbu : cpsTripleWithin 1 hphBase (hphBase + 4) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono0 (cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed)) **
          ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes)) (by pcFree) hLbu0))
  -- instruction 1: LI x6, 192
  have h192 : cpsTripleWithin 1 (hphBase + 4) (hphBase + 8) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono1
      (li_spec_gen_within .x6 v6 (192 : Word) (hphBase + 4) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 2: BLTU x5, x6 (b0 < 192?) — not taken
  have hBr0 := bltu_spec_gen_within .x5 .x6
    (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 8))
    ((thisBytes[0]'h0).zeroExtend 64) (192 : Word) (hphBase + 8)
  rw [hphSE2, hphA2t, hphA2f] at hBr0
  have hnotult2 : ¬ BitVec.ult ((thisBytes[0]'h0).zeroExtend 64) (192 : Word) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show (192 : Word).toNat = 192 from by decide,
      Nat.mod_eq_of_lt (show headersParentHash_b0 thisBytes < 2 ^ 64 from
      (hphB0_lt_256 thisBytes).trans (by decide))]
    omega
  have hNt20 := cpsBranchWithin_ntakenStripPure2 hBr0 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
    exact hnotult2 h_pure.2)
  have hNt2_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hNt20
  have hNt2 : cpsTripleWithin 1 (hphBase + 8) (hphBase + 12) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono2 hNt2_fr)
  -- instruction 3: LI x6, 248
  have h248 : cpsTripleWithin 1 (hphBase + 12) (hphBase + 16) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono3
      (li_spec_gen_within .x6 (192 : Word) (248 : Word) (hphBase + 12) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 4: BLTU x5, x6 (b0 < 248?) — taken, to instruction 13
  have hBr4 := bltu_spec_gen_within .x5 .x6 (36 : BitVec 13)
    ((thisBytes[0]'h0).zeroExtend 64) (248 : Word) (hphBase + 16)
  rw [hphSE4, hphA4t, hphA4f] at hBr4
  have hult4 : BitVec.ult ((thisBytes[0]'h0).zeroExtend 64) (248 : Word) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show (248 : Word).toNat = 248 from by decide,
      Nat.mod_eq_of_lt (show headersParentHash_b0 thisBytes < 2 ^ 64 from
      (hphB0_lt_256 thisBytes).trans (by decide))]
    exact hb0lt248
  have hTaken40 := cpsBranchWithin_takenStripPure2 hBr4 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
    exact h_pure.2 hult4)
  have hTaken4_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree)
    hTaken40
  have hTaken4 : cpsTripleWithin 1 (hphBase + 16) (hphBase + 52) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono4 hTaken4_fr)
  -- instruction 13: ADDI x10, x10, 1
  have hAddi10 : cpsTripleWithin 1 (hphBase + 52) (hphBase + 56) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 1)) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono13
      (addi_spec_gen_same_within .x10 thisPtr (1 : BitVec 12) (hphBase + 52) (by decide))
    rw [hphSE12_1, hph_ofNat1] at h0l
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (248 : Word)) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 14: ADDI x11, x11, -1
  have hAddi11 : cpsTripleWithin 1 (hphBase + 56) (hphBase + 60) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 1)) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 1)) **
        (.x11 ↦ᵣ (thisLen - (1 : Word))) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono14
      (addi_spec_gen_same_within .x11 thisLen (-1 : BitVec 12) (hphBase + 56) (by decide))
    rw [hph_sub1] at h0l
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (248 : Word)) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hLbu h192
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hNt2
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 h248
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hTaken4
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hAddi10
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hAddi11
  exact cpsTripleWithin_mono_nSteps (show 1 + 1 + 1 + 1 + 1 + 1 + 1 ≤ 7 from by omega) s6

/-- Long-form prologue (`248 ≤ b0 ≤ 249`): instructions 0..12 (branches not
    taken, JAL at 12) — 13 steps, landing at instruction 15 with
    `skip = b0 - 246`. -/
theorem hph_prologue_long_spec_within
    (retHdr thisPtr thisLen : Word) (v5 v6 v7 v28 : Word)
    (thisBytes claimedBytes : List (BitVec 8))
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (h0 : 0 < thisBytes.length)
    (hb0ge : 248 ≤ headersParentHash_b0 thisBytes)
    (hb0le : headersParentHash_b0 thisBytes ≤ 249) :
    cpsTripleWithin 13 hphBase (hphBase + 60) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) **
        (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x11 ↦ᵣ (thisLen - BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
  have _ := hsover
  have hmono0 : ∀ a i, CodeReq.singleton hphBase (.LBU .x5 .x10 0) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 0
      (hphBase + 4 * 0) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono1 : ∀ a i, CodeReq.singleton (hphBase + 4) (.LI .x6 (192 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 1
      (hphBase + 4 * 1) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono2 : ∀ a i, CodeReq.singleton (hphBase + 8)
      (.BLTU .x5 .x6 (brOff (GuestAddrs.headers_parent_hash + 128)
        (GuestAddrs.headers_parent_hash + 8))) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 2
      (hphBase + 4 * 2) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono3 : ∀ a i, CodeReq.singleton (hphBase + 12) (.LI .x6 (248 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 3
      (hphBase + 4 * 3) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono4 : ∀ a i, CodeReq.singleton (hphBase + 16)
      (.BLTU .x5 .x6 (36 : BitVec 13)) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 4
      (hphBase + 4 * 4) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono5 : ∀ a i, CodeReq.singleton (hphBase + 20) (.LI .x6 (247 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 5
      (hphBase + 4 * 5) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono6 : ∀ a i, CodeReq.singleton (hphBase + 24) (.SUB .x7 .x5 .x6) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 6
      (hphBase + 4 * 6) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono7 : ∀ a i, CodeReq.singleton (hphBase + 28) (.LI .x28 (2 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 7
      (hphBase + 4 * 7) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono8 : ∀ a i, CodeReq.singleton (hphBase + 32)
      (.BLTU .x28 .x7 (brOff (GuestAddrs.headers_parent_hash + 128)
        (GuestAddrs.headers_parent_hash + 32))) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 8
      (hphBase + 4 * 8) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono9 : ∀ a i, CodeReq.singleton (hphBase + 36) (.ADDI .x7 .x7 (1 : BitVec 12))
      a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 9
      (hphBase + 4 * 9) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono10 : ∀ a i, CodeReq.singleton (hphBase + 40) (.ADD .x10 .x10 .x7) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 10
      (hphBase + 4 * 10) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono11 : ∀ a i, CodeReq.singleton (hphBase + 44) (.SUB .x11 .x11 .x7) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 11
      (hphBase + 4 * 11) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono12 : ∀ a i, CodeReq.singleton (hphBase + 48) (.JAL .x0 (12 : BitVec 21))
      a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 12
      (hphBase + 4 * 12) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hAddr0 : thisPtr + BitVec.ofNat 64 0 = thisPtr := by
    rw [show BitVec.ofNat 64 0 = (0 : Word) from by decide]; bv_omega
  have hb0lt256 := hphB0_lt_256 thisBytes
  -- instruction 0: LBU x5 ← thisBytes[0]
  have hLbu0 := bytesRegion_lbu_within .x5 .x10 thisPtr v5 hphBase thisBytes 0
    (by decide) hsalign h0 (by omega) (hsvalid 0 h0)
  rw [hAddr0] at hLbu0
  have hLbu : cpsTripleWithin 1 hphBase (hphBase + 4) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono0 (cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed)) **
          ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes)) (by pcFree) hLbu0))
  -- instruction 1: LI x6, 192
  have h192 : cpsTripleWithin 1 (hphBase + 4) (hphBase + 8) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono1
      (li_spec_gen_within .x6 v6 (192 : Word) (hphBase + 4) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 2: BLTU x5, x6 (b0 < 192?) — not taken
  have hBr0 := bltu_spec_gen_within .x5 .x6
    (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 8))
    ((thisBytes[0]'h0).zeroExtend 64) (192 : Word) (hphBase + 8)
  rw [hphSE2, hphA2t, hphA2f] at hBr0
  have hnotult2 : ¬ BitVec.ult ((thisBytes[0]'h0).zeroExtend 64) (192 : Word) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show (192 : Word).toNat = 192 from by decide,
      Nat.mod_eq_of_lt (show headersParentHash_b0 thisBytes < 2 ^ 64 from hb0lt256.trans (by decide))]
    omega
  have hNt20 := cpsBranchWithin_ntakenStripPure2 hBr0 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
    exact hnotult2 h_pure.2)
  have hNt2_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hNt20
  have hNt2 : cpsTripleWithin 1 (hphBase + 8) (hphBase + 12) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono2 hNt2_fr)
  -- instruction 3: LI x6, 248
  have h248 : cpsTripleWithin 1 (hphBase + 12) (hphBase + 16) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (192 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono3
      (li_spec_gen_within .x6 (192 : Word) (248 : Word) (hphBase + 12) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 4: BLTU x5, x6 (b0 < 248?) — not taken
  have hBr4 := bltu_spec_gen_within .x5 .x6 (36 : BitVec 13)
    ((thisBytes[0]'h0).zeroExtend 64) (248 : Word) (hphBase + 16)
  rw [hphSE4, hphA4t, hphA4f] at hBr4
  have hnotult4 : ¬ BitVec.ult ((thisBytes[0]'h0).zeroExtend 64) (248 : Word) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show (248 : Word).toNat = 248 from by decide,
      Nat.mod_eq_of_lt (show headersParentHash_b0 thisBytes < 2 ^ 64 from hb0lt256.trans (by decide))]
    omega
  have hNt40 := cpsBranchWithin_ntakenStripPure2 hBr4 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
    exact hnotult4 h_pure.2)
  have hNt4_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hNt40
  have hNt4 : cpsTripleWithin 1 (hphBase + 16) (hphBase + 20) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono4 hNt4_fr)
  -- instruction 5: LI x6, 247
  have h247 : cpsTripleWithin 1 (hphBase + 20) (hphBase + 24) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono5
      (li_spec_gen_within .x6 (248 : Word) (247 : Word) (hphBase + 20) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 6: SUB x7, x5, x6 (lol = b0 - 247)
  have hSub : cpsTripleWithin 1 (hphBase + 24) (hphBase + 28) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono6
      (sub_spec_gen_within .x7 .x5 .x6 ((thisBytes[0]'h0).zeroExtend 64) (247 : Word) v7
        (hphBase + 24) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed)) **
        ((.x28 ↦ᵣ v28) ** bytesRegion hphClaimed claimedBytes **
          bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 7: LI x28, 2
  have h2li : cpsTripleWithin 1 (hphBase + 28) (hphBase + 32) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono7
      (li_spec_gen_within .x28 v28 (2 : Word) (hphBase + 28) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 8: BLTU x28, x7 (2 < b0 - 247?) — not taken (b0 ≤ 249)
  have hBr8 := bltu_spec_gen_within .x28 .x7
    (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 32))
    (2 : Word) ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word)) (hphBase + 32)
  rw [hphSE8, hphA8t, hphA8f] at hBr8
  have hnotult8 : ¬ BitVec.ult (2 : Word) ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word)) := by
    rw [hphB0_word thisBytes h0]
    simp only [BitVec.ult, decide_eq_true_eq, show (2 : Word).toNat = 2 from by decide]
    bv_omega
  have hNt80 := cpsBranchWithin_ntakenStripPure2 hBr8 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
    exact hnotult8 h_pure.2)
  have hNt8_fr := cpsTripleWithin_frameR
    (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
      (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) ** (.x6 ↦ᵣ (247 : Word))) **
      (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hNt80
  have hNt8 : cpsTripleWithin 1 (hphBase + 32) (hphBase + 36) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_extend_code hmono8 hNt8_fr)
  -- instruction 9: ADDI x7, x7, 1 (skip = b0 - 246)
  have hskipW : ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word)) + (1 : Word) =
      BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246) := by
    rw [hphB0_word thisBytes h0]; bv_omega
  have hAddi7 : cpsTripleWithin 1 (hphBase + 36) (hphBase + 40) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))) ** (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono9
      (addi_spec_gen_same_within .x7 ((thisBytes[0]'h0).zeroExtend 64 - (247 : Word))
        (1 : BitVec 12) (hphBase + 36) (by decide))
    rw [hphSE12_1, hskipW] at h0l
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (247 : Word)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 10: ADD x10, x10, x7
  have hAdd10 : cpsTripleWithin 1 (hphBase + 40) (hphBase + 44) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) **
        (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono10
      (add_spec_gen_rd_eq_rs1_within .x10 .x7 thisPtr
        (BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) (hphBase + 40) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (247 : Word)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 11: SUB x11, x11, x7
  have hSub11 : cpsTripleWithin 1 (hphBase + 44) (hphBase + 48) hphCode
      ((.x1 ↦ᵣ retHdr) **
        (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) **
        (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x11 ↦ᵣ (thisLen - BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0l := cpsTripleWithin_extend_code hmono11
      (sub_spec_gen_rd_eq_rs1_within .x11 .x7 thisLen
        (BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) (hphBase + 44) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64
          (headersParentHash_b0 thisBytes - 246))) ** (.x12 ↦ᵣ hphClaimed) **
        (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64)) ** ((.x6 ↦ᵣ (247 : Word)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0l
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) h0f
  -- instruction 12: JAL x0, 12 — to instruction 15
  have hJal0 := jal_x0_spec_gen_within (12 : BitVec 21) (hphBase + 48)
  rw [hphSE21_12, hphA12] at hJal0
  have hJal_ext := cpsTripleWithin_extend_code hmono12 hJal0
  have hJal_fr := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ retHdr) **
      (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
      (.x11 ↦ᵣ (thisLen - BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
      (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
      (.x6 ↦ᵣ (247 : Word)) **
      (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
      (.x28 ↦ᵣ (2 : Word)) **
      bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) (by pcFree) hJal_ext
  have hJal : cpsTripleWithin 1 (hphBase + 48) (hphBase + 60) hphCode
      ((.x1 ↦ᵣ retHdr) **
        (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x11 ↦ᵣ (thisLen - BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) **
        (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x11 ↦ᵣ (thisLen - BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (thisBytes[0]'h0).zeroExtend 64) **
        (.x6 ↦ᵣ (247 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) **
        (.x28 ↦ᵣ (2 : Word)) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
    cpsTripleWithin_weaken (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hq => by simpa only [sepConj_emp_left'] using hq) hJal_fr
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hLbu h192
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hNt2
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 h248
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hNt4
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 h247
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hSub
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 h2li
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hNt8
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s8 hAddi7
  have s10 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s9 hAdd10
  have s11 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s10 hSub11
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s11 hJal
  exact cpsTripleWithin_mono_nSteps
    (show 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≤ 13 from by omega) s12

end EvmAsm.Codegen
