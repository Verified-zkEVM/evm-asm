/-
  EvmAsm.Evm64.ReturnData.CopyLoopSpec

  The RETURNDATACOPY copy loop (`base+0 → base+24`), a bottom-tested
  `do { copy; advance; dec } while (cnt != 0)`.  Every byte is in bounds (the
  handler's `start+size > retlen → revert` guard is glue), so this is a plain
  unconditional copy — structurally the MCOPY forward loop but with the source in
  a SEPARATE region (the return-data frame) from the destination (EVM memory),
  and a bottom test (`BNE cnt x0`) instead of a top guard.

  Reuses the `Mcopy` destination content model (`mcopyFwdContent`, same shape as
  CALLDATACOPY's `copyDestContent`) and the `cc_*` counter/byte helpers.

  `rdc_body_spec_within` is one straight-line iteration (`base+0 → base+20`);
  `evm_returndatacopy_loop_spec_within` closes the `do..while` by induction on the
  remaining count (`size ≥ 1`; size = 0 is the handler's glue `beqz` skip).
-/

import EvmAsm.Evm64.ReturnData.CopyProgram
import EvmAsm.Evm64.Mcopy.ForwardLoopSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace ReturnData

open EvmAsm.Rv64
open EvmAsm.Evm64.Mcopy (mcopyFwdContent mcopyFwdContent_length mcopyFwdContent_set
  mcopyFwdContent_zero mcopyFwdContent_full cc_word_succ_dec cc_word_succ_ne_zero
  cc_trunc_zeroExtend)

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- One straight-line iteration of the RETURNDATACOPY loop (`base+0 → base+20`,
    indices [0..4]): read `srcBytes[i]` from the frame region, store it at
    destination index `i` in EVM memory, advance both pointers and the counter. -/
theorem rdc_body_spec_within
    (base memBase srcBase : Word) (destOff i : Nat)
    (srcBytes memBytes : List (BitVec 8)) (cntV scratchOld : Word)
    (h_i : i < srcBytes.length)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_win : destOff + srcBytes.length ≤ memBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 5 (base + 0) (base + 20)
      (evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base)
      (((.x19 : Reg) ↦ᵣ scratchOld) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 i)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x16 : Reg) ↦ᵣ cntV) **
       bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff i) **
       bytesRegion srcBase srcBytes)
      (((.x19 : Reg) ↦ᵣ ((srcBytes[i]'h_i).zeroExtend 64)) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       ((.x16 : Reg) ↦ᵣ (cntV + signExtend12 (-1 : BitVec 12))) **
       bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff (i + 1)) **
       bytesRegion srcBase srcBytes) := by
  have hlen : (mcopyFwdContent memBytes srcBytes destOff i).length = memBytes.length :=
    mcopyFwdContent_length memBytes srcBytes destOff i (by omega) (by omega)
  have hset : (mcopyFwdContent memBytes srcBytes destOff i).set (destOff + i)
        (((srcBytes[i]'h_i).zeroExtend 64).truncate 8)
      = mcopyFwdContent memBytes srcBytes destOff (i + 1) := by
    rw [cc_trunc_zeroExtend]
    exact mcopyFwdContent_set memBytes srcBytes destOff i (srcBytes[i]'h_i) (by omega)
      (by omega) rfl
  set srcP := srcBase + BitVec.ofNat 64 i with hsrcP
  set destP := memBase + BitVec.ofNat 64 (destOff + i) with hdestP
  -- [0] LBU x19 x17 0 : x19 := srcBytes[i].zeroExtend 64.
  have h0 := bytesRegion_lbu_within .x19 .x17 srcBase scratchOld (base + 0)
    srcBytes i (by decide) h_src_align h_i (by omega) (h_src_valid i h_i)
  rw [← hsrcP] at h0
  -- [1] SB x18 x19 0 : store at destination index i.
  have h1 := bytesRegion_sb_within .x18 .x19 memBase ((srcBytes[i]'h_i).zeroExtend 64)
    (base + 4) (mcopyFwdContent memBytes srcBytes destOff i) (destOff + i) h_mem_align
    (by rw [hlen]; omega) (by omega) (h_mem_valid (destOff + i) (by omega))
  rw [← hdestP, hset] at h1
  -- [2] ADDI x17 x17 1
  have h2 := addi_spec_gen_same_within .x17 srcP (1 : BitVec 12) (base + 8) (by decide)
  rw [show srcP + signExtend12 (1 : BitVec 12) = srcBase + BitVec.ofNat 64 (i + 1) from by
        rw [hsrcP, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at h2
  -- [3] ADDI x18 x18 1
  have h3 := addi_spec_gen_same_within .x18 destP (1 : BitVec 12) (base + 12) (by decide)
  rw [show destP + signExtend12 (1 : BitVec 12) = memBase + BitVec.ofNat 64 (destOff + (i + 1)) from by
        rw [hdestP, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at h3
  -- [4] ADDI x16 x16 -1
  have h4 := addi_spec_gen_same_within .x16 cntV (-1 : BitVec 12) (base + 16) (by decide)
  -- Code-monotonicity for each index.
  have m0 : ∀ a i, CodeReq.singleton (base + 0) (.LBU .x19 .x17 0) a = some i
      → evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_returndatacopy_loop .x18 .x17 .x16 .x19) 0
      (base + 0) (by rw [evm_returndatacopy_loop_length]; norm_num)
      (by rw [evm_returndatacopy_loop_length]; norm_num) (by rfl))
  have m1 : ∀ a i, CodeReq.singleton (base + 4) (.SB .x18 .x19 0) a = some i
      → evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_returndatacopy_loop .x18 .x17 .x16 .x19) 1
      (base + 4) (by rw [evm_returndatacopy_loop_length]; norm_num)
      (by rw [evm_returndatacopy_loop_length]; norm_num) (by rfl))
  have m2 : ∀ a i, CodeReq.singleton (base + 8) (.ADDI .x17 .x17 1) a = some i
      → evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_returndatacopy_loop .x18 .x17 .x16 .x19) 2
      (base + 8) (by rw [evm_returndatacopy_loop_length]; norm_num)
      (by rw [evm_returndatacopy_loop_length]; norm_num) (by rfl))
  have m3 : ∀ a i, CodeReq.singleton (base + 12) (.ADDI .x18 .x18 1) a = some i
      → evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_returndatacopy_loop .x18 .x17 .x16 .x19) 3
      (base + 12) (by rw [evm_returndatacopy_loop_length]; norm_num)
      (by rw [evm_returndatacopy_loop_length]; norm_num) (by rfl))
  have m4 : ∀ a i, CodeReq.singleton (base + 16) (.ADDI .x16 .x16 (-1 : BitVec 12)) a = some i
      → evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_returndatacopy_loop .x18 .x17 .x16 .x19) 4
      (base + 16) (by rw [evm_returndatacopy_loop_length]; norm_num)
      (by rw [evm_returndatacopy_loop_length]; norm_num) (by rfl))
  have h0e := cpsTripleWithin_extend_code m0 h0
  have h1e := cpsTripleWithin_extend_code m1 h1
  have h2e := cpsTripleWithin_extend_code m2 h2
  have h3e := cpsTripleWithin_extend_code m3 h3
  have h4e := cpsTripleWithin_extend_code m4 h4
  rw [show (base + 0 : Word) + 4 = base + 4 from by bv_omega] at h0e
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at h1e
  rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at h2e
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at h3e
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at h4e
  have f0 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ destP) ** ((.x16 : Reg) ↦ᵣ cntV) **
     bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff i)) (by pcFreeR) h0e
  have f1 := cpsTripleWithin_frameR
    (((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 i)) ** ((.x16 : Reg) ↦ᵣ cntV) **
     bytesRegion srcBase srcBytes) (by pcFreeR) h1e
  have f2 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ ((srcBytes[i]'h_i).zeroExtend 64)) **
     ((.x18 : Reg) ↦ᵣ destP) **
     ((.x16 : Reg) ↦ᵣ cntV) **
     bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff (i + 1)) **
     bytesRegion srcBase srcBytes) (by pcFreeR) h2e
  have f3 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ ((srcBytes[i]'h_i).zeroExtend 64)) **
     ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
     ((.x16 : Reg) ↦ᵣ cntV) **
     bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff (i + 1)) **
     bytesRegion srcBase srcBytes) (by pcFreeR) h3e
  have f4 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ ((srcBytes[i]'h_i).zeroExtend 64)) **
     ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
     ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
     bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff (i + 1)) **
     bytesRegion srcBase srcBytes) (by pcFreeR) h4e
  simp only [sepConj_assoc'] at f0 f1 f2 f3 f4
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f0 f1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f2
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f3
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f4
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s4

/-- The RETURNDATACOPY copy loop closure (`base+0 → base+24`) by induction on the
    remaining count.  The loop is bottom-tested, so it always copies at least one
    byte — the spec is stated for a nonzero remaining count `n+1`. -/
theorem evm_returndatacopy_loop_spec_within
    (base memBase srcBase : Word) (destOff n i : Nat)
    (srcBytes memBytes : List (BitVec 8)) (scratchV : Word)
    (h_ni : i + (n + 1) = srcBytes.length)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_win : destOff + srcBytes.length ≤ memBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * (n + 1)) (base + 0) (base + 24)
      (evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base)
      (((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 i)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x19 : Reg) ↦ᵣ scratchV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff i) **
       bytesRegion srcBase srcBytes)
      (((.x16 : Reg) ↦ᵣ (0 : Word)) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcBytes.length)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + srcBytes.length))) **
       regOwn .x19 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff srcBytes.length) **
       bytesRegion srcBase srcBytes) := by
  have hmono5 : ∀ a i, CodeReq.singleton (base + 20) (.BNE .x16 .x0 (-20 : BitVec 13)) a = some i
      → evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_returndatacopy_loop .x18 .x17 .x16 .x19) 5
      (base + 20) (by rw [evm_returndatacopy_loop_length]; norm_num)
      (by rw [evm_returndatacopy_loop_length]; norm_num) (by rfl))
  have ha_back : (base + 20) + signExtend13 (-20 : BitVec 13) = base + 0 := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have ha_f : (base + 20 : Word) + 4 = base + 24 := by bv_omega
  induction n generalizing i scratchV with
  | zero =>
    have hi_lt : i < srcBytes.length := by omega
    have hbody := rdc_body_spec_within base memBase srcBase destOff i srcBytes memBytes
      (BitVec.ofNat 64 1) scratchV hi_lt h_src_align h_mem_align h_win h_src_over
      h_src_valid h_mem_over h_mem_valid
    rw [show (BitVec.ofNat 64 1) + signExtend12 (-1 : BitVec 12) = (0 : Word) from by
          have h := cc_word_succ_dec 0; rw [show (0 : Word) = BitVec.ofNat 64 0 from by decide];
          simpa using h] at hbody
    have hbodyf := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFreeR) hbody
    -- BNE not taken (cnt = 0): fall through to base+24.
    have hbne := bne_spec_gen_within .x16 .x0 (-20 : BitVec 13) (0 : Word) (0 : Word) (base + 20)
    rw [ha_back, ha_f] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono5 hbne
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
    have hntf := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ ((srcBytes[i]'hi_lt).zeroExtend 64)) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff (i + 1)) **
       bytesRegion srcBase srcBytes) (by pcFreeR) hnt
    simp only [sepConj_assoc'] at hbodyf hntf
    have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hbodyf hntf
    -- i + 1 = srcBytes.length in this case.
    rw [show i + 1 = srcBytes.length from by omega] at s
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun sState hq => by
        have hq2 : (((.x19 : Reg) ↦ᵣ ((srcBytes[i]'hi_lt).zeroExtend 64)) **
            ((.x16 : Reg) ↦ᵣ (0 : Word)) **
            ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcBytes.length)) **
            ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + srcBytes.length))) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff srcBytes.length) **
            bytesRegion srcBase srcBytes) sState := by xperm_chunked hq
        have hq3 := sepConj_mono_left (regIs_implies_regOwn .x19) _ hq2
        xperm_chunked hq3) s)
  | succ m ih =>
    have hi_lt : i < srcBytes.length := by omega
    have hbody := rdc_body_spec_within base memBase srcBase destOff i srcBytes memBytes
      (BitVec.ofNat 64 (m + 2)) scratchV hi_lt h_src_align h_mem_align h_win h_src_over
      h_src_valid h_mem_over h_mem_valid
    rw [show (BitVec.ofNat 64 (m + 2)) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 (m + 1) from
          cc_word_succ_dec (m + 1)] at hbody
    have hbodyf := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFreeR) hbody
    -- BNE taken (cnt = m+1 ≠ 0): back to base+0.
    have hbne := bne_spec_gen_within .x16 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (m + 1))
      (0 : Word) (base + 20)
    rw [ha_back, ha_f] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono5 hbne
    have ht := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact cc_word_succ_ne_zero m (by omega) ((sepConj_pure_right _).1 hQ).2)
    have htf := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ ((srcBytes[i]'hi_lt).zeroExtend 64)) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       bytesRegion memBase (mcopyFwdContent memBytes srcBytes destOff (i + 1)) **
       bytesRegion srcBase srcBytes) (by pcFreeR) ht
    have hih := ih (i + 1) ((srcBytes[i]'hi_lt).zeroExtend 64) (by omega)
    simp only [sepConj_assoc'] at hbodyf htf
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hbodyf htf
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) s2)

end ReturnData
end EvmAsm.Evm64
