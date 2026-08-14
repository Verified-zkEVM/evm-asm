/-
  EvmAsm.Codegen.Programs.HeadersParentHashMain

  The whole-routine machine triple for the emitted guest routine
  `headers_parent_hash` (issue #12346): dispatch on the first header
  byte, composing the prologue path lemmas
  (`HeadersParentHashPrologues.lean`) with the checks + copy-loop phase
  (`HeadersParentHashSpec.lean`).
-/

import EvmAsm.Codegen.Programs.HeadersParentHashPrologues

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Whole-routine triple for `headers_parent_hash`.

    Static preconditions only; the outcome is stated in the
    postcondition via `headersParentHash_status` /
    `headersParentHash_out`.  The 312-step bound covers the worst path
    (long-form success: 13 prologue + 6 checks + 32 × 9 copy loop
    + 2 exit + 2 return = 311). -/
theorem headers_parent_hash_spec_within
    (retHdr thisPtr thisLen : Word)
    (v5 v6 v7 v28 : Word)
    (thisBytes claimedBytes : List (BitVec 8))
    (F : Assertion)
    (hF : F.pcFree)
    (hret : retHdr &&& ~~~(1 : Word) = retHdr)
    (hlen : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaimed : claimedBytes.length = 32)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 312 hphBase retHdr hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
       (.x12 ↦ᵣ hphClaimed) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes ** F)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ headersParentHash_status thisBytes) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       bytesRegion hphClaimed (headersParentHash_out thisBytes claimedBytes) **
       bytesRegion thisPtr thisBytes ** regOwn .x11 ** regOwn .x12 ** F) := by
  have h0 : 0 < thisBytes.length := by omega
  have hlen64 : thisBytes.length < 2 ^ 64 := by rw [hlen]; exact BitVec.isLt thisLen
  by_cases hb0lt192 : headersParentHash_b0 thisBytes < 192
  · -- low guard fails: 5 steps
    have hP := hph_fail_low_spec_within retHdr thisPtr thisLen v5 v6 v7 v28
      thisBytes claimedBytes hsalign hsover hsvalid hclaimed hret h0 hb0lt192
    have hM := cpsTripleWithin_mono_nSteps (show 5 ≤ 312 from by omega) hP
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq) (cpsTripleWithin_frameR F hF hM)
  · push Not at hb0lt192
    by_cases hb0lt248 : headersParentHash_b0 thisBytes < 248
    · -- short-form prologue (7 steps) then checks + copy (298 steps)
      have hP := hph_prologue_short_spec_within retHdr thisPtr thisLen v5 v6 v7 v28
        thisBytes claimedBytes hsalign hsover hsvalid h0 hb0lt192 hb0lt248
      have hskip : (1 : Nat) = headersParentHash_skip (headersParentHash_b0 thisBytes) := by
        simp only [headersParentHash_skip, if_pos hb0lt248]
      have hw11 : (thisLen - (1 : Word)).toNat = thisBytes.length - 1 := by
        simp only [BitVec.toNat_sub, show (1 : Word).toNat = 1 from by decide]
        omega
      have hF15 := hph_from15_spec_within retHdr hret thisPtr (thisLen - (1 : Word)) 1
        ((thisBytes[0]'h0).zeroExtend 64) (248 : Word) v7 v28
        thisBytes claimedBytes hsalign hsover hsvalid hclaimed hb0lt192
        (by omega) hskip hw11 (by omega)
      have s := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hP hF15
      have hM := cpsTripleWithin_mono_nSteps (show 7 + 298 ≤ 312 from by omega) s
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => by xperm_hyp hq) (cpsTripleWithin_frameR F hF hM)
    · push Not at hb0lt248
      by_cases hb0le249 : headersParentHash_b0 thisBytes ≤ 249
      · -- long-form prologue (13 steps) then checks + copy (298 steps)
        have hP := hph_prologue_long_spec_within retHdr thisPtr thisLen v5 v6 v7 v28
          thisBytes claimedBytes hsalign hsover hsvalid h0 hb0lt248 hb0le249
        have hskip : (headersParentHash_b0 thisBytes - 246) =
            headersParentHash_skip (headersParentHash_b0 thisBytes) := by
          simp only [headersParentHash_skip, if_neg (show ¬ headersParentHash_b0 thisBytes < 248 from by omega)]
        have hw11 :
            (thisLen - BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)).toNat =
              thisBytes.length - (headersParentHash_b0 thisBytes - 246) := by
          have hb0lt256 := hphB0_lt_256 thisBytes
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show headersParentHash_b0 thisBytes - 246 < 2 ^ 64 from by omega)]
          omega
        have hF15 := hph_from15_spec_within retHdr hret thisPtr
          (thisLen - BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246))
          (headersParentHash_b0 thisBytes - 246)
          ((thisBytes[0]'h0).zeroExtend 64) (247 : Word)
          (BitVec.ofNat 64 (headersParentHash_b0 thisBytes - 246)) (2 : Word)
          thisBytes claimedBytes hsalign hsover hsvalid hclaimed (by omega) hb0le249 hskip
          hw11 (by have := hphB0_lt_256 thisBytes; omega)
        have s := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hP hF15
        have hM := cpsTripleWithin_mono_nSteps (show 13 + 298 ≤ 312 from by omega) s
        exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun h hq => by xperm_hyp hq) (cpsTripleWithin_frameR F hF hM)
      · -- high guard fails: 11 steps
        push Not at hb0le249
        have hP := hph_fail_high_spec_within retHdr thisPtr thisLen v5 v6 v7 v28
          thisBytes claimedBytes hsalign hsover hsvalid hclaimed hret h0 hb0lt248 hb0le249
        have hM := cpsTripleWithin_mono_nSteps (show 11 ≤ 312 from by omega) hP
        exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun h hq => by xperm_hyp hq) (cpsTripleWithin_frameR F hF hM)


end EvmAsm.Codegen
