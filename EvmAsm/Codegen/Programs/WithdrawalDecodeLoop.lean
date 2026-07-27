/-
  The 20-byte address copy loop of `withdrawalDecode_prog` ([39]-[44]).

  The address field is materialised by a byte-safe `LBU`/`SB` do-while copy
  (the pkljc #10343 byte-fix): with `x28` the source cursor, `x29` the output
  cursor, `x6` the remaining count and `x30` the byte scratch, each iteration

    [39] LBU x30, 0(x28)   [40] SB  x30, 0(x29)
    [41] ADDI x28, x28, 1  [42] ADDI x29, x29, 1
    [43] ADDI x6,  x6, -1  [44] BNE x6, x0, -20

  copies one byte and decrements the counter.  This module hosts the reusable
  per-byte step (`wdCopyBody5`, instructions [39]-[43]), whose content tie is
  the same `copyIntoRegion` accumulator used by the header-root extractors.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.WithdrawalDecodeSpec

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

private theorem wd_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem wd_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

set_option maxRecDepth 8000 in
/-- One copy-loop body ([39]-[43], `WB+156 → WB+176`): copy one byte from
    `srcBase[srcOff+i]` to `dstBase[dstOff+i]` (advancing both cursors) and
    decrement the counter from `m+1` to `m`.  The destination content grows by
    one byte in the `copyIntoRegion` accumulator. -/
theorem wdCopyBody5 (srcBase dstBase x30old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i m : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_lt : srcOff + i < srcBytes.length)
    (h_dst_lt : dstOff + i < dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 5 (WB + 156) (WB + 176) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x30 : Reg) ↦ᵣ x30old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 m) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x30 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) := by
  set bval := srcBytes[srcOff + i]'h_src_lt with hbval
  have htrunc : (bval.zeroExtend 64).truncate 8 = bval := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := bval.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hgetd : srcBytes.getD (srcOff + i) 0 = bval := by
    rw [hbval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_src_lt]; rfl
  have hstep : copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)
      = (copyIntoRegion dstBytes srcBytes dstOff srcOff i).set (dstOff + i) bval := by
    simp only [copyIntoRegion, hgetd]
  -- [39] lbu x30, 0(x28)
  have hlbu := bytesRegion_lbu_within .x30 .x28 srcBase x30old (WB + 156)
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [show (WB + 156 : Word) + 4 = WB + 160 from by bv_omega, ← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 156) withdrawalDecode_prog 39
        (.LBU .x30 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) hlbu)
  have hlbuf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hlbue
  -- [40] sb x30, 0(x29)
  have hsb := bytesRegion_sb_within .x29 .x30 dstBase (bval.zeroExtend 64) (WB + 160)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (WB + 160 : Word) + 4 = WB + 164 from by bv_omega] at hsb
  have hsbe := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 160) withdrawalDecode_prog 40
        (.SB .x29 .x30 (0 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) hsb)
  have hsbf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hsbe
  -- [41] addi x28, x28, 1
  have h3 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (WB + 164) (by decide)
  rw [wd_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (WB + 164 : Word) + 4 = WB + 168 from by bv_omega] at h3
  have h3e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 164) withdrawalDecode_prog 41
        (.ADDI .x28 .x28 (1 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h3)
  have h3f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h3e
  -- [42] addi x29, x29, 1
  have h4 := addi_spec_gen_same_within .x29
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (WB + 168) (by decide)
  rw [wd_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (WB + 168 : Word) + 4 = WB + 172 from by bv_omega] at h4
  have h4e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 168) withdrawalDecode_prog 42
        (.ADDI .x29 .x29 (1 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h4)
  have h4f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h4e
  -- [43] addi x6, x6, -1
  have h5 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (WB + 172) (by decide)
  rw [wd_succ_dec m, show (WB + 172 : Word) + 4 = WB + 176 from by bv_omega] at h5
  have h5e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 172) withdrawalDecode_prog 43
        (.ADDI .x6 .x6 (-1 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h5)
  have h5f := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h5e
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1234 h5f
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by rw [hgetd]; xperm_chunked hq) s12345

#print axioms wdCopyBody5

private theorem wd_ofNat_ne_zero (n : Nat) (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  intro heq
  have h2 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
      show (0 : Word).toNat = 0 from by decide] at h2
  omega

set_option maxRecDepth 8000 in
/-- The bottom-tested 20-byte copy loop closure ([39]-[44], `WB+156 → WB+180`):
    each round copies one byte via `wdCopyBody5` ([39]-[43]) and then `BNE x6, x0`
    at [44] loops back to the header while the counter is nonzero, exiting when it
    reaches `0`.  Copies `n+1` bytes, growing the `copyIntoRegion` accumulator. -/
theorem wdCopyLoop (srcBase dstBase x30old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i n : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_bound : srcOff + i + (n + 1) ≤ srcBytes.length)
    (h_dst_bound : dstOff + i + (n + 1) ≤ dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * (n + 1)) (WB + 156) (WB + 180) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x30 : Reg) ↦ᵣ x30old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + (n + 1))))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + (n + 1))))) **
       regOwn .x30 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase
         (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + (n + 1)))) := by
  have hsrc_lt : srcBytes.length < 2 ^ 64 := by omega
  have htaken : (WB + 176 : Word) + signExtend13 (-20 : BitVec 13) = WB + 156 := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have hfall : (WB + 176 : Word) + 4 = WB + 180 := by bv_omega
  induction n generalizing i x30old with
  | zero =>
    -- one iteration: body (x6: 1 → 0) then BNE not-taken → exit.
    have hbody := wdCopyBody5 srcBase dstBase x30old srcBytes dstBytes srcOff dstOff i 0
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over
      h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (WB + 176)
    rw [htaken, hfall] at hbne
    have hbnee := cpsBranchWithin_extend_code wd_mono
      (cpsBranchWithin_extend_code (cr' := wdCode)
        (CodeReq.ofProg_mem_at WB (WB + 176) withdrawalDecode_prog 44
          (.BNE .x6 .x0 (-20 : BitVec 13)) (by bv_omega) (by rw [wd_length]; decide)
          rfl (by rw [wd_length]; decide)) hbne)
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x30 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hnt
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hbody hntf
    refine cpsTripleWithin_mono_nSteps (nSteps := 5 + 1) (by omega) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [Nat.zero_add]
        rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
        have hq2 := sepConj_mono_left (regIs_implies_regOwn .x30) _
          (show (((.x30 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
            ((.x6 : Reg) ↦ᵣ (0 : Word)) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
            ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
            bytesRegion srcBase srcBytes **
            bytesRegion dstBase
              (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) _ from by
            xperm_chunked hq)
        xperm_chunked hq2) s1
  | succ k ih =>
    -- body (x6: k+2 → k+1) then BNE taken → header, then loop (k+1 more).
    have hbody := wdCopyBody5 srcBase dstBase x30old srcBytes dstBytes srcOff dstOff i (k + 1)
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over
      h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (WB + 176)
    rw [htaken, hfall] at hbne
    have hbnee := cpsBranchWithin_extend_code wd_mono
      (cpsBranchWithin_extend_code (cr' := wdCode)
        (CodeReq.ofProg_mem_at WB (WB + 176) withdrawalDecode_prog 44
          (.BNE .x6 .x0 (-20 : BitVec 13)) (by bv_omega) (by rw [wd_length]; decide)
          rfl (by rw [wd_length]; decide)) hbne)
    have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact wd_ofNat_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have htkf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x30 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) htk
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega)
    -- compose: body ;; bne-taken ;; ih
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hbody htkf
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (nSteps := (5 + 1) + 6 * (k + 1)) (by omega) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [show i + 1 + (k + 1) = i + (k + 1 + 1) from by omega] at hq
        xperm_chunked hq) s2

#print axioms wdCopyLoop

end EvmAsm.Codegen.WithdrawalDecodeSpec
