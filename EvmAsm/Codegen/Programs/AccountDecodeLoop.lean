/-
  The fixed 32-byte copy loops of `accountDecode_prog` (storage_root, field 2,
  instrs [90]-[95]; and code_hash, field 3, instrs [116]-[121]).

  Both are byte-safe `LBU`/`SB` bottom-tested do-while copies (the pkljc #10344
  byte-fix).  With `x28` the source cursor, `rd` the output cursor (x20 for
  storage_root, x21 for code_hash), `x6` the remaining count and `x29` the byte
  scratch, each iteration

    LBU  x29, 0(x28)   SB  rd,  0(x29)  [i.e. store x29's byte at [rd]]
    ADDI x28, x28, 1   ADDI rd, rd, 1
    ADDI x6,  x6, -1   BNE  x6, x0, -20

  copies one byte and decrements the counter.  This module hosts a **generic**
  per-byte step (`adCopyBody`) and loop closure (`adCopyLoop`), parameterised on
  the destination register `rd` and the loop's guest byte-base `GB`, taking the
  per-instruction fetch facts as hypotheses so both fixed-32 fields reuse it.
  The content tie is the same `copyIntoRegion` accumulator used by
  `WithdrawalDecodeSpec.wdCopyLoop`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeSpec

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

private theorem ad_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem ad_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

private theorem ad_ofNat_ne_zero (n : Nat) (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  intro heq
  have h2 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
      show (0 : Word).toNat = 0 from by decide] at h2
  omega

/-- The per-instruction fetch facts for one fixed-32 copy loop, bundled: the
    five body instructions at `GB..GB+16` and the back-edge `BNE` at `GB+20`. -/
structure CopyFetch (rd : Reg) (GB : Word) : Prop where
  lbu : ∀ a i, CodeReq.singleton GB (.LBU .x29 .x28 (0 : BitVec 12)) a = some i → adCode a = some i
  sb : ∀ a i, CodeReq.singleton (GB + 4) (.SB rd .x29 (0 : BitVec 12)) a = some i → adCode a = some i
  a28 : ∀ a i, CodeReq.singleton (GB + 8) (.ADDI .x28 .x28 (1 : BitVec 12)) a = some i → adCode a = some i
  ard : ∀ a i, CodeReq.singleton (GB + 12) (.ADDI rd rd (1 : BitVec 12)) a = some i → adCode a = some i
  a6 : ∀ a i, CodeReq.singleton (GB + 16) (.ADDI .x6 .x6 (-1 : BitVec 12)) a = some i → adCode a = some i
  bne : ∀ a i, CodeReq.singleton (GB + 20) (.BNE .x6 .x0 (-20 : BitVec 13)) a = some i → adCode a = some i

set_option maxRecDepth 8000 in
/-- One copy-loop body (`GB → GB+20`): copy one byte from `srcBase[srcOff+i]` to
    `dstBase[dstOff+i]` (advancing both cursors) and decrement the counter from
    `m+1` to `m`.  The destination content grows by one byte in the
    `copyIntoRegion` accumulator.  Generic in the destination register `rd`. -/
theorem adCopyBody (rd : Reg) (GB srcBase dstBase x29old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i m : Nat)
    (hrd0 : rd ≠ .x0)
    (hfetch : CopyFetch rd GB)
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
    cpsTripleWithin 5 GB (GB + 20) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x29 : Reg) ↦ᵣ x29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 m) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
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
  -- LBU x29, 0(x28)
  have hlbu := bytesRegion_lbu_within .x29 .x28 srcBase x29old GB
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code hfetch.lbu hlbu)
  have hlbuf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hlbue
  -- SB rd, x29 (store x29's byte at [rd])
  have hsb := bytesRegion_sb_within rd .x29 dstBase (bval.zeroExtend 64) (GB + 4)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (GB + 4 : Word) + 4 = GB + 8 from by bv_omega] at hsb
  have hsbe := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code hfetch.sb hsb)
  have hsbf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hsbe
  -- ADDI x28, x28, 1
  have h3 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (GB + 8) (by decide)
  rw [ad_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (GB + 8 : Word) + 4 = GB + 12 from by bv_omega] at h3
  have h3e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code hfetch.a28 h3)
  have h3f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h3e
  -- ADDI rd, rd, 1
  have h4 := addi_spec_gen_same_within rd
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (GB + 12) hrd0
  rw [ad_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (GB + 12 : Word) + 4 = GB + 16 from by bv_omega] at h4
  have h4e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code hfetch.ard h4)
  have h4f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h4e
  -- ADDI x6, x6, -1
  have h5 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (GB + 16) (by decide)
  rw [ad_succ_dec m, show (GB + 16 : Word) + 4 = GB + 20 from by bv_omega] at h5
  have h5e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code hfetch.a6 h5)
  have h5f := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h5e
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1234 h5f
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by rw [hgetd]; xperm_chunked hq) s12345

#print axioms adCopyBody

set_option maxRecDepth 8000 in
/-- The bottom-tested fixed-32-style copy loop closure (`GB → GB+24`): each round
    copies one byte via `adCopyBody` and then `BNE x6, x0` at `GB+20` loops back
    to the header while the counter is nonzero, exiting when it reaches `0`.
    Copies `n+1` bytes, growing the `copyIntoRegion` accumulator.  Generic in the
    destination register `rd`. -/
theorem adCopyLoop (rd : Reg) (GB srcBase dstBase x29old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i n : Nat)
    (hrd0 : rd ≠ .x0)
    (hfetch : CopyFetch rd GB)
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
    cpsTripleWithin (6 * (n + 1)) GB (GB + 24) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x29 : Reg) ↦ᵣ x29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + (n + 1))))) **
       (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + (n + 1))))) **
       regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase
         (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + (n + 1)))) := by
  have htaken : (GB + 20 : Word) + signExtend13 (-20 : BitVec 13) = GB := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have hfall : (GB + 20 : Word) + 4 = GB + 24 := by bv_omega
  induction n generalizing i x29old with
  | zero =>
    have hbody := adCopyBody rd GB srcBase dstBase x29old srcBytes dstBytes srcOff dstOff i 0
      hrd0 hfetch h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over
      h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (GB + 20)
    rw [htaken, hfall] at hbne
    have hbnee := cpsBranchWithin_extend_code ad_mono
      (cpsBranchWithin_extend_code hfetch.bne hbne)
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hnt
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hbody hntf
    refine cpsTripleWithin_mono_nSteps (nSteps := 5 + 1) (by omega) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [Nat.zero_add]
        rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
        have hq2 := sepConj_mono_left (regIs_implies_regOwn .x29) _
          (show (((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
            ((.x6 : Reg) ↦ᵣ (0 : Word)) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
            (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
            bytesRegion srcBase srcBytes **
            bytesRegion dstBase
              (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) _ from by
            xperm_chunked hq)
        xperm_chunked hq2) s1
  | succ k ih =>
    have hbody := adCopyBody rd GB srcBase dstBase x29old srcBytes dstBytes srcOff dstOff i (k + 1)
      hrd0 hfetch h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over
      h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (GB + 20)
    rw [htaken, hfall] at hbne
    have hbnee := cpsBranchWithin_extend_code ad_mono
      (cpsBranchWithin_extend_code hfetch.bne hbne)
    have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ad_ofNat_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have htkf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       (rd ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) htk
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega)
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hbody htkf
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (nSteps := (5 + 1) + 6 * (k + 1)) (by omega) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [show i + 1 + (k + 1) = i + (k + 1 + 1) from by omega] at hq
        xperm_chunked hq) s2

#print axioms adCopyLoop

end EvmAsm.Codegen.AccountDecodeSpec
