/-
  The two 32-byte hash-copy loops of `headerExtendedDecode_prog`
  (`Programs/HeaderDecode.lean`, PR-K39): parent_hash ([22]-[27]) and
  state_root ([48]-[53]).

  Each field is materialised by a byte-safe `LBU`/`SB` do-while copy (the pkljc
  #10349 byte-fix): with `x28` the source cursor, `x29` the output cursor, `x5`
  the remaining count and `x6` the byte scratch, each iteration

    LBU x6, 0(x28)    SB  x6, 0(x29)
    ADDI x28, x28, 1  ADDI x29, x29, 1
    ADDI x5, x5, -1   BNE x5, x0, -20

  copies one byte and decrements the counter.  This module hosts the reusable
  per-byte step (`hedCopyBody5`) and the full bottom-tested loop
  (`hedCopyLoop`), both parameterised by the loop's `LBU` address `A` and the
  five/six per-instruction `fullCode`-membership witnesses (so the same proof
  serves both copy loops).  The content tie is the `copyIntoRegion`
  accumulator shared with the header-root extractors.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeSpec

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

private theorem hed_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem hed_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

private theorem hed_ofNat_ne_zero (n : Nat) (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  intro heq
  have h2 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
      show (0 : Word).toNat = 0 from by decide] at h2
  omega

set_option maxRecDepth 8000 in
/-- One copy-loop body ([b]-[b+4], `A → A+20`): copy one byte from
    `srcBase[srcOff+i]` to `dstBase[dstOff+i]` (advancing both cursors) and
    decrement the counter `x5` from `m+1` to `m`.  The destination content grows
    by one byte in the `copyIntoRegion` accumulator.  Byte scratch is `x6`. -/
theorem hedCopyBody5 (A srcBase dstBase v6old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i m : Nat)
    (hLBU : ∀ a i, CodeReq.singleton A (.LBU .x6 .x28 (0 : BitVec 12)) a = some i → fullCode a = some i)
    (hSB : ∀ a i, CodeReq.singleton (A + 4) (.SB .x29 .x6 (0 : BitVec 12)) a = some i → fullCode a = some i)
    (h28 : ∀ a i, CodeReq.singleton (A + 8) (.ADDI .x28 .x28 (1 : BitVec 12)) a = some i → fullCode a = some i)
    (h29 : ∀ a i, CodeReq.singleton (A + 12) (.ADDI .x29 .x29 (1 : BitVec 12)) a = some i → fullCode a = some i)
    (h5c : ∀ a i, CodeReq.singleton (A + 16) (.ADDI .x5 .x5 (-1 : BitVec 12)) a = some i → fullCode a = some i)
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
    cpsTripleWithin 5 A (A + 20) fullCode
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x6 : Reg) ↦ᵣ v6old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 m) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
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
  -- [b] lbu x6, 0(x28)
  have hlbu := bytesRegion_lbu_within .x6 .x28 srcBase v6old A
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code hLBU hlbu
  have hlbuf := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hlbue
  -- [b+1] sb x6, 0(x29)
  have hsb := bytesRegion_sb_within .x29 .x6 dstBase (bval.zeroExtend 64) (A + 4)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep] at hsb
  have hsbe := cpsTripleWithin_extend_code hSB hsb
  have hsbf := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hsbe
  -- [b+2] addi x28, x28, 1
  have h3 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (A + 8) (by decide)
  rw [hed_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega] at h3
  have h3e := cpsTripleWithin_extend_code h28 h3
  have h3f := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x6 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h3e
  -- [b+3] addi x29, x29, 1
  have h4 := addi_spec_gen_same_within .x29
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (A + 12) (by decide)
  rw [hed_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega] at h4
  have h4e := cpsTripleWithin_extend_code h29 h4
  have h4f := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x6 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h4e
  -- [b+4] addi x5, x5, -1
  have h5 := addi_spec_gen_same_within .x5 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (A + 16) (by decide)
  rw [hed_succ_dec m] at h5
  have h5e := cpsTripleWithin_extend_code h5c h5
  have h5f := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x6 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h5e
  -- addresses collapse: A + 4 + 4 + 4 + 4 + 4 = A + 20
  rw [show (A + 4 : Word) = A + 4 from rfl] at hsbf
  rw [show (A : Word) + 4 + 4 = A + 8 from by bv_omega] at *
  rw [show (A : Word) + 8 + 4 = A + 12 from by bv_omega] at *
  rw [show (A : Word) + 12 + 4 = A + 16 from by bv_omega] at *
  rw [show (A : Word) + 16 + 4 = A + 20 from by bv_omega] at *
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1234 h5f
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by rw [hgetd]; xperm_hyp hq) s12345

#print axioms hedCopyBody5

set_option maxRecDepth 8000 in
/-- The bottom-tested 32-byte copy loop closure ([b]-[b+5], `A → A+24`): each
    round copies one byte via `hedCopyBody5` ([b]-[b+4]) then `BNE x5, x0, -20`
    at [b+5] loops back while the counter is nonzero, exiting when it reaches
    `0`.  Copies `n+1` bytes, growing the `copyIntoRegion` accumulator. -/
theorem hedCopyLoop (A srcBase dstBase v6old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i n : Nat)
    (hLBU : ∀ a i, CodeReq.singleton A (.LBU .x6 .x28 (0 : BitVec 12)) a = some i → fullCode a = some i)
    (hSB : ∀ a i, CodeReq.singleton (A + 4) (.SB .x29 .x6 (0 : BitVec 12)) a = some i → fullCode a = some i)
    (h28 : ∀ a i, CodeReq.singleton (A + 8) (.ADDI .x28 .x28 (1 : BitVec 12)) a = some i → fullCode a = some i)
    (h29 : ∀ a i, CodeReq.singleton (A + 12) (.ADDI .x29 .x29 (1 : BitVec 12)) a = some i → fullCode a = some i)
    (h5c : ∀ a i, CodeReq.singleton (A + 16) (.ADDI .x5 .x5 (-1 : BitVec 12)) a = some i → fullCode a = some i)
    (hBNE : ∀ a i, CodeReq.singleton (A + 20) (.BNE .x5 .x0 (-20 : BitVec 13)) a = some i → fullCode a = some i)
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
    cpsTripleWithin (6 * (n + 1)) A (A + 24) fullCode
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x6 : Reg) ↦ᵣ v6old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x5 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + (n + 1))))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + (n + 1))))) **
       regOwn .x6 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase
         (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + (n + 1)))) := by
  have hsrc_lt : srcBytes.length < 2 ^ 64 := by omega
  have htaken : (A + 20 : Word) + signExtend13 (-20 : BitVec 13) = A := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have hfall : (A + 20 : Word) + 4 = A + 24 := by bv_omega
  induction n generalizing i v6old with
  | zero =>
    have hbody := hedCopyBody5 A srcBase dstBase v6old srcBytes dstBytes srcOff dstOff i 0
      hLBU hSB h28 h29 h5c
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over
      h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x5 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (A + 20)
    rw [htaken, hfall] at hbne
    have hbnee := cpsBranchWithin_extend_code hBNE hbne
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hnt
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbody hntf
    refine cpsTripleWithin_mono_nSteps (nSteps := 5 + 1) (by omega) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        simp only [Nat.zero_add]
        rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
        have hq2 := sepConj_mono_left (regIs_implies_regOwn .x6) _
          (show (((.x6 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
            ((.x5 : Reg) ↦ᵣ (0 : Word)) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
            ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
            bytesRegion srcBase srcBytes **
            bytesRegion dstBase
              (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) _ from by
            xperm_hyp hq)
        xperm_hyp hq2) s1
  | succ k ih =>
    have hbody := hedCopyBody5 A srcBase dstBase v6old srcBytes dstBytes srcOff dstOff i (k + 1)
      hLBU hSB h28 h29 h5c
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over
      h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x5 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (A + 20)
    rw [htaken, hfall] at hbne
    have hbnee := cpsBranchWithin_extend_code hBNE hbne
    have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hed_ofNat_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have htkf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) htk
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega)
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbody htkf
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (nSteps := (5 + 1) + 6 * (k + 1)) (by omega) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        simp only [show i + 1 + (k + 1) = i + (k + 1 + 1) from by omega] at hq
        xperm_hyp hq) s2

#print axioms hedCopyLoop

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
