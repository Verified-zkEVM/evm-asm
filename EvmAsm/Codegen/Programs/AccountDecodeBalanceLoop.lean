/-
  The balance right-aligned copy loop of `accountDecode_prog`
  (`Programs/State.lean`, field 1, instrs [65]-[71], `AB+260 → AB+288`).

  After the 32-byte output slot is zeroed and the destination cursor is set to
  `out + (32-len)` (instrs [55]-[64]), the `len` content bytes are copied
  forward into that cursor by a top-tested `BEQ`/`JAL` loop:

    [65] BEQ  x6, x0, +28   -- exit to AB+288 when x6 = 0
    [66] LBU  x30, 0(x28)
    [67] SB   x30, 0(x29)   -- store x30's byte at [x29]
    [68] ADDI x28, x28, 1
    [69] ADDI x29, x29, 1
    [70] ADDI x6,  x6, -1
    [71] JAL  x0, -24       -- back to AB+260

  The byte-copy reasoning is the same `copyIntoRegion` accumulator used by
  `AccountDecodeLoop.adCopyLoop` (byte temp `x30`, destination cursor `x29`,
  source cursor `x28`), re-derived here with the top-tested loop structure of
  `AccountDecodeNonceLoop.adNonceLoop`.  Starting from the fully-zeroed 32-byte
  buffer with destination offset `32-len`, the closure produces exactly
  `AccountDecodeSpec.balanceCopied`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

set_option maxRecDepth 8000

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs` cells. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-- `k`-th instruction membership of `accountDecode_prog` into `fullCode`. -/
local macro "adMemF" k:term ", " A:term ", " ins:term : term =>
  `((fun a i h => ad_mono a i
      (CodeReq.ofProg_mem_at AB $A accountDecode_prog $k $ins (by bv_omega)
        (by rw [ad_length]; omega) rfl (by rw [ad_length]; norm_num) a i h)))

/-! ## Address / counter arithmetic helpers -/

private theorem adb_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem adb_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

private theorem adb_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

/-! ## Balance right-align copy loop ([65]-[71], `AB+260 → AB+288`) -/

/-- **One balance-copy iteration** ([66]-[71], `AB+264 → AB+260`): load
    `srcBytes[srcOff+i]` into `x30`, store it at `dstBase[dstOff+i]`, advance
    both cursors, decrement the countdown, and take the back-edge `JAL`; the
    destination content grows by one byte in the `copyIntoRegion` accumulator. -/
private theorem adBalBody (srcBase dstBase x30old : Word)
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
    cpsTripleWithin 6 (AB + 264) (AB + 260) fullCode
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
  -- [66] LBU x30, 0(x28)
  have hlbu := bytesRegion_lbu_within .x30 .x28 srcBase x30old (AB + 264)
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [← hbval, show (AB + 264 : Word) + 4 = AB + 268 from by bv_omega] at hlbu
  have e66 := cpsTripleWithin_extend_code
    (adMemF 66, (AB + 264), (.LBU .x30 .x28 (0 : BitVec 12))) hlbu
  have f66 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by pcFreeR) e66
  -- [67] SB x30, 0(x29)  (store x30's byte at [x29])
  have hsb := bytesRegion_sb_within .x29 .x30 dstBase (bval.zeroExtend 64) (AB + 268)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (AB + 268 : Word) + 4 = AB + 272 from by bv_omega] at hsb
  have e67 := cpsTripleWithin_extend_code
    (adMemF 67, (AB + 268), (.SB .x29 .x30 (0 : BitVec 12))) hsb
  have f67 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by pcFreeR) e67
  -- [68] ADDI x28, x28, 1
  have h68 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (AB + 272) (by decide)
  rw [adb_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (AB + 272 : Word) + 4 = AB + 276 from by bv_omega] at h68
  have e68 := cpsTripleWithin_extend_code
    (adMemF 68, (AB + 272), (.ADDI .x28 .x28 (1 : BitVec 12))) h68
  have f68 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) e68
  -- [69] ADDI x29, x29, 1
  have h69 := addi_spec_gen_same_within .x29
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (AB + 276) (by decide)
  rw [adb_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (AB + 276 : Word) + 4 = AB + 280 from by bv_omega] at h69
  have e69 := cpsTripleWithin_extend_code
    (adMemF 69, (AB + 276), (.ADDI .x29 .x29 (1 : BitVec 12))) h69
  have f69 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) e69
  -- [70] ADDI x6, x6, -1
  have h70 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (AB + 280) (by decide)
  rw [adb_succ_dec m, show (AB + 280 : Word) + 4 = AB + 284 from by bv_omega] at h70
  have e70 := cpsTripleWithin_extend_code
    (adMemF 70, (AB + 280), (.ADDI .x6 .x6 (-1 : BitVec 12))) h70
  have f70 := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) e70
  -- [71] JAL x0, -24  → AB+260
  have h71 := jal_x0_spec_gen_within (-24 : BitVec 21) (AB + 284)
  rw [show AB + 284 + signExtend21 (-24 : BitVec 21) = AB + 260 from by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega] at h71
  have e71 := cpsTripleWithin_extend_code
    (adMemF 71, (AB + 284), (.JAL .x0 (-24 : BitVec 21))) h71
  have f71 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 m) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) e71
  rw [sepConj_emp_left'] at f71
  -- compose the six body steps ([66]-[71])
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f66 f67
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f68
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f69
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f70
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s4 f71
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by rw [hgetd]; xperm_chunked hq) s5)

/-- **The balance right-align copy loop closure** ([65]-[71], `AB+260 → AB+288`):
    by induction on the byte countdown `n`, copy the remaining `n` content bytes
    forward into the destination and exit through the top `BEQ` with `x6 = 0`.
    Grows the `copyIntoRegion` accumulator; starting from the zeroed buffer with
    `dstOff = 32-len` this yields `balanceCopied`. -/
theorem adBalLoop (srcBase dstBase x30old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i n : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_bound : srcOff + i + n ≤ srcBytes.length)
    (h_dst_bound : dstOff + i + n ≤ dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * n + 1) (AB + 260) (AB + 288) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x30 : Reg) ↦ᵣ x30old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + n)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + n)))) **
       regOwn .x30 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + n))) := by
  have hbeq : (AB + 260 : Word) + signExtend13 (28 : BitVec 13) = AB + 288 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  induction n generalizing i x30old with
  | zero =>
    -- x6 = 0 : BEQ taken → AB+288
    have hb := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (AB + 260)
    rw [hbeq] at hb
    have hbe := cpsBranchWithin_extend_code
      (adMemF 65, (AB + 260), (.BEQ .x6 .x0 (28 : BitVec 13))) hb
    have htaken := cpsBranchWithin_takenStripPure2 hbe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x30 : Reg) ↦ᵣ x30old) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          simp only [show i + 0 = i from by omega]
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          have hq2 : (((.x6 : Reg) ↦ᵣ (0 : Word)) **
              ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
              ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
              ((.x30 : Reg) ↦ᵣ x30old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion srcBase srcBytes **
              bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
              sState := by xperm_chunked hq
          have hq3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x30)))) _ hq2
          xperm_chunked hq3) htf)
  | succ k ih =>
    -- x6 = k+1 ≠ 0 : BEQ not-taken → AB+264, then body, then IH
    have hb := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (AB + 260)
    rw [hbeq] at hb
    have hbe := cpsBranchWithin_extend_code
      (adMemF 65, (AB + 260), (.BEQ .x6 .x0 (28 : BitVec 13))) hb
    have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact adb_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x30 : Reg) ↦ᵣ x30old) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (by pcFreeR) hnt
    have hbody := adBalBody srcBase dstBase x30old srcBytes dstBytes srcOff dstOff i k
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over
      h_src_valid h_dst_valid
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega)
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hntf hbody
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show i + 1 + k = i + (k + 1) from by omega] at hq
          xperm_chunked hq) sfull)

#print axioms adBalLoop

end EvmAsm.Codegen.AccountDecodeSpec
