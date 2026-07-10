/-
  EvmAsm.Evm64.Terminating.ReturnCaptureSpec

  Support for the RETURN-only `system_call_mode` capture block in the standalone
  (`depthAware = false`) RETURN (0xf3) tail.  The existing `ReturnSpec` proves
  the ordinary `system_call_mode = 0` path.  This file proves the byte-copy loop
  used by the nonzero system-call path:

      beqz t4, nocap
      lbu  t5, 0(t2)
      sb   t5, 0(t3)
      addi t2, t2, 1
      addi t3, t3, 1
      addi t4, t4, -1
      j    loop

  Register mapping: `t2/t3/t4/t5 = x7/x28/x29/x30`.
-/

import EvmAsm.Evm64.Terminating.ReturnSpec

namespace EvmAsm.Evm64
namespace Terminating

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- `(n+1) - 1 = n` as words (capture-loop counter decrement). -/
private theorem cap_word_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem cap_word_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc
  rw [hc] at ht
  simp at ht

/-- Pointer advance by 1 byte. -/
private theorem cap_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

/-- The 7-instruction RETURN system-call capture copy loop. -/
def returnCaptureCopyLoop : Program :=
  [.BEQ .x29 .x0 (BitVec.ofNat 13 28),
   .LBU .x30 .x7 0,
   .SB .x28 .x30 0,
   .ADDI .x7 .x7 1,
   .ADDI .x28 .x28 1,
   .ADDI .x29 .x29 (-1 : BitVec 12),
   .JAL .x0 (-24 : BitVec 21)]

@[simp] theorem returnCaptureCopyLoop_length : returnCaptureCopyLoop.length = 7 := rfl

/-- **The RETURN system-call capture copy-loop closure** (`base → base+28`) by
    induction on the byte countdown `n`.  Entering with `n` bytes left and `i`
    already copied, it copies the remaining `n` bytes from `srcBase[srcOff+i..]`
    to `destBase[destOff+i..]`, advances `x7`/`x28`, and zeroes `x29`. -/
theorem returnCaptureCopyLoop_spec_within (base srcBase destBase : Word)
    (srcBytes destBytes : List (BitVec 8)) (srcOff destOff n i : Nat) (x30old : Word)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dest_align : destBase.toNat % 8 = 0)
    (h_src_bound : srcOff + i + n ≤ srcBytes.length)
    (h_dest_bound : destOff + i + n ≤ destBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dest_over : destBase.toNat + destBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dest_valid : ∀ k, k < destBytes.length →
      isValidByteAccess (destBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * n + 1) base (base + 28)
      (CodeReq.ofProg base returnCaptureCopyLoop)
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x30 : Reg) ↦ᵣ x30old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff i))
      (((.x29 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i + n))) **
       ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + i + n))) **
       regOwn .x30 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + n))) := by
  have hmono0 : ∀ a i', CodeReq.singleton base (.BEQ .x29 .x0 (BitVec.ofNat 13 28)) a = some i'
      → CodeReq.ofProg base returnCaptureCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCaptureCopyLoop 0 base
      (by decide) (by decide) (by bv_omega))
  have hmono1 : ∀ a i', CodeReq.singleton (base + 4) (.LBU .x30 .x7 0) a = some i'
      → CodeReq.ofProg base returnCaptureCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCaptureCopyLoop 1 (base + 4)
      (by decide) (by decide) (by bv_omega))
  have hmono2 : ∀ a i', CodeReq.singleton (base + 8) (.SB .x28 .x30 0) a = some i'
      → CodeReq.ofProg base returnCaptureCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCaptureCopyLoop 2 (base + 8)
      (by decide) (by decide) (by bv_omega))
  have hmono3 : ∀ a i', CodeReq.singleton (base + 12) (.ADDI .x7 .x7 1) a = some i'
      → CodeReq.ofProg base returnCaptureCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCaptureCopyLoop 3 (base + 12)
      (by decide) (by decide) (by bv_omega))
  have hmono4 : ∀ a i', CodeReq.singleton (base + 16) (.ADDI .x28 .x28 1) a = some i'
      → CodeReq.ofProg base returnCaptureCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCaptureCopyLoop 4 (base + 16)
      (by decide) (by decide) (by bv_omega))
  have hmono5 : ∀ a i', CodeReq.singleton (base + 20) (.ADDI .x29 .x29 (-1 : BitVec 12)) a = some i'
      → CodeReq.ofProg base returnCaptureCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCaptureCopyLoop 5 (base + 20)
      (by decide) (by decide) (by bv_omega))
  have hmono6 : ∀ a i', CodeReq.singleton (base + 24) (.JAL .x0 (-24 : BitVec 21)) a = some i'
      → CodeReq.ofProg base returnCaptureCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCaptureCopyLoop 6 (base + 24)
      (by decide) (by decide) (by bv_omega))
  have ha_t : base + signExtend13 (BitVec.ofNat 13 28) = base + 28 := by
    rw [show signExtend13 (BitVec.ofNat 13 28) = (28 : Word) from by decide]
  have ha_back : (base + 24) + signExtend21 (-24 : BitVec 21) = base := by
    rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]
    bv_omega
  induction n generalizing i x30old with
  | zero =>
    have hbeq := beq_spec_gen_within .x29 .x0 (BitVec.ofNat 13 28) (BitVec.ofNat 64 0)
      (0 : Word) base
    rw [ha_t] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono0 hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp h_qf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := h_qf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x30 : Reg) ↦ᵣ x30old) **
       bytesRegion srcBase srcBytes **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff i))
      (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          simp only [Nat.add_zero]
          have hq2 : (((.x30 : Reg) ↦ᵣ x30old) **
              ((.x29 : Reg) ↦ᵣ (0 : Word)) **
              ((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
              ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + i))) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion srcBase srcBytes **
              bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff i)) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x30) _ hq2
          xperm_chunked hq3) htf)
  | succ k ih =>
    have hsi : srcOff + i < srcBytes.length := by omega
    have hdi : destOff + i < destBytes.length := by omega
    set bval := srcBytes[srcOff + i]'hsi with hbval
    have htrunc : (bval.zeroExtend 64).truncate 8 = bval := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
      have := bval.isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hgetd : srcBytes.getD (srcOff + i) 0 = bval := by
      rw [hbval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsi]
      rfl
    have hstep : copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)
        = (copyIntoRegion destBytes srcBytes destOff srcOff i).set (destOff + i) bval := by
      simp only [copyIntoRegion, hgetd]
    -- Step 0: BEQ not taken (x29 = k+1 ≠ 0).
    have hbeq := beq_spec_gen_within .x29 .x0 (BitVec.ofNat 13 28) (BitVec.ofNat 64 (k + 1))
      (0 : Word) base
    rw [ha_t] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono0 hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp h_qt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := h_qt
      exact cap_word_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x30 : Reg) ↦ᵣ x30old) **
       bytesRegion srcBase srcBytes **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff i))
      (by pcFreeR) hnt
    -- Step 1: LBU x30 ← src[srcOff+i].
    have hlbu := bytesRegion_lbu_within .x30 .x7 srcBase x30old (base + 4)
      srcBytes (srcOff + i) (by decide) h_src_align hsi (by omega)
      (h_src_valid (srcOff + i) hsi)
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega, ← hbval] at hlbu
    have hlbue := cpsTripleWithin_extend_code hmono1 hlbu
    have hlbuf := cpsTripleWithin_frameR
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff i))
      (by pcFreeR) hlbue
    -- Step 2: SB dest[destOff+i] ← x30 (= bval).
    have hsb := bytesRegion_sb_within .x28 .x30 destBase (bval.zeroExtend 64) (base + 8)
      (copyIntoRegion destBytes srcBytes destOff srcOff i) (destOff + i) h_dest_align
      (by rw [copyIntoRegion_length]; omega) (by omega)
      (h_dest_valid (destOff + i) hdi)
    rw [htrunc, ← hstep, show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hsb
    have hsbe := cpsTripleWithin_extend_code hmono2 hsb
    have hsbf := cpsTripleWithin_frameR
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      (by pcFreeR) hsbe
    -- Step 3: ADDI x7 += 1.
    have h3 := addi_spec_gen_same_within .x7
      (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (base + 12) (by decide)
    rw [cap_advance srcBase (srcOff + i),
        show srcOff + i + 1 = srcOff + (i + 1) from by omega,
        show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at h3
    have h3e := cpsTripleWithin_extend_code hmono3 h3
    have h3f := cpsTripleWithin_frameR
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)))
      (by pcFreeR) h3e
    -- Step 4: ADDI x28 += 1.
    have h4 := addi_spec_gen_same_within .x28
      (destBase + BitVec.ofNat 64 (destOff + i)) (1 : BitVec 12) (base + 16) (by decide)
    rw [cap_advance destBase (destOff + i),
        show destOff + i + 1 = destOff + (i + 1) from by omega,
        show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at h4
    have h4e := cpsTripleWithin_extend_code hmono4 h4
    have h4f := cpsTripleWithin_frameR
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)))
      (by pcFreeR) h4e
    -- Step 5: ADDI x29 -= 1.
    have h5 := addi_spec_gen_same_within .x29 (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12)
      (base + 20) (by decide)
    rw [cap_word_succ_dec k, show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at h5
    have h5e := cpsTripleWithin_extend_code hmono5 h5
    have h5f := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)))
      (by pcFreeR) h5e
    -- Step 6: JAL back to base.
    have h6 := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 24)
    rw [ha_back] at h6
    have h6e := cpsTripleWithin_extend_code hmono6 h6
    have h6f := cpsTripleWithin_frameR
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
       ((.x7 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x28 : Reg) ↦ᵣ (destBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       ((.x30 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion destBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)))
      (by pcFreeR) h6e
    have hih := ih (i + 1) (bval.zeroExtend 64)
      (by rw [show srcOff + (i + 1) + k = srcOff + i + (k + 1) from by omega]; exact h_src_bound)
      (by rw [show destOff + (i + 1) + k = destOff + i + (k + 1) from by omega]; exact h_dest_bound)
    -- Compose.
    have s01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hlbuf
    have s012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s01 hsbf
    have s0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s012 h3f
    have s01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s0123 h4f
    have s012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s01234 h5f
    have s0_6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left']
      xperm_chunked hp) s012345 h6f
    have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left'] at hp
      xperm_chunked hp) s0_6 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show srcOff + (i + 1) + k = srcOff + i + (k + 1) from by omega,
                     show destOff + (i + 1) + k = destOff + i + (k + 1) from by omega,
                     show i + 1 + k = i + (k + 1) from by omega] at hq
          xperm_chunked hq) sfull)

def returnCaptureLenPost (scmVal size lenOld : Word) : Word :=
  if scmVal = (0 : Word) then lenOld else if BitVec.ult (4096 : Word) size then lenOld else size

def returnCaptureRdPost (scmVal size : Word) (rdBytes memBytes : List (BitVec 8)) (off : Word) :
    List (BitVec 8) :=
  if scmVal = (0 : Word) then rdBytes
  else if BitVec.ult (4096 : Word) size then rdBytes
  else copyIntoRegion rdBytes memBytes 0 off.toNat size.toNat

def returnCaptureX7Post (scmVal size evmMemBase off x7o : Word) : Word :=
  if scmVal = (0 : Word) then x7o
  else if BitVec.ult (4096 : Word) size then x7o
  else evmMemBase + BitVec.ofNat 64 (off.toNat + size.toNat)

def returnCaptureX28Post (scmVal size rdBase x28o : Word) : Word :=
  if scmVal = (0 : Word) then x28o
  else if BitVec.ult (4096 : Word) size then x28o
  else rdBase + BitVec.ofNat 64 size.toNat

def returnCaptureX29Post (scmVal size x29o : Word) : Word :=
  if scmVal = (0 : Word) then x29o
  else if BitVec.ult (4096 : Word) size then x29o
  else 0

def returnCaptureX30Post (scmVal size x30o : Word) : Assertion :=
  if scmVal = (0 : Word) then ((.x30 : Reg) ↦ᵣ x30o)
  else if BitVec.ult (4096 : Word) size then ((.x30 : Reg) ↦ᵣ x30o)
  else regOwn .x30

/-! ## Capture-block segments embedded in `returnTailProg` -/

section Compose

variable (hiSCM : BitVec 20) (loSCM : BitVec 12) (hiLen : BitVec 20) (loLen : BitVec 12)
  (hiRd : BitVec 20) (loRd : BitVec 12) (hiMem : BitVec 20) (loMem : BitVec 12)
  (hiMem2 : BitVec 20) (loMem2 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
  (hi1 : BitVec 20) (lo1 : BitVec 12)

local notation "PROG" =>
  returnTailProg hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1

local notation "TAILCR" hbase => CodeReq.ofProg hbase PROG

/-- **RETURN prologue through `system_call_mode` load** (`hbase → hbase+20`).
    Reads `offset`/`size`, reconstructs the `system_call_mode` address, and
    loads its current value into `x5`. -/
theorem return_seg_load_scm (hbase p scmAddr off size scmVal x14o x15o x5o : Word)
    (hlaSCM : (hbase + (8 : Word)) + ((hiSCM.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loSCM = scmAddr) :
    cpsTripleWithin 5 hbase (hbase + 20)
      (TAILCR hbase)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p) ** (.x14 ↦ᵣ x14o) ** (.x15 ↦ᵣ x15o) **
        (.x5 ↦ᵣ x5o) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p) ** (.x14 ↦ᵣ off) ** (.x15 ↦ᵣ size) **
        (.x5 ↦ᵣ scmVal) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal)) := by
  -- idx 0: ld x14, 0(x12)
  have t0 := ld_spec_within .x14 .x12 p x14o off 0 hbase (by nofun)
  have t0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 0 hbase
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t0
  have t0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x15 : Reg) ↦ᵣ x15o) ** ((.x5 : Reg) ↦ᵣ x5o) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal))
    (by pcFree) t0e
  -- idx 1: ld x15, 32(x12)
  have t1 := ld_spec_within .x15 .x12 p x15o size 32 (hbase + 4) (by nofun)
  rw [show (hbase + 4 : Word) + 4 = hbase + 8 from by bv_omega] at t1
  have t1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 1 (hbase + 4)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t1
  have t1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x5 : Reg) ↦ᵣ x5o) **
      ((p + signExtend12 0) ↦ₘ off) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal))
    (by pcFree) t1e
  -- idx 2: auipc x5, hiSCM
  have t2 := auipc_spec_within .x5 x5o hiSCM (hbase + 8) (by nofun)
  rw [show (hbase + 8 : Word) + 4 = hbase + 12 from by bv_omega] at t2
  set scmAuipc := (hbase + (8 : Word)) + ((hiSCM.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    with hAuipc
  have t2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 2 (hbase + 8)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t2
  have t2f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ scmVal))
    (by pcFree) t2e
  -- idx 3: addi x5, x5, loSCM
  have t3 := addi_spec_same_within .x5 scmAuipc loSCM (hbase + 12) (by nofun)
  rw [hlaSCM, show (hbase + 12 : Word) + 4 = hbase + 16 from by bv_omega] at t3
  have t3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 3 (hbase + 12)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t3
  have t3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ scmVal))
    (by pcFree) t3e
  -- idx 4: ld x5, 0(x5)
  have t4 := ld_spec_same_within .x5 scmAddr scmVal 0 (hbase + 16) (by nofun)
  rw [show (hbase + 16 : Word) + 4 = hbase + 20 from by bv_omega] at t4
  have t4e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 4 (hbase + 16)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t4
  have t4f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size))
    (by pcFree) t4e
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) t0f t1f
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 t2f
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 t3f
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123 t4f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c01234)

/-- **RETURN nonzero-system-call oversized capture skip** (`hbase → hbase+88`).
    With `system_call_mode ≠ 0` and `4096 < size`, the capture guard falls
    through, the oversized guard branches to `.Lrr_nocap`, and the descriptor
    path begins without touching `system_call_returndata_len` or the returndata
    buffer. -/
theorem return_seg_capture_oversize (hbase p scmAddr off size scmVal x14o x15o x5o x6o : Word)
    (h_scm_ne : scmVal ≠ (0 : Word))
    (h_oversize : BitVec.ult (4096 : Word) size)
    (hlaSCM : (hbase + (8 : Word)) + ((hiSCM.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loSCM = scmAddr) :
    cpsTripleWithin 8 hbase (hbase + 88)
      (TAILCR hbase)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p) ** (.x14 ↦ᵣ x14o) ** (.x15 ↦ᵣ x15o) **
        (.x5 ↦ᵣ x5o) ** (.x6 ↦ᵣ x6o) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p) ** (.x14 ↦ᵣ off) ** (.x15 ↦ᵣ size) **
        (.x5 ↦ᵣ scmVal) ** (.x6 ↦ᵣ (4096 : Word)) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal)) := by
  have pre := return_seg_load_scm hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase p scmAddr off size scmVal x14o x15o x5o hlaSCM
  have pref := cpsTripleWithin_frameR ((.x6 : Reg) ↦ᵣ x6o) (by pcFree) pre
  -- idx 5: beqz x5, nocap.  Since scmVal ≠ 0, it falls through.
  have b0 := beq_spec_gen_within .x5 .x0 (BitVec.ofNat 13 68) scmVal (0 : Word) (hbase + 20)
  rw [show (hbase + 20 : Word) + signExtend13 (BitVec.ofNat 13 68) = hbase + 88 from by
        rw [show signExtend13 (BitVec.ofNat 13 68) = (68 : Word) from by decide]; bv_omega,
      show (hbase + 20 : Word) + 4 = hbase + 24 from by bv_omega] at b0
  have b0e := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 5 (hbase + 20)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) b0
  have b0nt := cpsBranchWithin_ntakenStripPure2 b0e (fun hp h_qt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := h_qt
    exact h_scm_ne ((sepConj_pure_right _).1 hQ).2)
  have b0f := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x6 : Reg) ↦ᵣ x6o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal))
    (by pcFree) b0nt
  -- idx 6: li x6, 4096
  have s1 := li_spec_within .x6 x6o (4096 : Word) (hbase + 24) (by nofun)
  rw [show (hbase + 24 : Word) + 4 = hbase + 28 from by bv_omega] at s1
  have s1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 6 (hbase + 24)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s1
  have s1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) ** ((.x5 : Reg) ↦ᵣ scmVal) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal))
    (by pcFree) s1e
  -- idx 7: bltu x6, x15, nocap.  Since 4096 < size, it branches to hbase+88.
  have b1 := bltu_spec_gen_within .x6 .x15 (BitVec.ofNat 13 60) (4096 : Word) size (hbase + 28)
  rw [show (hbase + 28 : Word) + signExtend13 (BitVec.ofNat 13 60) = hbase + 88 from by
        rw [show signExtend13 (BitVec.ofNat 13 60) = (60 : Word) from by decide]; bv_omega,
      show (hbase + 28 : Word) + 4 = hbase + 32 from by bv_omega] at b1
  have b1e := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 7 (hbase + 28)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) b1
  have b1t := cpsBranchWithin_takenStripPure2 b1e (fun hp h_qf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := h_qf
    exact ((sepConj_pure_right _).1 hQ).2 h_oversize)
  have b1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x5 : Reg) ↦ᵣ scmVal) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ scmVal))
    (by pcFree) b1t
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pref b0f
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 s1f
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 b1f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c2)

/-- **RETURN nonzero-system-call capture path** (`hbase → hbase+88`).  With
    `system_call_mode ≠ 0` and `size ≤ 4096`, the capture block stores
    `system_call_returndata_len := size`, copies `evm_memory[offset..offset+size)`
    into `system_call_returndata[0..size)`, and then joins the ordinary
    descriptor-building path at `.Lrr_nocap`. -/
theorem return_seg_capture_small
    (hbase p scmAddr lenAddr rdBase evmMemBase off size scmVal
      x14o x15o x5o x6o x7o x28o x29o x30o lenOld : Word)
    (memBytes rdBytes : List (BitVec 8))
    (h_scm_ne : scmVal ≠ (0 : Word))
    (h_not_oversize : ¬ BitVec.ult (4096 : Word) size)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hRdAlign : rdBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hRdOver : rdBase.toNat + rdBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hRdValid : ∀ k, k < rdBytes.length →
      isValidByteAccess (rdBase + BitVec.ofNat 64 k) = true)
    (hOffFull : off.toNat + size.toNat ≤ memBytes.length)
    (hRdBound : size.toNat ≤ rdBytes.length)
    (hlaSCM : (hbase + (8 : Word)) + ((hiSCM.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loSCM = scmAddr)
    (hlaLen : (hbase + (32 : Word)) + ((hiLen.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loLen = lenAddr)
    (hlaRd : (hbase + (48 : Word)) + ((hiRd.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loRd = rdBase) :
    cpsTripleWithin (16 + 7 * size.toNat) hbase (hbase + 88)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) **
        ((.x13 : Reg) ↦ᵣ evmMemBase) ** ((.x14 : Reg) ↦ᵣ x14o) **
        ((.x15 : Reg) ↦ᵣ x15o) ** ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) **
        ((.x7 : Reg) ↦ᵣ x7o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
        ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
        ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
        bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) **
        ((.x13 : Reg) ↦ᵣ evmMemBase) ** ((.x14 : Reg) ↦ᵣ off) **
        ((.x15 : Reg) ↦ᵣ size) ** ((.x5 : Reg) ↦ᵣ scmVal) ** ((.x6 : Reg) ↦ᵣ lenAddr) **
        ((.x7 : Reg) ↦ᵣ (evmMemBase + BitVec.ofNat 64 (off.toNat + size.toNat))) **
        ((.x28 : Reg) ↦ᵣ (rdBase + BitVec.ofNat 64 size.toNat)) **
        ((.x29 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
        ((lenAddr + signExtend12 0) ↦ₘ size) **
        bytesRegion evmMemBase memBytes **
        bytesRegion rdBase (copyIntoRegion rdBytes memBytes 0 off.toNat size.toNat)) := by
  have pre := return_seg_load_scm hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase p scmAddr off size scmVal x14o x15o x5o hlaSCM
  have pref := cpsTripleWithin_frameR
    (((.x13 : Reg) ↦ᵣ evmMemBase) ** ((.x6 : Reg) ↦ᵣ x6o) ** ((.x7 : Reg) ↦ᵣ x7o) **
      ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) **
      ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) pre
  -- idx 5: beqz x5, nocap.  Since scmVal ≠ 0, it falls through.
  have b0 := beq_spec_gen_within .x5 .x0 (BitVec.ofNat 13 68) scmVal (0 : Word) (hbase + 20)
  rw [show (hbase + 20 : Word) + signExtend13 (BitVec.ofNat 13 68) = hbase + 88 from by
        rw [show signExtend13 (BitVec.ofNat 13 68) = (68 : Word) from by decide]; bv_omega,
      show (hbase + 20 : Word) + 4 = hbase + 24 from by bv_omega] at b0
  have b0e := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 5 (hbase + 20)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) b0
  have b0nt := cpsBranchWithin_ntakenStripPure2 b0e (fun hp h_qt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := h_qt
    exact h_scm_ne ((sepConj_pure_right _).1 hQ).2)
  have b0f := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) ** ((.x6 : Reg) ↦ᵣ x6o) ** ((.x7 : Reg) ↦ᵣ x7o) **
      ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ scmVal) ** ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) b0nt
  -- idx 6: li x6, 4096
  have s1 := li_spec_within .x6 x6o (4096 : Word) (hbase + 24) (by nofun)
  rw [show (hbase + 24 : Word) + 4 = hbase + 28 from by bv_omega] at s1
  have s1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 6 (hbase + 24)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s1
  have s1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
      ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) ** ((.x5 : Reg) ↦ᵣ scmVal) **
      ((.x7 : Reg) ↦ᵣ x7o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
      ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
      ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) s1e
  -- idx 7: bltu x6, x15, nocap.  Since size ≤ 4096, it falls through.
  have b1 := bltu_spec_gen_within .x6 .x15 (BitVec.ofNat 13 60) (4096 : Word) size (hbase + 28)
  rw [show (hbase + 28 : Word) + signExtend13 (BitVec.ofNat 13 60) = hbase + 88 from by
        rw [show signExtend13 (BitVec.ofNat 13 60) = (60 : Word) from by decide]; bv_omega,
      show (hbase + 28 : Word) + 4 = hbase + 32 from by bv_omega] at b1
  have b1e := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 7 (hbase + 28)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) b1
  have b1nt := cpsBranchWithin_ntakenStripPure2 b1e (fun hp h_qt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := h_qt
    exact h_not_oversize ((sepConj_pure_right _).1 hQ).2)
  have b1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
      ((.x14 : Reg) ↦ᵣ off) ** ((.x5 : Reg) ↦ᵣ scmVal) ** ((.x7 : Reg) ↦ᵣ x7o) **
      ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ scmVal) ** ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) b1nt
  -- idx 8: auipc x6, hiLen
  have a0 := auipc_spec_within .x6 (4096 : Word) hiLen (hbase + 32) (by nofun)
  rw [show (hbase + 32 : Word) + 4 = hbase + 36 from by bv_omega] at a0
  set lenAuipc := (hbase + (32 : Word)) + ((hiLen.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    with hLenAuipc
  have a0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 8 (hbase + 32)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a0
  have a0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
      ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) ** ((.x5 : Reg) ↦ᵣ scmVal) **
      ((.x7 : Reg) ↦ᵣ x7o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
      ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
      ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) a0e
  -- idx 9: addi x6, x6, loLen
  have a1 := addi_spec_same_within .x6 lenAuipc loLen (hbase + 36) (by nofun)
  rw [hlaLen, show (hbase + 36 : Word) + 4 = hbase + 40 from by bv_omega] at a1
  have a1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 9 (hbase + 36)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a1
  have a1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
      ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) ** ((.x5 : Reg) ↦ᵣ scmVal) **
      ((.x7 : Reg) ↦ᵣ x7o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
      ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
      ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) a1e
  -- idx 10: sd x15, 0(x6)  (system_call_returndata_len := size)
  have a2 := sd_spec_within .x6 .x15 lenAddr size lenOld 0 (hbase + 40)
  rw [show (hbase + 40 : Word) + 4 = hbase + 44 from by bv_omega] at a2
  have a2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 10 (hbase + 40)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a2
  have a2f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
      ((.x14 : Reg) ↦ᵣ off) ** ((.x5 : Reg) ↦ᵣ scmVal) ** ((.x7 : Reg) ↦ᵣ x7o) **
      ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) a2e
  -- idx 11: add x7, x13, x14
  have a3 := add_spec_within .x7 .x13 .x14 evmMemBase off x7o (hbase + 44) (by nofun)
  rw [show (hbase + 44 : Word) + 4 = hbase + 48 from by bv_omega] at a3
  have a3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 11 (hbase + 44)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a3
  have a3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x5 : Reg) ↦ᵣ scmVal) ** ((.x6 : Reg) ↦ᵣ lenAddr) ** ((.x28 : Reg) ↦ᵣ x28o) **
      ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
      ((lenAddr + signExtend12 0) ↦ₘ size) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) a3e
  -- idx 12: auipc x28, hiRd
  have a4 := auipc_spec_within .x28 x28o hiRd (hbase + 48) (by nofun)
  rw [show (hbase + 48 : Word) + 4 = hbase + 52 from by bv_omega] at a4
  set rdAuipc := (hbase + (48 : Word)) + ((hiRd.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    with hRdAuipc
  have a4e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 12 (hbase + 48)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a4
  have a4f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
      ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) ** ((.x5 : Reg) ↦ᵣ scmVal) **
      ((.x6 : Reg) ↦ᵣ lenAddr) ** ((.x7 : Reg) ↦ᵣ (evmMemBase + off)) **
      ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
      ((lenAddr + signExtend12 0) ↦ₘ size) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) a4e
  -- idx 13: addi x28, x28, loRd
  have a5 := addi_spec_same_within .x28 rdAuipc loRd (hbase + 52) (by nofun)
  rw [hlaRd, show (hbase + 52 : Word) + 4 = hbase + 56 from by bv_omega] at a5
  have a5e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 13 (hbase + 52)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a5
  have a5f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
      ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) ** ((.x5 : Reg) ↦ᵣ scmVal) **
      ((.x6 : Reg) ↦ᵣ lenAddr) ** ((.x7 : Reg) ↦ᵣ (evmMemBase + off)) **
      ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
      ((lenAddr + signExtend12 0) ↦ₘ size) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) a5e
  -- idx 14: mv x29, x15
  have a6 := mv_spec_within .x29 .x15 size x29o (hbase + 56) (by nofun)
  rw [show (hbase + 56 : Word) + 4 = hbase + 60 from by bv_omega] at a6
  have a6e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 14 (hbase + 56)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a6
  have a6f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
      ((.x14 : Reg) ↦ᵣ off) ** ((.x5 : Reg) ↦ᵣ scmVal) ** ((.x6 : Reg) ↦ᵣ lenAddr) **
      ((.x7 : Reg) ↦ᵣ (evmMemBase + off)) ** ((.x28 : Reg) ↦ᵣ rdBase) **
      ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
      ((lenAddr + signExtend12 0) ↦ₘ size) **
      bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) a6e
  -- idx 15..21: capture copy loop
  have hloop := returnCaptureCopyLoop_spec_within (hbase + 60) evmMemBase rdBase memBytes
    rdBytes off.toNat 0 size.toNat 0 x30o hSrcAlign hRdAlign (by simpa using hOffFull)
    (by simpa using hRdBound) hSrcOver hRdOver hSrcValid hRdValid
  rw [show copyIntoRegion rdBytes memBytes 0 off.toNat 0 = rdBytes from rfl,
      show BitVec.ofNat 64 size.toNat = size from word_ofNat_toNat _,
      show evmMemBase + BitVec.ofNat 64 (off.toNat + 0) = evmMemBase + off from by
        rw [Nat.add_zero, word_ofNat_toNat],
      show rdBase + BitVec.ofNat 64 (0 + 0) = rdBase from by
        rw [show BitVec.ofNat 64 (0 + 0) = (0 : Word) from by decide]
        bv_omega,
      show 0 + size.toNat = size.toNat from Nat.zero_add _,
      show (hbase + 60 : Word) + 28 = hbase + 88 from by bv_omega] at hloop
  have hloopE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 60) PROG returnCaptureCopyLoop 15
      (by bv_omega) (by rfl)
      (by simp only [returnTailProg_length, returnCaptureCopyLoop_length]; omega)
      (by simp only [returnTailProg_length]; decide)) hloop
  have hloopf := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) ** ((.x5 : Reg) ↦ᵣ scmVal) ** ((.x6 : Reg) ↦ᵣ lenAddr) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ scmVal) ** ((lenAddr + signExtend12 0) ↦ₘ size))
    (by pcFreeR) hloopE
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) pref b0f
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 s1f
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 b1f
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 a0f
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 a1f
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c4 a2f
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c5 a3f
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c6 a4f
  have c8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c7 a5f
  have c9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c8 a6f
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c9 hloopf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by
      rw [show off.toNat + 0 + size.toNat = off.toNat + size.toNat from by omega] at hq
      xperm_chunked hq) c10)

/-- **Shared RETURN tail after `.Lrr_nocap`** (`hbase+88 → halt`).  This is the
    descriptor-building and `dispatchHaltRet 2` suffix factored out so the
    ordinary skip path, oversized system-call skip path, and small capture path
    can share the same proof. -/
theorem return_seg_nocap_rest
    (hbase p evmMemBase flag resume : Word)
    (off size x1o x5v x6v x16o x17o x19o x21o x22o x23o f0 : Word)
    (descInit memBytes : List (BitVec 8))
    (hDescLen : descInit.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hOff : off.toNat + (returnClamp size).toNat ≤ memBytes.length)
    (hOff32 : off.toNat + (returnClamp32 size).toNat ≤ memBytes.length)
    (hlaMem : (hbase + (160 : Word)) + ((hiMem.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem = evmMemBase)
    (hlaMem2 : (hbase + (208 : Word)) + ((hiMem2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem2 = evmMemBase)
    (hla2 : (hbase + 276 + 4) + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla1 : (hbase + 276 + 16) + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = resume) :
    cpsTripleWithin (148 + 7 * (returnClamp size).toNat + 7 * (returnClamp32 size).toNat)
      (hbase + 88) (resume &&& ~~~1)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5v) **
        ((.x6 : Reg) ↦ᵣ x6v) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
        ((.x15 : Reg) ↦ᵣ size) ** ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o) **
        ((.x23 : Reg) ↦ᵣ x23o) ** (flag ↦ₘ f0) **
        bytesRegion returnDescBase descInit ** bytesRegion evmMemBase memBytes)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ resume) ** ((.x5 : Reg) ↦ᵣ (2 : Word)) **
        ((.x6 : Reg) ↦ᵣ flag) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
        ((.x15 : Reg) ↦ᵣ size) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ (1 : Word)) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 size).toNat)) **
        ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
        (flag ↦ₘ (2 : Word)) **
        bytesRegion returnDescBase
          (setBytes
            (copyIntoRegion
              (copyIntoRegion
                (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
                  (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
              memBytes 0 off.toNat (returnClamp32 size).toNat) 32 (dwordBytes (1 : Word))) **
        bytesRegion evmMemBase memBytes) := by
  have h_rc1_len : (copyIntoRegion
      (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
        (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat).length = 256 := by
    simp only [copyIntoRegion_length, length_setBytes, returnDescZeroed, zeroDwords_length, hDescLen]
  have h_rc2_len : (copyIntoRegion
      (copyIntoRegion
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
          (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
      memBytes 0 off.toNat (returnClamp32 size).toNat).length = 256 := by
    simp only [copyIntoRegion_length, length_setBytes, returnDescZeroed, zeroDwords_length, hDescLen]
  have S2 := return_seg_header hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase x16o x19o x21o descInit hDescLen
  have S2f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5v) ** ((.x6 : Reg) ↦ᵣ x6v) **
      ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x17 : Reg) ↦ᵣ x17o) ** ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
      (flag ↦ₘ f0) ** bytesRegion evmMemBase memBytes) (by pcFreeR) S2
  have S3 := return_seg_clamp176 hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase size (0 : Word) x22o
  have S3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5v) **
      ((.x6 : Reg) ↦ᵣ x6v) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ x17o) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0 + 22)))) **
      ((.x23 : Reg) ↦ᵣ x23o) ** (flag ↦ₘ f0) **
      bytesRegion returnDescBase (returnDescZeroed descInit) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S3
  have S4 := return_seg_copy1 hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase evmMemBase off size x17o
    (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0 + 22))) (176 : Word) x23o descInit memBytes
    hDescLen hSrcAlign hSrcOver hSrcValid hOff hlaMem
  have S4f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5v) ** ((.x6 : Reg) ↦ᵣ x6v) **
      ((.x12 : Reg) ↦ᵣ p) ** (flag ↦ₘ f0)) (by pcFreeR) S4
  have S5 := return_seg_clamp32 hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase evmMemBase off size
    (evmMemBase + BitVec.ofNat 64 (off.toNat + 0 + (returnClamp size).toNat))
    (returnClamp size) (0 : Word) hlaMem2
  have S5f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5v) **
      ((.x6 : Reg) ↦ᵣ x6v) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (72 + 0 + (returnClamp size).toNat))) **
      regOwn .x23 ** (flag ↦ₘ f0) **
      bytesRegion returnDescBase
        (copyIntoRegion
          (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
            (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S5
  have S6 := return_seg_copy2 hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase evmMemBase off size
    (returnDescBase + BitVec.ofNat 64 (72 + 0 + (returnClamp size).toNat))
    (copyIntoRegion
      (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
        (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
    memBytes h_rc1_len hSrcAlign hSrcOver hSrcValid hOff32
  have S6f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5v) ** ((.x6 : Reg) ↦ᵣ x6v) **
      ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x21 : Reg) ↦ᵣ (32 : Word)) ** (flag ↦ₘ f0)) (by pcFreeR) S6
  have S7 := return_seg_kindhalt hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase flag resume
    (evmMemBase + BitVec.ofNat 64 (off.toNat + 0 + (returnClamp32 size).toNat))
    x5v x6v x1o f0
    (copyIntoRegion
      (copyIntoRegion
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
          (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
      memBytes 0 off.toNat (returnClamp32 size).toNat) h_rc2_len hla2 hla1
  have S7f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 size).toNat)) **
      ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S7
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) S2f S3f
  have c13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c12 S4f
  have c14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c13 S5f
  have c15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c14 S6f
  have c16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c15 S7f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c16)

/-- **Upgraded RETURN (0xf3) return-data window + halt core, including the
    `system_call_mode` capture block.**  This theorem covers all three front
    paths before the shared descriptor/halt suffix:

    * `system_call_mode = 0`: ordinary transactions skip the capture block.
    * `system_call_mode ≠ 0 ∧ size > 4096`: oversized system-call returns skip
      capture conservatively.
    * `system_call_mode ≠ 0 ∧ size ≤ 4096`: store
      `system_call_returndata_len := size` and copy the whole return window into
      `system_call_returndata` before building the normal RETURN descriptor.

    It is still stated from the post-memory-gas entry.  The source/destination
    bounds needed by the small capture copy are therefore static hypotheses,
    conditional on the copy branch being taken. -/
theorem evm_return_stack_spec_within_with_capture
    (hbase p scmAddr lenAddr rdBase evmMemBase flag resume : Word)
    (off size scmVal x1o x5o x6o x7o x14o x15o x16o x17o x19o x21o x22o x23o
      x28o x29o x30o f0 lenOld : Word)
    (descInit memBytes rdBytes : List (BitVec 8))
    (hDescLen : descInit.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hRdAlign : rdBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hRdOver : rdBase.toNat + rdBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hRdValid : ∀ k, k < rdBytes.length →
      isValidByteAccess (rdBase + BitVec.ofNat 64 k) = true)
    (hOff : off.toNat + (returnClamp size).toNat ≤ memBytes.length)
    (hOff32 : off.toNat + (returnClamp32 size).toNat ≤ memBytes.length)
    (hOffCapture : scmVal ≠ (0 : Word) → ¬ BitVec.ult (4096 : Word) size →
      off.toNat + size.toNat ≤ memBytes.length)
    (hRdCapture : scmVal ≠ (0 : Word) → ¬ BitVec.ult (4096 : Word) size →
      size.toNat ≤ rdBytes.length)
    (hlaSCM : (hbase + (8 : Word)) + ((hiSCM.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loSCM = scmAddr)
    (hlaLen : (hbase + (32 : Word)) + ((hiLen.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loLen = lenAddr)
    (hlaRd : (hbase + (48 : Word)) + ((hiRd.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loRd = rdBase)
    (hlaMem : (hbase + (160 : Word)) + ((hiMem.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem = evmMemBase)
    (hlaMem2 : (hbase + (208 : Word)) + ((hiMem2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem2 = evmMemBase)
    (hla2 : (hbase + 276 + 4) + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla1 : (hbase + 276 + 16) + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = resume) :
    cpsTripleWithin
      (164 + 7 * size.toNat + 7 * (returnClamp size).toNat + 7 * (returnClamp32 size).toNat)
      hbase (resume &&& ~~~1)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) **
        ((.x6 : Reg) ↦ᵣ x6o) ** ((.x7 : Reg) ↦ᵣ x7o) ** ((.x12 : Reg) ↦ᵣ p) **
        ((.x13 : Reg) ↦ᵣ evmMemBase) ** ((.x14 : Reg) ↦ᵣ x14o) **
        ((.x15 : Reg) ↦ᵣ x15o) ** ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o) **
        ((.x23 : Reg) ↦ᵣ x23o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
        ((.x30 : Reg) ↦ᵣ x30o) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
        ((lenAddr + signExtend12 0) ↦ₘ lenOld) ** (flag ↦ₘ f0) **
        bytesRegion returnDescBase descInit ** bytesRegion evmMemBase memBytes **
        bytesRegion rdBase rdBytes)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ resume) ** ((.x5 : Reg) ↦ᵣ (2 : Word)) **
        ((.x6 : Reg) ↦ᵣ flag) **
        ((.x7 : Reg) ↦ᵣ returnCaptureX7Post scmVal size evmMemBase off x7o) **
        ((.x12 : Reg) ↦ᵣ p) ** ((.x13 : Reg) ↦ᵣ evmMemBase) ** ((.x14 : Reg) ↦ᵣ off) **
        ((.x15 : Reg) ↦ᵣ size) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ (1 : Word)) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 size).toNat)) **
        ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
        ((.x28 : Reg) ↦ᵣ returnCaptureX28Post scmVal size rdBase x28o) **
        ((.x29 : Reg) ↦ᵣ returnCaptureX29Post scmVal size x29o) **
        returnCaptureX30Post scmVal size x30o **
        ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
        ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
        ((lenAddr + signExtend12 0) ↦ₘ returnCaptureLenPost scmVal size lenOld) **
        (flag ↦ₘ (2 : Word)) **
        bytesRegion returnDescBase
          (setBytes
            (copyIntoRegion
              (copyIntoRegion
                (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
                  (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
              memBytes 0 off.toNat (returnClamp32 size).toNat) 32 (dwordBytes (1 : Word))) **
        bytesRegion evmMemBase memBytes **
        bytesRegion rdBase (returnCaptureRdPost scmVal size rdBytes memBytes off)) := by
  by_cases h_scm_zero : scmVal = (0 : Word)
  · subst scmVal
    have S1 := return_seg_prologue hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
      hi2 lo2 hi1 lo1 hbase p scmAddr off size x14o x15o x5o hlaSCM
    have S1f := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ x1o) ** ((.x6 : Reg) ↦ᵣ x6o) ** ((.x7 : Reg) ↦ᵣ x7o) **
        ((.x13 : Reg) ↦ᵣ evmMemBase) ** ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o) **
        ((.x23 : Reg) ↦ᵣ x23o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
        ((.x30 : Reg) ↦ᵣ x30o) ** ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
        (flag ↦ₘ f0) ** bytesRegion returnDescBase descInit **
        bytesRegion evmMemBase memBytes ** bytesRegion rdBase rdBytes) (by pcFreeR) S1
    have Rest := return_seg_nocap_rest hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
      hi2 lo2 hi1 lo1 hbase p evmMemBase flag resume off size x1o (0 : Word) x6o
      x16o x17o x19o x21o x22o x23o f0 descInit memBytes
      hDescLen hSrcAlign hSrcOver hSrcValid hOff hOff32 hlaMem hlaMem2 hla2 hla1
    have Restf := cpsTripleWithin_frameR
      (((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
        ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) **
        ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
        ((.x7 : Reg) ↦ᵣ x7o) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
        ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) **
        bytesRegion rdBase rdBytes) (by pcFreeR) Rest
    have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) S1f Restf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by
        simp only [returnCaptureX7Post, returnCaptureX28Post, returnCaptureX29Post,
          returnCaptureX30Post, returnCaptureLenPost, returnCaptureRdPost, if_true]
        xperm_chunked hq) c)
  · by_cases h_oversize : BitVec.ult (4096 : Word) size
    · have S1 := return_seg_capture_oversize hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem
        hiMem2 loMem2 hi2 lo2 hi1 lo1 hbase p scmAddr off size scmVal x14o x15o x5o x6o
        h_scm_zero h_oversize hlaSCM
      have S1f := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ x1o) ** ((.x7 : Reg) ↦ᵣ x7o) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
          ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) ** ((.x19 : Reg) ↦ᵣ x19o) **
          ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
          ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) **
          ((lenAddr + signExtend12 0) ↦ₘ lenOld) ** (flag ↦ₘ f0) **
          bytesRegion returnDescBase descInit ** bytesRegion evmMemBase memBytes **
          bytesRegion rdBase rdBytes) (by pcFreeR) S1
      have Rest := return_seg_nocap_rest hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
        hi2 lo2 hi1 lo1 hbase p evmMemBase flag resume off size x1o scmVal (4096 : Word)
        x16o x17o x19o x21o x22o x23o f0 descInit memBytes
        hDescLen hSrcAlign hSrcOver hSrcValid hOff hOff32 hlaMem hlaMem2 hla2 hla1
      have Restf := cpsTripleWithin_frameR
        (((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
          ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
          ((lenAddr + signExtend12 0) ↦ₘ lenOld) **
          ((.x7 : Reg) ↦ᵣ x7o) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
          ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) ** ((.x30 : Reg) ↦ᵣ x30o) **
          bytesRegion rdBase rdBytes) (by pcFreeR) Rest
      have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) S1f Restf
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by
          simp only [returnCaptureX7Post, returnCaptureX28Post, returnCaptureX29Post,
            returnCaptureX30Post, returnCaptureLenPost, returnCaptureRdPost,
            if_neg h_scm_zero, if_pos h_oversize]
          xperm_chunked hq) c)
    · have S1 := return_seg_capture_small hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem
        hiMem2 loMem2 hi2 lo2 hi1 lo1 hbase p scmAddr lenAddr rdBase evmMemBase off size
        scmVal x14o x15o x5o x6o x7o x28o x29o x30o lenOld memBytes rdBytes
        h_scm_zero h_oversize hSrcAlign hRdAlign hSrcOver hRdOver hSrcValid hRdValid
        (hOffCapture h_scm_zero h_oversize) (hRdCapture h_scm_zero h_oversize)
        hlaSCM hlaLen hlaRd
      have S1f := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ x1o) ** ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) **
          ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o) **
          ((.x23 : Reg) ↦ᵣ x23o) ** (flag ↦ₘ f0) **
          bytesRegion returnDescBase descInit) (by pcFreeR) S1
      have Rest := return_seg_nocap_rest hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
        hi2 lo2 hi1 lo1 hbase p evmMemBase flag resume off size x1o scmVal lenAddr
        x16o x17o x19o x21o x22o x23o f0 descInit memBytes
        hDescLen hSrcAlign hSrcOver hSrcValid hOff hOff32 hlaMem hlaMem2 hla2 hla1
      have Restf := cpsTripleWithin_frameR
        (((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
          ((scmAddr + signExtend12 0) ↦ₘ scmVal) **
          ((lenAddr + signExtend12 0) ↦ₘ size) ** ((.x13 : Reg) ↦ᵣ evmMemBase) **
          ((.x7 : Reg) ↦ᵣ (evmMemBase + BitVec.ofNat 64 (off.toNat + size.toNat))) **
          ((.x28 : Reg) ↦ᵣ (rdBase + BitVec.ofNat 64 size.toNat)) **
          ((.x29 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x30 **
          bytesRegion rdBase (copyIntoRegion rdBytes memBytes 0 off.toNat size.toNat))
        (by pcFreeR) Rest
      have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) S1f Restf
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by
          simp only [returnCaptureX7Post, returnCaptureX28Post, returnCaptureX29Post,
            returnCaptureX30Post, returnCaptureLenPost, returnCaptureRdPost,
            if_neg h_scm_zero, if_neg h_oversize]
          xperm_chunked hq) c)

end Compose

/-! ## Anti-vacuity cover for the upgraded RETURN registry entry -/

/-- The upgraded RETURN theorem's system-call capture branch is satisfiable on a
    representative small return (`system_call_mode = 1`, `size = 5`), and both
    descriptor clamps are identity on that input. -/
theorem return_capture_nondegenerate :
    (1 : Word) ≠ 0 ∧ ¬ BitVec.ult (4096 : Word) (5 : Word) ∧
      returnClamp (5 : Word) = 5 ∧ returnClamp32 (5 : Word) = 5 := by
  decide

end Terminating
end EvmAsm.Evm64
