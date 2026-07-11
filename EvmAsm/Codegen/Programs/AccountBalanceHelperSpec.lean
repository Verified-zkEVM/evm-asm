/-
  EvmAsm.Codegen.Programs.AccountBalanceHelperSpec

  Lives under Codegen/Programs (not Evm64) because it pins the concrete
  linked `GuestAddrs.mset_memcpy` / `Codegen.Programs.MptSet` routine
  (layering L1: verified core may not import Codegen) — same shape as the
  other `*SAsm.lean` linked-PC verification files in this directory.

  Phase 3c part 1 (SELFDESTRUCT balance move, PR #10178 follow-up): success-path
  `cpsTripleWithin` triples for the helper subroutines called by
  `selfdestruct_balance_transfer` (`EvmAsm/Codegen/Programs/AccountBalance.lean`).

  This file proves the leaf helper `mset_memcpy`
  (`EvmAsm/Codegen/Programs/MptSet.lean`, 8 instructions):

  ```
  mset_memcpy:            -- a0 = dst, a1 = src, a2 = len; clobbers t0
    beqz a2, 2f           -- BEQ  x12 x0 +28
  1:
    lbu  t0, 0(a1)        -- LBU  x5  x11 0
    sb   t0, 0(a0)        -- SB   x10 x5  0
    addi a0, a0, 1
    addi a1, a1, 1
    addi a2, a2, -1
    bnez a2, 1b           -- BNE  x12 x0 -20
  2:
    ret                   -- JALR x0 x1 0
  ```

  The proof mirrors the RETURN window copy loop
  (`Evm64/Terminating/ReturnWindowLoopSpec.lean`, `returnCopyLoop_spec_within`)
  and reuses its pure content model `copyIntoRegion`; the only structural
  difference is the do-while shape (`BNE` back-edge after the decrement instead
  of a head `BEQ` re-test) and the `JALR` return to `ra`.

  Main results (all `∀ base`, plus a corollary pinned at the linked guest
  address `GuestAddrs.mset_memcpy`):

    * `mset_memcpy_body_spec_within`  — one loop iteration (5 instructions).
    * `mset_memcpy_loop_spec_within`  — the loop closure by induction on the
      byte countdown.
    * `mset_memcpy_spec_pinned_within` / `mset_memcpy_own_spec_within` — the
      full function `base → raVal &&& ~~~1`: copies `n` bytes from the source
      region into the destination region (`copyIntoRegion dstBytes srcBytes
      dstOff srcOff n`), advancing `a0`/`a1` by `n`, zeroing `a2`, clobbering
      `t0`, preserving `ra` and both regions' framing. The two regions are
      separate separation-logic atoms, so this covers exactly the
      non-overlapping case (all `selfdestruct_balance_transfer` call sites copy
      between distinct buffers).
    * `mset_memcpy_spec_within`       — the same triple at the fixed guest
      address `msetMemcpyBase = GuestAddrs.mset_memcpy`.
    * `copyIntoRegion_getElem` / `copyIntoRegion_self` — pure content lemmas;
      in particular a whole-buffer copy yields exactly the source bytes.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-! ## Pure content lemmas for `copyIntoRegion` -/

/-- Pointwise characterization of `copyIntoRegion`: inside the copied window
    the destination holds the corresponding source byte, outside it the
    original destination byte. -/
theorem copyIntoRegion_getElem (dstBytes srcBytes : List (BitVec 8))
    (dstOff srcOff i j : Nat) (hj : j < dstBytes.length) :
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i)[j]'(by
        rw [copyIntoRegion_length]; exact hj)
      = if dstOff ≤ j ∧ j < dstOff + i then srcBytes.getD (srcOff + (j - dstOff)) 0
        else dstBytes[j]'hj := by
  induction i with
  | zero =>
    rw [if_neg (by omega)]
    rfl
  | succ k ih =>
    show ((copyIntoRegion dstBytes srcBytes dstOff srcOff k).set (dstOff + k)
        (srcBytes.getD (srcOff + k) 0))[j]'(by
          rw [List.length_set, copyIntoRegion_length]; exact hj) = _
    by_cases hcase : dstOff + k = j
    · subst hcase
      rw [List.getElem_set_self, if_pos (by omega)]
      congr 1
      omega
    · rw [List.getElem_set_ne hcase, ih]
      by_cases hin : dstOff ≤ j ∧ j < dstOff + k
      · rw [if_pos hin, if_pos (by omega)]
      · rw [if_neg hin, if_neg (by omega)]

/-- **Whole-buffer copy.** Copying all `srcBytes.length` bytes over a
    destination of the same length yields exactly the source bytes — the
    semantic form the `selfdestruct_balance_transfer` same-address arm needs
    (the output slot ends up holding the untouched account RLP). -/
theorem copyIntoRegion_self (dstBytes srcBytes : List (BitVec 8))
    (hlen : dstBytes.length = srcBytes.length) :
    copyIntoRegion dstBytes srcBytes 0 0 srcBytes.length = srcBytes := by
  apply List.ext_getElem (by rw [copyIntoRegion_length, hlen])
  intro j h1 h2
  rw [copyIntoRegion_getElem dstBytes srcBytes 0 0 srcBytes.length j
        (by rw [copyIntoRegion_length] at h1; exact h1)]
  rw [if_pos ⟨Nat.zero_le _, by omega⟩, Nat.sub_zero, Nat.zero_add,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

/-! ## Word-counter arithmetic (loop decrement / nonzero) -/

/-- `(n+1) - 1 = n` as words (loop counter decrement). -/
private theorem mm_word_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem mm_word_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- Pointer advance by 1 byte. -/
private theorem mm_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

/-! ## Fixed guest address (pinned to `Codegen.GuestAddrs`) -/

/-- Guest entry of `mset_memcpy`. -/
def msetMemcpyBase : Word := 0x800054a4#64

theorem msetMemcpyBase_eq :
    msetMemcpyBase = BitVec.ofNat 64 Codegen.GuestAddrs.mset_memcpy := by decide

theorem msetMemcpy_prog_length : Codegen.msetMemcpy_prog.length = 8 := rfl

/-- The `mset_memcpy` body at its linked guest address. -/
abbrev msetMemcpyCode : CodeReq :=
  CodeReq.ofProg msetMemcpyBase Codegen.msetMemcpy_prog

/-! ## One loop iteration (the 5 straight-line body instructions) -/

/-- **One `mset_memcpy` iteration** (`base+4 → base+24`): copy the byte at
    source index `srcOff+i` to destination index `dstOff+i`, advance both
    pointers, and decrement the counter from `m+1` to `m`. -/
private theorem mset_memcpy_body_spec_within (base srcBase dstBase x5old : Word)
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
    cpsTripleWithin 5 (base + 4) (base + 24)
      (CodeReq.ofProg base Codegen.msetMemcpy_prog)
      (((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x5 : Reg) ↦ᵣ x5old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 m) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x5 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) := by
  -- Code-inclusion (mono) lemmas for the five body instructions.
  have hmono1 : ∀ a i', CodeReq.singleton (base + 4) (.LBU .x5 .x11 (0 : BitVec 12)) a = some i'
      → CodeReq.ofProg base Codegen.msetMemcpy_prog a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base Codegen.msetMemcpy_prog 1 (base + 4)
      (by decide) (by decide) (by bv_omega))
  have hmono2 : ∀ a i', CodeReq.singleton (base + 8) (.SB .x10 .x5 (0 : BitVec 12)) a = some i'
      → CodeReq.ofProg base Codegen.msetMemcpy_prog a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base Codegen.msetMemcpy_prog 2 (base + 8)
      (by decide) (by decide) (by bv_omega))
  have hmono3 : ∀ a i', CodeReq.singleton (base + 12) (.ADDI .x10 .x10 (1 : BitVec 12)) a = some i'
      → CodeReq.ofProg base Codegen.msetMemcpy_prog a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base Codegen.msetMemcpy_prog 3 (base + 12)
      (by decide) (by decide) (by bv_omega))
  have hmono4 : ∀ a i', CodeReq.singleton (base + 16) (.ADDI .x11 .x11 (1 : BitVec 12)) a = some i'
      → CodeReq.ofProg base Codegen.msetMemcpy_prog a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base Codegen.msetMemcpy_prog 4 (base + 16)
      (by decide) (by decide) (by bv_omega))
  have hmono5 : ∀ a i', CodeReq.singleton (base + 20) (.ADDI .x12 .x12 (-1 : BitVec 12)) a = some i'
      → CodeReq.ofProg base Codegen.msetMemcpy_prog a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base Codegen.msetMemcpy_prog 5 (base + 20)
      (by decide) (by decide) (by bv_omega))
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
  -- Step 1: LBU x5 ← src[srcOff+i].
  have hlbu := bytesRegion_lbu_within .x5 .x11 srcBase x5old (base + 4)
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega, ← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code hmono1 hlbu
  have hlbuf := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by pcFreeR) hlbue
  -- Step 2: SB dst[dstOff+i] ← x5 (= bval).
  have hsb := bytesRegion_sb_within .x10 .x5 dstBase (bval.zeroExtend 64) (base + 8)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hsb
  have hsbe := cpsTripleWithin_extend_code hmono2 hsb
  have hsbf := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by pcFreeR) hsbe
  -- Step 3: ADDI x10 += 1.
  have h3 := addi_spec_gen_same_within .x10
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (base + 12) (by decide)
  rw [mm_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at h3
  have h3e := cpsTripleWithin_extend_code hmono3 h3
  have h3f := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x5 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h3e
  -- Step 4: ADDI x11 += 1.
  have h4 := addi_spec_gen_same_within .x11
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (base + 16) (by decide)
  rw [mm_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at h4
  have h4e := cpsTripleWithin_extend_code hmono4 h4
  have h4f := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x5 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h4e
  -- Step 5: ADDI x12 -= 1.
  have h5 := addi_spec_gen_same_within .x12 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (base + 20) (by decide)
  rw [mm_word_succ_dec m, show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at h5
  have h5e := cpsTripleWithin_extend_code hmono5 h5
  have h5f := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x5 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h5e
  -- Compose the five steps.
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1234 h5f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by rw [hgetd]; xperm_chunked hq) s12345)

/-! ## The loop closure -/

/-- **The `mset_memcpy` loop closure** (`base+4 → base+28`) by induction on the
    byte countdown: entering the loop body with `n+1` bytes left and `i` bytes
    already copied, it copies the remaining `n+1` bytes and falls through past
    the `BNE` back-edge with `a2 = 0`. -/
theorem mset_memcpy_loop_spec_within (base srcBase dstBase x5old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff n i : Nat)
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
    cpsTripleWithin (6 * (n + 1)) (base + 4) (base + 28)
      (CodeReq.ofProg base Codegen.msetMemcpy_prog)
      (((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x5 : Reg) ↦ᵣ x5old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i + (n + 1)))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i + (n + 1)))) **
       regOwn .x5 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + (n + 1)))) := by
  have hmono6 : ∀ a i', CodeReq.singleton (base + 24) (.BNE .x12 .x0 (-20 : BitVec 13)) a = some i'
      → CodeReq.ofProg base Codegen.msetMemcpy_prog a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base Codegen.msetMemcpy_prog 6 (base + 24)
      (by decide) (by decide) (by bv_omega))
  have ha_back : (base + 24 : Word) + signExtend13 (-20 : BitVec 13) = base + 4 := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have ha_fall : (base + 24 : Word) + 4 = base + 28 := by bv_omega
  induction n generalizing i x5old with
  | zero =>
    -- One iteration, then BNE not taken (x12 = 0) → fall through to base+28.
    have hbody := mset_memcpy_body_spec_within base srcBase dstBase x5old
      srcBytes dstBytes srcOff dstOff i 0 h_src_align h_dst_align (by omega) (by omega)
      h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x12 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (base + 24)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono6 hbne
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have hntf := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x5 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by pcFreeR) hnt
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hbody hntf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          simp only [show srcOff + i + (0 + 1) = srcOff + (i + 1) from by omega,
                     show dstOff + i + (0 + 1) = dstOff + (i + 1) from by omega,
                     show i + (0 + 1) = i + 1 from by omega]
          have hq2 : (((.x5 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
              ((.x12 : Reg) ↦ᵣ (0 : Word)) **
              ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
              ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion srcBase srcBytes **
              bytesRegion dstBase
                (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x5) _ hq2
          xperm_chunked hq3) sfull)
  | succ k ih =>
    -- One iteration, BNE taken (x12 = k+1 ≠ 0) back to base+4, then the IH.
    have hbody := mset_memcpy_body_spec_within base srcBase dstBase x5old
      srcBytes dstBytes srcOff dstOff i (k + 1) h_src_align h_dst_align (by omega) (by omega)
      h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x12 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (base + 24)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono6 hbne
    have htaken := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact mm_word_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have htf := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x5 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by pcFreeR) htaken
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega)
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hbody htf
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show srcOff + (i + 1) + (k + 1) = srcOff + i + (k + 1 + 1) from by omega,
                     show dstOff + (i + 1) + (k + 1) = dstOff + i + (k + 1 + 1) from by omega,
                     show i + 1 + (k + 1) = i + (k + 1 + 1) from by omega] at hq
          xperm_chunked hq) sfull)

/-! ## The full function: `base → raVal &&& ~~~1` -/

/-- **`mset_memcpy` full-function triple** (pinned-scratch form, `∀ base`):
    from the entry with `a0 = dst+dstOff`, `a1 = src+srcOff`, `a2 = n`, and
    return address `raVal` in `ra`, the function copies `n` bytes
    (`copyIntoRegion dstBytes srcBytes dstOff srcOff n`), advances `a0`/`a1`
    by `n`, zeroes `a2`, clobbers `t0`, preserves `ra` and the source region,
    and returns to `raVal &&& ~~~1`. -/
theorem mset_memcpy_spec_pinned_within (base srcBase dstBase raVal x5old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff n : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_bound : srcOff + n ≤ srcBytes.length)
    (h_dst_bound : dstOff + n ≤ dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * n + 2) base (raVal &&& ~~~1)
      (CodeReq.ofProg base Codegen.msetMemcpy_prog)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 dstOff)) **
       ((.x5 : Reg) ↦ᵣ x5old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + n))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + n))) **
       regOwn .x5 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff n)) := by
  have hmono0 : ∀ a i', CodeReq.singleton base (.BEQ .x12 .x0 (28 : BitVec 13)) a = some i'
      → CodeReq.ofProg base Codegen.msetMemcpy_prog a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base Codegen.msetMemcpy_prog 0 base
      (by decide) (by decide) (by bv_omega))
  have hmono7 : ∀ a i', CodeReq.singleton (base + 28) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i'
      → CodeReq.ofProg base Codegen.msetMemcpy_prog a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base Codegen.msetMemcpy_prog 7 (base + 28)
      (by decide) (by decide) (by bv_omega))
  have ha_t : base + signExtend13 (28 : BitVec 13) = base + 28 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
  -- The JALR return.
  have hjalr := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 28)
  simp only [signExtend12_0] at hjalr
  rw [show (raVal + 0 : Word) = raVal from by bv_omega] at hjalr
  have hjalre := cpsTripleWithin_extend_code hmono7 hjalr
  cases n with
  | zero =>
    -- BEQ taken (x12 = 0) → base+28 → JALR.
    have hbeq := beq_spec_gen_within .x12 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) base
    rw [ha_t] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono0 hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 dstOff)) **
       ((.x5 : Reg) ↦ᵣ x5old) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (by pcFreeR) htaken
    have hjalrf := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 dstOff)) **
       ((.x5 : Reg) ↦ᵣ x5old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (by pcFreeR) hjalre
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) htf hjalrf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          simp only [copyIntoRegion, Nat.add_zero]
          have hq2 : (((.x5 : Reg) ↦ᵣ x5old) **
              ((.x1 : Reg) ↦ᵣ raVal) **
              ((.x12 : Reg) ↦ᵣ (0 : Word)) **
              ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
              ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 dstOff)) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x5) _ hq2
          xperm_chunked hq3) sfull)
  | succ m =>
    -- BEQ not taken (x12 = m+1 ≠ 0) → loop → JALR.
    have hbeq := beq_spec_gen_within .x12 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (m + 1))
      (0 : Word) base
    rw [ha_t] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono0 hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact mm_word_succ_ne_zero m (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 dstOff)) **
       ((.x5 : Reg) ↦ᵣ x5old) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (by pcFreeR) hnt
    have hloop := mset_memcpy_loop_spec_within base srcBase dstBase x5old
      srcBytes dstBytes srcOff dstOff m 0 h_src_align h_dst_align
      (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
    rw [show copyIntoRegion dstBytes srcBytes dstOff srcOff 0 = dstBytes from rfl] at hloop
    simp only [Nat.add_zero, Nat.zero_add] at hloop
    have hloopf := cpsTripleWithin_frameR ((.x1 : Reg) ↦ᵣ raVal) (by pcFreeR) hloop
    have hjalrf := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (m + 1)))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (m + 1)))) **
       regOwn .x5 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (m + 1)))
      (by pcFreeR) hjalre
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hntf hloopf
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) s1 hjalrf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by xperm_chunked hq) sfull)

/-- `mset_memcpy_spec_pinned_within` with the `t0` pin released to `regOwn` —
    the form a caller's clobbered-scratch post feeds directly. -/
theorem mset_memcpy_own_spec_within (base srcBase dstBase raVal : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff n : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_bound : srcOff + n ≤ srcBytes.length)
    (h_dst_bound : dstOff + n ≤ dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * n + 2) base (raVal &&& ~~~1)
      (CodeReq.ofProg base Codegen.msetMemcpy_prog)
      ((((.x1 : Reg) ↦ᵣ raVal) **
        ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 dstOff)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes) **
       regOwn .x5)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + n))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + n))) **
       regOwn .x5 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff n)) :=
  cpsTripleWithin_of_forall_regIs_to_regOwn (fun x5old =>
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (mset_memcpy_spec_pinned_within base srcBase dstBase raVal x5old
        srcBytes dstBytes srcOff dstOff n h_src_align h_dst_align h_src_bound
        h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid))

/-- **`mset_memcpy` at its linked guest address** (`GuestAddrs.mset_memcpy`) —
    the form the `selfdestruct_balance_transfer` composition consumes. -/
theorem mset_memcpy_spec_within (srcBase dstBase raVal : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff n : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_bound : srcOff + n ≤ srcBytes.length)
    (h_dst_bound : dstOff + n ≤ dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * n + 2) msetMemcpyBase (raVal &&& ~~~1) msetMemcpyCode
      ((((.x1 : Reg) ↦ᵣ raVal) **
        ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 dstOff)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes) **
       regOwn .x5)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + n))) **
       ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + n))) **
       regOwn .x5 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff n)) :=
  mset_memcpy_own_spec_within msetMemcpyBase srcBase dstBase raVal
    srcBytes dstBytes srcOff dstOff n h_src_align h_dst_align h_src_bound
    h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid

end EvmAsm.Codegen
