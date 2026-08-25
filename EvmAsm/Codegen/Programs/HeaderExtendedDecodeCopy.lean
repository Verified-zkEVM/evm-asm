/-
  EvmAsm.Codegen.Programs.HeaderExtendedDecodeCopy

  **The shared 32-byte field-copy loop of `header_extended_decode`, proved once.**

  `GuestAddrs.header_extended_decode` (174 instructions; the extent
  `hi - lo = 4 * headerExtendedDecode_prog.length` is pinned by
  `headerExtendedDecode_prog_length`) contains *two* byte-copy loops, and they
  are the same six instructions verbatim:

  ```
  GuestAddrs.header_extended_decode + 88 .. + 108   -- program indices 22..27
  GuestAddrs.header_extended_decode + 192 .. + 212  -- program indices 48..53

      lbu  t1, 0(t3)      -- LBU  x6  x28 0
      sb   t1, 0(t4)      -- SB   x29 x6  0
      addi t3, t3, 1      -- ADDI x28 x28 1     (source pointer)
      addi t4, t4, 1      -- ADDI x29 x29 1     (destination pointer)
      addi t0, t0, -1     -- ADDI x5  x5  -1    (byte countdown)
      bnez t0, -20        -- BNE  x5  x0  -20   (do-while back edge)
  ```

  They copy the two 32-byte header fields — `parent_hash` into `out + 0` and
  `state_root` into `out + 32` — from the RLP content window the preceding
  `rlp_walk_next` call left in `a0`/`a2`.

  So this file proves **one** loop lemma and instantiates it **twice**, rather
  than proving the same loop twice.  That is the factoring #12813 used for its
  five textually identical copy loops (`aer_copy_loop`, parameterised over the
  loop-top program index with its code memberships bundled), and it is followed
  here deliberately.

  The loop shape is the same do-while countdown as `mset_memcpy`
  (`EvmAsm/Codegen/Programs/AccountBalanceHelperSpec.lean`,
  `mset_memcpy_loop_spec_within`), and the proof is ported from it.  Three
  differences, all mechanical: the registers (`x5`/`x28`/`x29`/`x6` here versus
  `x12`/`x11`/`x10`/`x5` there), the order of the two pointer increments
  (source first here, destination first there), and the code requirement — this
  loop sits at a *parameterised offset inside a 174-instruction program*, so the
  six code memberships are bundled as `CopyCode` rather than resolved against a
  fixed 8-instruction `ofProg`.

  The pure content model is `copyIntoRegion`, reused unchanged from
  `EvmAsm/Evm64/Terminating/ReturnWindowLoopSpec.lean`.

  Main results:

    * `CopyCode`             — the six code memberships for a loop top at `L`.
    * `copy_body_spec_within`— one iteration (5 instructions, `L → L + 20`).
    * `copy_loop_spec_within`— the closure by induction on the countdown
                               (`6 * (n+1)` steps, `L → L + 24`).
    * `copyCode_at`          — `CopyCode` for a loop top at program index `n`,
                               discharged from `headerExtendedDecode_prog`
                               by `rfl` (no instruction transcribed by hand).
    * `parentHashCopyCode` / `stateRootCopyCode` — the two instantiations, at
                               indices 22 and 48.
    * `parent_hash_copy_spec_within` / `state_root_copy_spec_within` — the two
                               loops, each a one-line application of the shared
                               lemma.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec
import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Codegen.Programs.HeaderU64ExtractSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.HeaderExtendedDecodeCopy

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-! ## Word-counter arithmetic

    Verbatim from `AccountBalanceHelperSpec` (they are `private` there, so the
    three one-liners are restated rather than the file being edited). -/

/-- `(n+1) - 1 = n` as words (loop counter decrement). -/
private theorem word_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem word_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- Pointer advance by 1 byte. -/
private theorem advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

/-! ## The code requirement for one loop

    `cpsTripleWithin` is monotone in the `CodeReq`, so the loop lemma does not
    need to know *which* program it sits in — only that the six instructions of
    the loop are present at `L .. L+20`.  Bundling them keeps the two
    instantiation sites to one line each. -/

/-- The six code memberships of a copy loop whose top instruction is at `L`,
    inside an ambient code requirement `cr`.

    Every field is exactly the instruction at the corresponding program index of
    `headerExtendedDecode_prog`; `copyCode_at` discharges all six by `rfl`
    against that Program, so no opcode here is transcribed by hand. -/
structure CopyCode (cr : CodeReq) (L : Word) : Prop where
  lbu : ∀ a i, CodeReq.singleton L (.LBU .x6 .x28 (0 : BitVec 12)) a = some i → cr a = some i
  sb : ∀ a i, CodeReq.singleton (L + 4) (.SB .x29 .x6 (0 : BitVec 12)) a = some i → cr a = some i
  incSrc : ∀ a i,
    CodeReq.singleton (L + 8) (.ADDI .x28 .x28 (1 : BitVec 12)) a = some i → cr a = some i
  incDst : ∀ a i,
    CodeReq.singleton (L + 12) (.ADDI .x29 .x29 (1 : BitVec 12)) a = some i → cr a = some i
  dec : ∀ a i,
    CodeReq.singleton (L + 16) (.ADDI .x5 .x5 (-1 : BitVec 12)) a = some i → cr a = some i
  bne : ∀ a i,
    CodeReq.singleton (L + 20) (.BNE .x5 .x0 (-20 : BitVec 13)) a = some i → cr a = some i

/-! ## One iteration -/

/-- **One iteration of the shared copy loop** (`L → L + 20`, 5 instructions):
    copy the byte at source index `srcOff + i` to destination index
    `dstOff + i`, advance both pointers, and decrement the countdown from
    `m + 1` to `m`.

    The two regions are separate separation-logic atoms, so this covers exactly
    the non-overlapping case — which is what the decoder does: it copies out of
    the caller's RLP buffer into the caller's 144-byte output struct. -/
theorem copy_body_spec_within (cr : CodeReq) (L : Word) (hcode : CopyCode cr L)
    (srcBase dstBase x6old : Word)
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
    cpsTripleWithin 5 L (L + 20) cr
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x6 : Reg) ↦ᵣ x6old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
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
  -- idx +0: LBU x6 ← src[srcOff+i].
  have hlbu := bytesRegion_lbu_within .x6 .x28 srcBase x6old L
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code hcode.lbu hlbu
  have hlbuf := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by pcFreeR) hlbue
  -- idx +1: SB dst[dstOff+i] ← x6.
  have hsb := bytesRegion_sb_within .x29 .x6 dstBase (bval.zeroExtend 64) (L + 4)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (L + 4 : Word) + 4 = L + 8 from by bv_omega] at hsb
  have hsbe := cpsTripleWithin_extend_code hcode.sb hsb
  have hsbf := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by pcFreeR) hsbe
  -- idx +2: ADDI x28 += 1 (source pointer).
  have h3 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (L + 8) (by decide)
  rw [advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (L + 8 : Word) + 4 = L + 12 from by bv_omega] at h3
  have h3e := cpsTripleWithin_extend_code hcode.incSrc h3
  have h3f := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x6 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h3e
  -- idx +3: ADDI x29 += 1 (destination pointer).
  have h4 := addi_spec_gen_same_within .x29
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (L + 12) (by decide)
  rw [advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (L + 12 : Word) + 4 = L + 16 from by bv_omega] at h4
  have h4e := cpsTripleWithin_extend_code hcode.incDst h4
  have h4f := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x6 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h4e
  -- idx +4: ADDI x5 -= 1 (countdown).
  have h5 := addi_spec_gen_same_within .x5 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (L + 16) (by decide)
  rw [word_succ_dec m, show (L + 16 : Word) + 4 = L + 20 from by bv_omega] at h5
  have h5e := cpsTripleWithin_extend_code hcode.dec h5
  have h5f := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x6 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h5e
  -- Compose the five steps.
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1234 h5f
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by rw [hgetd]; xperm_chunked hq) s12345)

/-! ## The loop closure -/

/-- **The shared copy loop** (`L → L + 24`) by induction on the byte countdown:
    entering the loop top with `n + 1` bytes left and `i` bytes already copied,
    it copies the remaining `n + 1` bytes and falls through past the `BNE` back
    edge with `x5 = 0`.

    Step count `6 * (n + 1)`: six instructions per iteration, the `BNE`
    included, and the exit iteration pays for the not-taken branch too. -/
theorem copy_loop_spec_within (cr : CodeReq) (L : Word) (hcode : CopyCode cr L)
    (srcBase dstBase x6old : Word)
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
    cpsTripleWithin (6 * (n + 1)) L (L + 24) cr
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x6 : Reg) ↦ᵣ x6old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x5 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i + (n + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i + (n + 1)))) **
       regOwn .x6 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase
         (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + (n + 1)))) := by
  have ha_back : (L + 20 : Word) + signExtend13 (-20 : BitVec 13) = L := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have ha_fall : (L + 20 : Word) + 4 = L + 24 := by bv_omega
  induction n generalizing i x6old with
  | zero =>
    -- One iteration, then BNE not taken (x5 = 0) → fall through to L + 24.
    have hbody := copy_body_spec_within cr L hcode srcBase dstBase x6old
      srcBytes dstBytes srcOff dstOff i 0 h_src_align h_dst_align (by omega) (by omega)
      h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x5 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (L + 20)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hcode.bne hbne
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
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
          have hq2 : (((.x6 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
              ((.x5 : Reg) ↦ᵣ (0 : Word)) **
              ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
              ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion srcBase srcBytes **
              bytesRegion dstBase
                (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x6) _ hq2
          xperm_chunked hq3) sfull)
  | succ k ih =>
    -- One iteration, BNE taken (x5 = k+1 ≠ 0) back to L, then the IH.
    have hbody := copy_body_spec_within cr L hcode srcBase dstBase x6old
      srcBytes dstBytes srcOff dstOff i (k + 1) h_src_align h_dst_align (by omega) (by omega)
      h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x5 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (L + 20)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hcode.bne hbne
    have htaken := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact word_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by pcFreeR) htaken
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega)
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hbody htf
    have s2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show srcOff + (i + 1) + (k + 1) = srcOff + i + (k + 1 + 1) from by omega,
                     show dstOff + (i + 1) + (k + 1) = dstOff + i + (k + 1 + 1) from by omega,
                     show i + 1 + (k + 1) = i + (k + 1 + 1) from by omega] at hq
          xperm_chunked hq) s2)

/-! ## The two anchored instantiations

    `GuestAddrs.header_extended_decode + 88` (program index 22) and
    `GuestAddrs.header_extended_decode + 192` (program index 48).

    Both `CopyCode` bundles are built by `copyCode_at`, whose `hins` obligation
    is `rfl` against `headerExtendedDecode_prog`.  So the claim "these two loops
    are the same six instructions" is not asserted in prose here — it is the
    kernel checking twelve `rfl`s against the linked Program, six per site,
    against the *same six* instruction terms in `CopyCode`. -/

/-- `k < 174` as a bound on `headerExtendedDecode_prog.length`, routed through
    the named length theorem.  `decide` on the goal directly re-elaborates the
    174-element `Instr` list and exhausts the recursion budget. -/
private theorem hed_index_lt (k : Nat) (h : k < 174) :
    k < headerExtendedDecode_prog.length := by
  rw [headerExtendedDecode_prog_length]; exact h

/-- Instruction `k` of the **linked** decoder Program is in any code
    requirement that contains the decoder image. -/
private theorem hed_mem_at (cr : CodeReq)
    (hmono : ∀ a i, HeaderU64ExtractSpec.headerExtendedDecodeCode a = some i → cr a = some i)
    (k : Nat) (ins : Instr) (A : Word)
    (hA : A = HeaderU64ExtractSpec.headerExtendedDecodeBase + BitVec.ofNat 64 (4 * k))
    (hk : k < headerExtendedDecode_prog.length)
    (hins : headerExtendedDecode_prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → cr a = some i :=
  fun a i h => hmono a i
    (CodeReq.ofProg_mem_at HeaderU64ExtractSpec.headerExtendedDecodeBase A
      headerExtendedDecode_prog k ins hA hk hins
      (by rw [headerExtendedDecode_prog_length]; decide) a i h)

/-- The `CopyCode` bundle for the copy loop whose top instruction is program
    index `n` of the linked decoder.  All six memberships are discharged from
    `headerExtendedDecode_prog` by `rfl`; nothing is transcribed. -/
theorem copyCode_at (cr : CodeReq)
    (hmono : ∀ a i, HeaderU64ExtractSpec.headerExtendedDecodeCode a = some i → cr a = some i)
    (n : Nat) (hn : n + 5 < 174) (L : Word)
    (hL : L = HeaderU64ExtractSpec.headerExtendedDecodeBase + BitVec.ofNat 64 (4 * n))
    (h0 : headerExtendedDecode_prog[n]'(hed_index_lt n (by omega))
      = .LBU .x6 .x28 (0 : BitVec 12))
    (h1 : headerExtendedDecode_prog[n + 1]'(hed_index_lt (n + 1) (by omega))
      = .SB .x29 .x6 (0 : BitVec 12))
    (h2 : headerExtendedDecode_prog[n + 2]'(hed_index_lt (n + 2) (by omega))
      = .ADDI .x28 .x28 (1 : BitVec 12))
    (h3 : headerExtendedDecode_prog[n + 3]'(hed_index_lt (n + 3) (by omega))
      = .ADDI .x29 .x29 (1 : BitVec 12))
    (h4 : headerExtendedDecode_prog[n + 4]'(hed_index_lt (n + 4) (by omega))
      = .ADDI .x5 .x5 (-1 : BitVec 12))
    (h5 : headerExtendedDecode_prog[n + 5]'(hed_index_lt (n + 5) (by omega))
      = .BNE .x5 .x0 (-20 : BitVec 13)) :
    CopyCode cr L where
  lbu := hed_mem_at cr hmono n _ L hL _ h0
  sb := hed_mem_at cr hmono (n + 1) _ (L + 4) (by rw [hL]; bv_omega) _ h1
  incSrc := hed_mem_at cr hmono (n + 2) _ (L + 8) (by rw [hL]; bv_omega) _ h2
  incDst := hed_mem_at cr hmono (n + 3) _ (L + 12) (by rw [hL]; bv_omega) _ h3
  dec := hed_mem_at cr hmono (n + 4) _ (L + 16) (by rw [hL]; bv_omega) _ h4
  bne := hed_mem_at cr hmono (n + 5) _ (L + 20) (by rw [hL]; bv_omega) _ h5

/-- Loop top of the `parent_hash` copy: `GuestAddrs.header_extended_decode + 88`
    (program index 22).  The `sub t3,a0,a2` / `mv t4,s2` / `li t0,32` setup is
    at indices 19..21 and belongs to the caller, not to this lemma. -/
abbrev parentHashLoopTop : Word :=
  HeaderU64ExtractSpec.headerExtendedDecodeBase + BitVec.ofNat 64 88

/-- Loop top of the `state_root` copy:
    `GuestAddrs.header_extended_decode + 192` (program index 48).  Its setup at
    indices 45..47 differs from the `parent_hash` one in exactly one
    instruction — `addi t4,s2,32` instead of `mv t4,s2`, i.e. destination
    offset 32 instead of 0. -/
abbrev stateRootLoopTop : Word :=
  HeaderU64ExtractSpec.headerExtendedDecodeBase + BitVec.ofNat 64 192

/-- `CopyCode` for the `parent_hash` loop. -/
theorem parentHashCopyCode (cr : CodeReq)
    (hmono : ∀ a i, HeaderU64ExtractSpec.headerExtendedDecodeCode a = some i → cr a = some i) :
    CopyCode cr parentHashLoopTop :=
  copyCode_at cr hmono 22 (by omega) _ (by norm_num) rfl rfl rfl rfl rfl rfl

/-- `CopyCode` for the `state_root` loop — the SAME six instruction terms,
    twelve `rfl`s apart. -/
theorem stateRootCopyCode (cr : CodeReq)
    (hmono : ∀ a i, HeaderU64ExtractSpec.headerExtendedDecodeCode a = some i → cr a = some i) :
    CopyCode cr stateRootLoopTop :=
  copyCode_at cr hmono 48 (by omega) _ (by norm_num) rfl rfl rfl rfl rfl rfl

end EvmAsm.Codegen.HeaderExtendedDecodeCopy
