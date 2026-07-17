/-
  The prologue of `headerExtendedDecode_prog` (`Programs/HeaderDecode.lean`,
  PR-K39), slots [0]-[11]:

    [0]  ADDI sp, sp, -64        [1] SD sp, ra, 0    [2] SD sp, s0, 8
    [3]  SD sp, s1, 16           [4] SD sp, s2, 24   [5] SD sp, s3, 32
    [6]  MV s0, a0               [7] MV s2, a2
    [8]  JAL ra, rlp_walk_init   [9] BNE a2, x0, →fail  (HB + 664)
    [10] MV s1, a1               [11] MV s3, a0

  The prologue reserves the 64-byte frame, spills the five callee-saved
  registers (`ra`/`s0`/`s1`/`s2`/`s3`), stashes the header pointer (`a0 → s0`)
  and the output-struct pointer (`a2 → s2`), then calls the merged strict list
  opener `rlp_walk_init`.  `rlp_walk_init`'s seven-way status lands in `a2`
  (`x12`): status 0 (short/long list success) continues, everything else
  short-circuits to `HB + 664`.  On success the initial cursor (`a0`) and list
  end (`a1`) are stashed into `s3`/`s1` for the sequential walk.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeSlots
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeEpilogue
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm EvmAsm.EL.RLP

/-- The `rlp_walk_init` callee post as re-based onto `fullCode`: the surrendered
    temporaries `t0..t6`, the preserved `x0`/`ra`/input bytes, and the nine-way
    status disjunction (empty=2, not-a-list=1, short-success=0, short-mismatch=3,
    long-truncated=4, long-leading-zero=5, long-non-minimal=6, long-mismatch=7,
    long-success=0).  Matches the post of `rlp_walk_init_spec_within` with
    `base := WIB`. -/
def hedWalkInitPost (hdrBase raVal listLen : Word) (listBytes : List (BitVec 8))
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
    bytesRegion hdrBase listBytes) **
  (fun h =>
    (((.x10 ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ (2 : Word)) ** ⌜listLen = (0 : Word)⌝) h) ∨
    (((.x10 ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) **
       (.x11 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (1 : Word)) **
       ⌜listLen ≠ (0 : Word) ∧
         BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true⌝) h) ∨
    (((.x10 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
       (.x11 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
       ⌜listLen ≠ (0 : Word) ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
         BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
         (hdrBase + BitVec.ofNat 64 listOff) +
           (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
           = (hdrBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
    (((.x10 ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) **
       (.x11 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (3 : Word)) **
       ⌜listLen ≠ (0 : Word) ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
         BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
         (hdrBase + BitVec.ofNat 64 listOff) +
           (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
           ≠ (hdrBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
    (((.x10 ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) **
       (.x11 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (4 : Word)) **
       ⌜listLen ≠ (0 : Word) ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
         BitVec.ult ((hdrBase + BitVec.ofNat 64 listOff) + listLen)
           ((hdrBase + BitVec.ofNat 64 listOff) +
             (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
           = true⌝) h) ∨
    (((.x10 ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) **
       (.x11 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (5 : Word)) **
       ⌜listLen ≠ (0 : Word) ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
         ¬ BitVec.ult ((hdrBase + BitVec.ofNat 64 listOff) + listLen)
           ((hdrBase + BitVec.ofNat 64 listOff) +
             (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
           = true ∧
         listBytes[listOff + 1]? = some (0 : BitVec 8)⌝) h) ∨
    (((.x10 ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) **
       (.x11 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (6 : Word)) **
       ⌜listLen ≠ (0 : Word) ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
         ¬ BitVec.ult ((hdrBase + BitVec.ofNat 64 listOff) + listLen)
           ((hdrBase + BitVec.ofNat 64 listOff) +
             (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
           = true ∧
         listBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
         BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
           ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true⌝) h) ∨
    (((.x10 ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) **
       (.x11 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (7 : Word)) **
       ⌜listLen ≠ (0 : Word) ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
         ¬ BitVec.ult ((hdrBase + BitVec.ofNat 64 listOff) + listLen)
           ((hdrBase + BitVec.ofNat 64 listOff) +
             (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
           = true ∧
         listBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
         ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
           ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
         ((hdrBase + BitVec.ofNat 64 listOff) +
             (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
             BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
               ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
           ≠ (hdrBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
    (((.x10 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) +
         (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
       (.x11 ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
       ⌜listLen ≠ (0 : Word) ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
         ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
         ¬ BitVec.ult ((hdrBase + BitVec.ofNat 64 listOff) + listLen)
           ((hdrBase + BitVec.ofNat 64 listOff) +
             (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
           = true ∧
         listBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
         ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
           ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
         ((hdrBase + BitVec.ofNat 64 listOff) +
             (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
             BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
               ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
           = (hdrBase + BitVec.ofNat 64 listOff) + listLen⌝) h))

/-- The prologue ok exit at `HB + 48` (slot 12): the 64-byte frame is spilled,
    `s0 = a0` (header ptr) and `s2 = a2` (output ptr) are stashed, and
    `rlp_walk_init` succeeded, so the initial cursor is in `s3 = x19` and the
    list end `ptr + listLen` in `s1 = x9`.  The working temporaries are
    surrendered for the sequential walk. -/
def hedPrologueOk (hdrBase a2Old spF raSaved s0old s1old s2old s3old listLen : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (Extra : Assertion) : Assertion :=
  fun h => ∃ initCursor : Word,
    (((.x8 : Reg) ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) ** ((.x18 : Reg) ↦ᵣ a2Old) **
      ((.x2 : Reg) ↦ᵣ spF) ** ((.x9 : Reg) ↦ᵣ ((hdrBase + BitVec.ofNat 64 listOff) + listLen)) **
      ((.x19 : Reg) ↦ᵣ initCursor) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
      bytesRegion hdrBase listBytes ** hedStackFrame spF raSaved s0old s1old s2old s3old ** Extra) h

/-- The prologue fail exit at `HB + 664`: `rlp_walk_init` rejected (status ≠ 0),
    so the decode short-circuits to the fail entry.  The frame is spilled and the
    saved-register / stack image is intact for the epilogue restore. -/
def hedPrologueFail (hdrBase a2Old spF raSaved s0old s1old s2old s3old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (Extra : Assertion) : Assertion :=
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** ((.x8 : Reg) ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) **
    ((.x18 : Reg) ↦ᵣ a2Old) ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x9 : Reg) ↦ᵣ s1old) **
    ((.x19 : Reg) ↦ᵣ s3old) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x1 : Reg) ↦ᵣ (HB + 36)) ** bytesRegion hdrBase listBytes **
    hedStackFrame spF raSaved s0old s1old s2old s3old ** Extra

set_option maxRecDepth 8000 in
/-- **Prologue.**  Frame spill + saved-register stash + `rlp_walk_init` call +
    seven-way status dispatch.  On success (`x12 = 0`) the cursor / end are
    stashed into `s3`/`s1` and control reaches `HB + 48` (`hedPrologueOk`); any
    reject short-circuits to `HB + 664` (`hedPrologueFail`). -/
theorem hedPrologue {Extra : Assertion}
    (hdrBase listLen a2Old spOld raSaved s0old s1old s2old s3old t0 t1 t2 t3 t4 t5 t6 : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (hExtra : Extra.pcFree)
    (hsalign : hdrBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length)
    (hover : hdrBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (hdrBase + BitVec.ofNat 64 listOff) = true)
    (hll_len : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        listOff + 1 + ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ listBytes.length)
    (hll_over : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        hdrBase.toNat + (listOff + 1 +
          ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ∀ k, k < ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (hdrBase + BitVec.ofNat 64 (listOff + 1 + k)) = true) :
    cpsBranchWithin (8 + 82 + 3) HB fullCode
      (((.x2 : Reg) ↦ᵣ spOld) ** ((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0old) **
        ((.x9 : Reg) ↦ᵣ s1old) ** ((.x18 : Reg) ↦ᵣ s2old) ** ((.x19 : Reg) ↦ᵣ s3old) **
        ((.x10 : Reg) ↦ᵣ (hdrBase + BitVec.ofNat 64 listOff)) ** ((.x11 : Reg) ↦ᵣ listLen) **
        ((.x12 : Reg) ↦ᵣ a2Old) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) **
        ((.x7 : Reg) ↦ᵣ t2) ** ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) **
        ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion hdrBase listBytes **
        memOwn (spOld + signExtend12 (-64 : BitVec 12)) **
        memOwn ((spOld + signExtend12 (-64 : BitVec 12)) + 8) **
        memOwn ((spOld + signExtend12 (-64 : BitVec 12)) + 16) **
        memOwn ((spOld + signExtend12 (-64 : BitVec 12)) + 24) **
        memOwn ((spOld + signExtend12 (-64 : BitVec 12)) + 32) ** Extra)
      (HB + 664) (hedPrologueFail hdrBase a2Old (spOld + signExtend12 (-64 : BitVec 12))
        raSaved s0old s1old s2old s3old listBytes listOff Extra)
      (HB + 48) (hedPrologueOk hdrBase a2Old (spOld + signExtend12 (-64 : BitVec 12))
        raSaved s0old s1old s2old s3old listLen listBytes listOff Extra) := by
  set spF := spOld + signExtend12 (-64 : BitVec 12) with hspF
  set ptr := hdrBase + BitVec.ofNat 64 listOff with hptr
  -- membership witnesses for the straight-line front + dispatch instructions.
  have mem0 : ∀ a i, CodeReq.singleton HB (.ADDI .x2 .x2 (-64 : BitVec 12)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB HB headerExtendedDecode_prog 0 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem1 : ∀ a i, CodeReq.singleton (HB + 4) (.SD .x2 .x1 (0 : BitVec 12)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 4) headerExtendedDecode_prog 1 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem2 : ∀ a i, CodeReq.singleton (HB + 8) (.SD .x2 .x8 (8 : BitVec 12)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 8) headerExtendedDecode_prog 2 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem3 : ∀ a i, CodeReq.singleton (HB + 12) (.SD .x2 .x9 (16 : BitVec 12)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 12) headerExtendedDecode_prog 3 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem4 : ∀ a i, CodeReq.singleton (HB + 16) (.SD .x2 .x18 (24 : BitVec 12)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 16) headerExtendedDecode_prog 4 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem5 : ∀ a i, CodeReq.singleton (HB + 20) (.SD .x2 .x19 (32 : BitVec 12)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 20) headerExtendedDecode_prog 5 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem6 : ∀ a i, CodeReq.singleton (HB + 24) (.MV .x8 .x10) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 24) headerExtendedDecode_prog 6 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem7 : ∀ a i, CodeReq.singleton (HB + 28) (.MV .x18 .x12) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 28) headerExtendedDecode_prog 7 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem9 : ∀ a i, CodeReq.singleton (HB + 36) (.BNE .x12 .x0 (628 : BitVec 13)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 36) headerExtendedDecode_prog 9 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem10 : ∀ a i, CodeReq.singleton (HB + 40) (.MV .x9 .x11) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 40) headerExtendedDecode_prog 10 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have mem11 : ∀ a i, CodeReq.singleton (HB + 44) (.MV .x19 .x10) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 44) headerExtendedDecode_prog 11 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  -- ===== front: ADDI ; 5×SD ; 2×MV  (HB → HB + 32) =====
  -- [0] ADDI sp, sp, -64
  have h0 := addi_spec_gen_same_within .x2 spOld (-64 : BitVec 12) HB (by decide)
  rw [← hspF] at h0
  have h0L := cpsTripleWithin_extend_code mem0 h0
  have h0F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0old) ** ((.x9 : Reg) ↦ᵣ s1old) **
     ((.x18 : Reg) ↦ᵣ s2old) ** ((.x19 : Reg) ↦ᵣ s3old) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x11 : Reg) ↦ᵣ listLen) ** ((.x12 : Reg) ↦ᵣ a2Old) ** ((.x5 : Reg) ↦ᵣ t0) **
     ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) ** ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) **
     ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion hdrBase listBytes ** memOwn spF ** memOwn (spF + 8) ** memOwn (spF + 16) **
     memOwn (spF + 24) ** memOwn (spF + 32) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact hExtra | apply pcFree_sepConj) h0L
  -- [1] SD sp, ra, 0
  have h1 := sd_spec_gen_own_within .x2 .x1 spF raSaved (0 : BitVec 12) (HB + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, show spF + 0 = spF from by bv_omega,
    show (HB + 4) + 4 = HB + 8 from by bv_omega] at h1
  have h1L := cpsTripleWithin_extend_code mem1 h1
  have h1F := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ s0old) ** ((.x9 : Reg) ↦ᵣ s1old) ** ((.x18 : Reg) ↦ᵣ s2old) **
     ((.x19 : Reg) ↦ᵣ s3old) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ listLen) **
     ((.x12 : Reg) ↦ᵣ a2Old) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) **
     ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion hdrBase listBytes ** memOwn (spF + 8) **
     memOwn (spF + 16) ** memOwn (spF + 24) ** memOwn (spF + 32) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact hExtra | apply pcFree_sepConj) h1L
  -- [2] SD sp, s0, 8
  have h2 := sd_spec_gen_own_within .x2 .x8 spF s0old (8 : BitVec 12) (HB + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show (HB + 8) + 4 = HB + 12 from by bv_omega] at h2
  have h2L := cpsTripleWithin_extend_code mem2 h2
  have h2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x9 : Reg) ↦ᵣ s1old) ** ((.x18 : Reg) ↦ᵣ s2old) **
     ((.x19 : Reg) ↦ᵣ s3old) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ listLen) **
     ((.x12 : Reg) ↦ᵣ a2Old) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) **
     ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion hdrBase listBytes ** (spF ↦ₘ raSaved) **
     memOwn (spF + 16) ** memOwn (spF + 24) ** memOwn (spF + 32) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h2L
  -- [3] SD sp, s1, 16
  have h3 := sd_spec_gen_own_within .x2 .x9 spF s1old (16 : BitVec 12) (HB + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show (HB + 12) + 4 = HB + 16 from by bv_omega] at h3
  have h3L := cpsTripleWithin_extend_code mem3 h3
  have h3F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0old) ** ((.x18 : Reg) ↦ᵣ s2old) **
     ((.x19 : Reg) ↦ᵣ s3old) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ listLen) **
     ((.x12 : Reg) ↦ᵣ a2Old) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) **
     ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion hdrBase listBytes ** (spF ↦ₘ raSaved) **
     ((spF + 8) ↦ₘ s0old) ** memOwn (spF + 24) ** memOwn (spF + 32) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h3L
  -- [4] SD sp, s2, 24
  have h4 := sd_spec_gen_own_within .x2 .x18 spF s2old (24 : BitVec 12) (HB + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show (HB + 16) + 4 = HB + 20 from by bv_omega] at h4
  have h4L := cpsTripleWithin_extend_code mem4 h4
  have h4F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0old) ** ((.x9 : Reg) ↦ᵣ s1old) **
     ((.x19 : Reg) ↦ᵣ s3old) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ listLen) **
     ((.x12 : Reg) ↦ᵣ a2Old) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) **
     ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion hdrBase listBytes ** (spF ↦ₘ raSaved) **
     ((spF + 8) ↦ₘ s0old) ** ((spF + 16) ↦ₘ s1old) ** memOwn (spF + 32) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h4L
  -- [5] SD sp, s3, 32
  have h5 := sd_spec_gen_own_within .x2 .x19 spF s3old (32 : BitVec 12) (HB + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show (HB + 20) + 4 = HB + 24 from by bv_omega] at h5
  have h5L := cpsTripleWithin_extend_code mem5 h5
  have h5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0old) ** ((.x9 : Reg) ↦ᵣ s1old) **
     ((.x18 : Reg) ↦ᵣ s2old) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ listLen) **
     ((.x12 : Reg) ↦ᵣ a2Old) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) **
     ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion hdrBase listBytes ** (spF ↦ₘ raSaved) **
     ((spF + 8) ↦ₘ s0old) ** ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h5L
  -- [6] MV s0, a0  (x8 ← x10 = ptr)
  have h6 := mv_spec_gen_within .x8 .x10 ptr s0old (HB + 24) (by decide)
  rw [show (HB + 24) + 4 = HB + 28 from by bv_omega] at h6
  have h6L := cpsTripleWithin_extend_code mem6 h6
  have h6F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spF) ** ((.x1 : Reg) ↦ᵣ raSaved) ** ((.x9 : Reg) ↦ᵣ s1old) ** ((.x18 : Reg) ↦ᵣ s2old) **
     ((.x19 : Reg) ↦ᵣ s3old) ** ((.x11 : Reg) ↦ᵣ listLen) ** ((.x12 : Reg) ↦ᵣ a2Old) **
     ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) ** ((.x28 : Reg) ↦ᵣ t3) **
     ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion hdrBase listBytes ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
     ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h6L
  -- [7] MV s2, a2  (x18 ← x12 = a2Old)
  have h7 := mv_spec_gen_within .x18 .x12 a2Old s2old (HB + 28) (by decide)
  rw [show (HB + 28) + 4 = HB + 32 from by bv_omega] at h7
  have h7L := cpsTripleWithin_extend_code mem7 h7
  have h7F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spF) ** ((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ s1old) **
     ((.x19 : Reg) ↦ᵣ s3old) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ listLen) **
     ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) ** ((.x28 : Reg) ↦ᵣ t3) **
     ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion hdrBase listBytes ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
     ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h7L
  -- chain the front.
  have hf01 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h0F h1F
  have hf012 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hf01 h2F
  have hf0123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hf012 h3F
  have hf4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hf0123 h4F
  have hf5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hf4 h5F
  have hf6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hf5 h6F
  have hfront := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hf6 h7F
  -- ===== walk_init call (HB + 32 → HB + 36) =====
  have hspec := rlp_walk_init_spec_within WIB hdrBase (HB + 36) listLen a2Old t0 t1 t2 t3 t4 t5 t6
    listBytes listOff hsalign hoff hover hvalid hll_len hll_over hll_valid
  -- frame the preserved caller state (x2/x8/x18/x9/x19 + stack + Extra).
  have hspecF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) ** ((.x18 : Reg) ↦ᵣ a2Old) **
     ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
     ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) hspec
  -- re-base the callee-leaf triple onto fullCode and land at the aligned return.
  have hadapter := hedCall_walkInit_slot8 (n := 81) raSaved
    (Prest := ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ listLen) ** ((.x12 : Reg) ↦ᵣ a2Old) **
      ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) ** ((.x28 : Reg) ↦ᵣ t3) **
      ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x18 : Reg) ↦ᵣ a2Old) ** ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) ** (spF ↦ₘ raSaved) **
      ((spF + 8) ↦ₘ s0old) ** ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj)
    (by
      rw [show (HB + 32 + 4 : Word) = HB + 36 from by bv_omega]
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x) hspecF)
  rw [show (HB + 32 + 4 : Word) = HB + 36 from by bv_omega] at hadapter
  -- glue front ;; call.
  have hfc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hfront
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x) hadapter
      (P' := ((.x1 : Reg) ↦ᵣ raSaved) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ listLen) **
        ((.x12 : Reg) ↦ᵣ a2Old) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) ** ((.x7 : Reg) ↦ᵣ t2) **
        ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) ** ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) **
        ((.x8 : Reg) ↦ᵣ ptr) ** ((.x18 : Reg) ↦ᵣ a2Old) ** ((.x9 : Reg) ↦ᵣ s1old) **
        ((.x19 : Reg) ↦ᵣ s3old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) ** ((spF + 16) ↦ₘ s1old) **
        ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra))
  -- ===== dispatch: BNE x12, x0  then (ok) MV s1 ; MV s3  (HB + 36 → HB + 48 / HB + 664) =====
  -- ok continuation: x12 = 0 (short/long success)
  have hokc : cpsBranchWithin 3 (HB + 36) fullCode
      (fun h => ∃ ic : Word,
        (((.x10 : Reg) ↦ᵣ ic) ** ((.x11 : Reg) ↦ᵣ (ptr + listLen)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
          bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
          ((.x18 : Reg) ↦ᵣ a2Old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
          ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra) h)
      (HB + 664) (hedPrologueFail hdrBase a2Old spF raSaved s0old s1old s2old s3old listBytes listOff Extra)
      (HB + 48) (hedPrologueOk hdrBase a2Old spF raSaved s0old s1old s2old s3old listLen listBytes listOff Extra) := by
    refine cpsBranchWithin_exists_pre (fun ic => ?_)
    have hbne := bne_spec_gen_within .x12 .x0 (628 : BitVec 13) (0 : Word) (0 : Word) (HB + 36)
    rw [show (HB + 36) + 4 = HB + 40 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code mem9 hbne
    have hfall := cpsBranchWithin_ntakenStripPure2 hbneL (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt; exact absurd rfl ((sepConj_pure_right _).1 hpure).2)
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ ic) ** ((.x11 : Reg) ↦ᵣ (ptr + listLen)) ** ((.x9 : Reg) ↦ᵣ s1old) **
       ((.x19 : Reg) ↦ᵣ s3old) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
       bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
       ((.x18 : Reg) ↦ᵣ a2Old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
       ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) hfall
    have hmv9 := mv_spec_gen_within .x9 .x11 (ptr + listLen) s1old (HB + 40) (by decide)
    rw [show (HB + 40) + 4 = HB + 44 from by bv_omega] at hmv9
    have hmv9L := cpsTripleWithin_extend_code mem10 hmv9
    have hmv9F := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ ic) **
       ((.x19 : Reg) ↦ᵣ s3old) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
       bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
       ((.x18 : Reg) ↦ᵣ a2Old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
       ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) hmv9L
    have hmv19 := mv_spec_gen_within .x19 .x10 ic s3old (HB + 44) (by decide)
    rw [show (HB + 44) + 4 = HB + 48 from by bv_omega] at hmv19
    have hmv19L := cpsTripleWithin_extend_code mem11 hmv19
    have hmv19F := cpsTripleWithin_frameR
      (((.x9 : Reg) ↦ᵣ (ptr + listLen)) ** ((.x11 : Reg) ↦ᵣ (ptr + listLen)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
       bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
       ((.x18 : Reg) ↦ᵣ a2Old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
       ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) hmv19L
    have hc1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hfallF hmv9F
    have hc2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hc1 hmv19F
    have hout : cpsTripleWithin 3 (HB + 36) (HB + 48) fullCode
        (((.x10 : Reg) ↦ᵣ ic) ** ((.x11 : Reg) ↦ᵣ (ptr + listLen)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
          bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
          ((.x18 : Reg) ↦ᵣ a2Old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
          ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
        (hedPrologueOk hdrBase a2Old spF raSaved s0old s1old s2old s3old listLen listBytes listOff Extra) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hc2
      have hq' : (((.x10 : Reg) ↦ᵣ ic) ** ((.x11 : Reg) ↦ᵣ (ptr + listLen)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x9 : Reg) ↦ᵣ (ptr + listLen)) ** ((.x19 : Reg) ↦ᵣ ic) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** ((.x1 : Reg) ↦ᵣ (HB + 36)) ** bytesRegion hdrBase listBytes **
          ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) ** ((.x18 : Reg) ↦ᵣ a2Old) **
          (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) ** ((spF + 16) ↦ₘ s1old) **
          ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra) h := by xperm_hyp hq
      have hq2 := sepConj_mono (regIs_implies_regOwn .x10)
        (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
          (fun _ x => x))) h hq'
      show hedPrologueOk hdrBase a2Old spF raSaved s0old s1old s2old s3old listLen listBytes listOff Extra h
      unfold hedPrologueOk hedStackFrame
      exact ⟨ic, by xperm_hyp hq2⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right (HB + 664)
        (hedPrologueFail hdrBase a2Old spF raSaved s0old s1old s2old s3old listBytes listOff Extra) hout)
  -- fail continuation: x12 = st ≠ 0 (any reject)
  have hfailc : cpsBranchWithin 3 (HB + 36) fullCode
      (fun h => ∃ st v10 v11 : Word,
        ((((.x12 : Reg) ↦ᵣ st) ** ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
          ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
          bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
          ((.x18 : Reg) ↦ᵣ a2Old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
          ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra) **
         ⌜st ≠ (0 : Word)⌝) h)
      (HB + 664) (hedPrologueFail hdrBase a2Old spF raSaved s0old s1old s2old s3old listBytes listOff Extra)
      (HB + 48) (hedPrologueOk hdrBase a2Old spF raSaved s0old s1old s2old s3old listLen listBytes listOff Extra) := by
    refine cpsBranchWithin_exists_pre (fun st => ?_)
    refine cpsBranchWithin_exists_pre (fun v10 => ?_)
    refine cpsBranchWithin_exists_pre (fun v11 => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hst => ?_)
    have hbne := bne_spec_gen_within .x12 .x0 (628 : BitVec 13) st (0 : Word) (HB + 36)
    rw [show (HB + 36) + signExtend13 (628 : BitVec 13) = HB + 664 from by
      rw [show signExtend13 (628 : BitVec 13) = (628 : Word) from by decide]; bv_omega,
      show (HB + 36) + 4 = HB + 40 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code mem9 hbne
    have htk := cpsBranchWithin_takenStripPure2 hbneL (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf; exact hst ((sepConj_pure_right _).1 hpure).2)
    have htkF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x9 : Reg) ↦ᵣ s1old) **
       ((.x19 : Reg) ↦ᵣ s3old) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
       bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
       ((.x18 : Reg) ↦ᵣ a2Old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
       ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) htk
    have hout : cpsTripleWithin 1 (HB + 36) (HB + 664) fullCode
        (((.x12 : Reg) ↦ᵣ st) ** ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
          ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
          bytesRegion hdrBase listBytes ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) **
          ((.x18 : Reg) ↦ᵣ a2Old) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) **
          ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra)
        (hedPrologueFail hdrBase a2Old spF raSaved s0old s1old s2old s3old listBytes listOff Extra) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htkF
      have hq' : (((.x12 : Reg) ↦ᵣ st) ** ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
          ((.x8 : Reg) ↦ᵣ ptr) ** ((.x18 : Reg) ↦ᵣ a2Old) ** ((.x2 : Reg) ↦ᵣ spF) **
          ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) ** regOwn .x5 ** regOwn .x6 **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (HB + 36)) ** bytesRegion hdrBase listBytes **
          (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0old) ** ((spF + 16) ↦ₘ s1old) **
          ((spF + 24) ↦ₘ s2old) ** ((spF + 32) ↦ₘ s3old) ** Extra) h := by xperm_hyp hq
      have hq2 := sepConj_mono (regIs_implies_regOwn .x12)
        (sepConj_mono (regIs_implies_regOwn .x10) (sepConj_mono (regIs_implies_regOwn .x11)
          (fun _ x => x))) h hq'
      show hedPrologueFail hdrBase a2Old spF raSaved s0old s1old s2old s3old listBytes listOff Extra h
      unfold hedPrologueFail hedStackFrame
      xperm_hyp hq2
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_left (HB + 48)
        (hedPrologueOk hdrBase a2Old spF raSaved s0old s1old s2old s3old listLen listBytes listOff Extra) hout)
  -- fold the nine walk_init arms into ok ∨ fail
  have hdisp : cpsBranchWithin 3 (HB + 36) fullCode
      (hedWalkInitPost hdrBase (HB + 36) listLen listBytes listOff hoff **
        (((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) ** ((.x18 : Reg) ↦ᵣ a2Old) **
          ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) ** (spF ↦ₘ raSaved) **
          ((spF + 8) ↦ₘ s0old) ** ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) **
          ((spF + 32) ↦ₘ s3old) ** Extra))
      (HB + 664) (hedPrologueFail hdrBase a2Old spF raSaved s0old s1old s2old s3old listBytes listOff Extra)
      (HB + 48) (hedPrologueOk hdrBase a2Old spF raSaved s0old s1old s2old s3old listLen listBytes listOff Extra) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x)
      (cpsBranchWithin_pre_or hokc hfailc)
    unfold hedWalkInitPost at hp
    obtain ⟨g1, g2, gd, gu, hWF9, hFRM⟩ := hp
    obtain ⟨k1, k2, kd, ku, hWF, hDisj⟩ := hWF9
    have rebuild : ∀ (arm : Assertion), arm k2 →
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (HB + 36)) **
            bytesRegion hdrBase listBytes) ** arm) **
          (((.x2 : Reg) ↦ᵣ spF) ** ((.x8 : Reg) ↦ᵣ ptr) ** ((.x18 : Reg) ↦ᵣ a2Old) **
            ((.x9 : Reg) ↦ᵣ s1old) ** ((.x19 : Reg) ↦ᵣ s3old) ** (spF ↦ₘ raSaved) **
            ((spF + 8) ↦ₘ s0old) ** ((spF + 16) ↦ₘ s1old) ** ((spF + 24) ↦ₘ s2old) **
            ((spF + 32) ↦ₘ s3old) ** Extra)) h :=
      fun arm ha => ⟨g1, g2, gd, gu, ⟨k1, k2, kd, ku, hWF, ha⟩, hFRM⟩
    rcases hDisj with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a1)
      exact Or.inr ⟨(2 : Word), ptr, (0 : Word),
        (sepConj_pure_right _).2 ⟨by xperm_hyp hR, by decide⟩⟩
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a2)
      exact Or.inr ⟨(1 : Word), ptr, ptr + listLen,
        (sepConj_pure_right _).2 ⟨by xperm_hyp hR, by decide⟩⟩
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a3)
      exact Or.inl ⟨ptr + signExtend12 (1 : BitVec 12), by xperm_hyp hR⟩
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a4)
      exact Or.inr ⟨(3 : Word), ptr, ptr + listLen,
        (sepConj_pure_right _).2 ⟨by xperm_hyp hR, by decide⟩⟩
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a5)
      exact Or.inr ⟨(4 : Word), ptr, ptr + listLen,
        (sepConj_pure_right _).2 ⟨by xperm_hyp hR, by decide⟩⟩
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a6)
      exact Or.inr ⟨(5 : Word), ptr, ptr + listLen,
        (sepConj_pure_right _).2 ⟨by xperm_hyp hR, by decide⟩⟩
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a7)
      exact Or.inr ⟨(6 : Word), ptr, ptr + listLen,
        (sepConj_pure_right _).2 ⟨by xperm_hyp hR, by decide⟩⟩
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a8)
      exact Or.inr ⟨(7 : Word), ptr, ptr + listLen,
        (sepConj_pure_right _).2 ⟨by xperm_hyp hR, by decide⟩⟩
    · have hR := rebuild _ (sepConj_strip_pure_end3 _ a9)
      exact Or.inl ⟨ptr + (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)),
        by xperm_hyp hR⟩
  -- ===== assemble: front ;; call ;; dispatch =====
  have hbody := cpsTripleWithin_seq_branch_same_cr hfc hdisp
  refine cpsBranchWithin_mono_nSteps (by omega)
    (cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x) hbody)

#print axioms hedPrologue

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
