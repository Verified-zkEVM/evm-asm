/-
  EvmAsm.Evm64.Terminating.RevertSpec

  Composition of the standalone (`depthAware = false`) `REVERT` (0xfd)
  return-data descriptor window into a public `cpsTripleWithin` witness.

  REVERT is a near-clone of `RETURN` (0xf3): the emitted tail
  (`Codegen.Programs.NoopHalt.returnRevertTail 2 <rollbackAsm> false`) reuses the
  SAME `0xa0010000` return-data descriptor window and the SAME shared halt core
  (`dispatchHaltRet 2`).  It differs from RETURN in exactly three ways:

  * **No `system_call_mode` capture block.**  That block is `kind == 1` (RETURN)
    only, so REVERT's tail has *no* capture-skip and hence *no*
    `system_call_mode = 0` gating precondition — the descriptor window starts
    immediately after the `ld x14,0(x12); ld x15,32(x12)` prologue.
  * **The kind store writes `2`** (`li x17,2; sd x17,32(x16)`) instead of `1`.
  * **Five straight-line rollback env-cell stores** sit between the kind store
    and the halt core (`ld x17,456(x20); sd x17,448(x20); sd x0,464(x20);
    ld x17,480(x20); sd x17,472(x20)`), restoring the persistent/transient log
    lengths + checkpoint on revert.  These are `LD`/`SD` on `x20 + offset`,
    disjoint from the `0xa0010000` descriptor region, composed straight-line.

  The window loop closures (`ReturnWindowLoopSpec`), the offset-`SD` primitive
  (`bytesRegion_sd_off_within`), the descriptor content/clamp models
  (`returnDescZeroed`/`returnClamp`/`returnClamp32`, reused from `ReturnSpec`),
  and the halt core (`evm_return_halt_spec_within`, `ReturnHaltSpec`) are all
  reused verbatim — only the code layout (no capture block → every offset shifts
  down by 80 bytes / 20 instructions from RETURN), the kind-store value, and the
  appended rollback differ.

  ## Coverage boundary (READ THIS)

  * The `preBody` memory-gas glue (with its `.exit_outofgas` branch) is a
    decision-1 TCB item and stays OUTSIDE this triple — the triple is stated
    from the framed post-gas entry `hbase`.
  * Unlike RETURN, there is NO `system_call_mode = 0` precondition (no capture
    block); the triple is unconditional over the descriptor window modulo the
    memory-gas TCB boundary and the evm_memory well-formedness domain hyps
    (`hOff`/`hOff32` etc., shared verbatim with RETURN).

  Kernel-checkable throughout (classical-3 only): no `native_decide` /
  `bv_decide`.
-/

import EvmAsm.Evm64.Terminating.ReturnSpec

namespace EvmAsm.Evm64
namespace Terminating

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves (as in `ReturnSpec`). -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- **The verified `Program` image of `returnRevertTail 2 <rollbackAsm> false`'s
    `.Lrr_halt_2` path.**  61 instructions from the post-gas handler entry through
    the descriptor window, the kind store (`kind = 2`), the five rollback env-cell
    stores, and the shared halt core, parameterised by the linker `la` immediate
    pairs:

    * `hiMem`/`loMem`, `hiMem2`/`loMem2` — the two `la x17, evm_memory`;
    * `hi2`/`lo2`, `hi1`/`lo1` — the halt core's `la evm_halt_flag` /
      `la .Ldispatch_resume`. -/
def revertTailProg
    (hiMem : BitVec 20) (loMem : BitVec 12)
    (hiMem2 : BitVec 20) (loMem2 : BitVec 12)
    (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12) : Program :=
  [ -- prologue: read offset/size off the stack scratch (x12)
    .LD .x14 .x12 0,                        -- 0
    .LD .x15 .x12 32,                       -- 1
    -- header + descriptor-body zeroing (no capture block: kind ≠ 1)
    .LI .x16 returnDescBase,                 -- 2
    .SD .x16 .x0 0,                          -- 3  header dword 0
    .SD .x16 .x0 8,                          -- 4  header dword 1
    .SD .x16 .x0 16,                         -- 5  header dword 2
    .SD .x16 .x0 24,                         -- 6  header dword 3
    .ADDI .x19 .x16 72,                      -- 7
    .LI .x21 22,                             -- 8
    -- zero loop (returnZeroLoop, idx 9..13)
    .BEQ .x21 .x0 (BitVec.ofNat 13 20),      -- 9
    .SD .x19 .x0 0,                          -- 10
    .ADDI .x19 .x19 8,                       -- 11
    .ADDI .x21 .x21 (-1 : BitVec 12),        -- 12
    .JAL .x0 (-16 : BitVec 21),              -- 13
    -- clamp size to 176
    .MV .x21 .x15,                           -- 14
    .LI .x22 176,                            -- 15
    .BGEU .x22 .x21 (BitVec.ofNat 13 8),     -- 16  → label3 (idx 18)
    .MV .x21 .x22,                           -- 17
    -- label3: size / clamped stores
    .SD .x16 .x15 64,                        -- 18  size  @ +64  (dword 8)
    .SD .x16 .x21 248,                       -- 19  clamp @ +248 (dword 31)
    .AUIPC .x17 hiMem,                       -- 20  la x17, evm_memory
    .ADDI .x17 .x17 loMem,                   -- 21
    .ADD .x17 .x17 .x14,                     -- 22
    .ADDI .x19 .x16 72,                      -- 23
    .MV .x22 .x21,                           -- 24
    -- copy loop 1 (returnCopyLoop, idx 25..31): dest +72, n = clamped
    .BEQ .x22 .x0 (BitVec.ofNat 13 28),      -- 25
    .LBU .x23 .x17 0,                        -- 26
    .SB .x19 .x23 0,                         -- 27
    .ADDI .x17 .x17 1,                       -- 28
    .ADDI .x19 .x19 1,                       -- 29
    .ADDI .x22 .x22 (-1 : BitVec 12),        -- 30
    .JAL .x0 (-24 : BitVec 21),              -- 31
    -- label5: clamp size to 32 for the first-32 prefix copy
    .AUIPC .x17 hiMem2,                      -- 32  la x17, evm_memory
    .ADDI .x17 .x17 loMem2,                  -- 33
    .ADD .x17 .x17 .x14,                     -- 34
    .MV .x22 .x15,                           -- 35
    .LI .x21 32,                             -- 36
    .BGEU .x21 .x22 (BitVec.ofNat 13 8),     -- 37  → label6 (idx 39)
    .MV .x22 .x21,                           -- 38
    -- label6: reset dest to descriptor base
    .MV .x19 .x16,                           -- 39
    -- copy loop 2 (returnCopyLoop, idx 40..46): dest +0, n = min(size,32)
    .BEQ .x22 .x0 (BitVec.ofNat 13 28),      -- 40
    .LBU .x23 .x17 0,                        -- 41
    .SB .x19 .x23 0,                         -- 42
    .ADDI .x17 .x17 1,                       -- 43
    .ADDI .x19 .x19 1,                       -- 44
    .ADDI .x22 .x22 (-1 : BitVec 12),        -- 45
    .JAL .x0 (-24 : BitVec 21),              -- 46
    -- label8: kind store (kind = 2 @ +32)
    .LI .x17 2,                              -- 47
    .SD .x16 .x17 32,                        -- 48
    -- rollback (5 env-cell stores on x20, idx 49..53)
    .LD .x17 .x20 456,                       -- 49
    .SD .x20 .x17 448,                       -- 50
    .SD .x20 .x0 464,                        -- 51
    .LD .x17 .x20 480,                       -- 52
    .SD .x20 .x17 472,                       -- 53
    -- halt core (evm_return_halt hi2 lo2 hi1 lo1, idx 54..60)
    .LI .x5 2,                               -- 54
    .AUIPC .x6 hi2,                          -- 55
    .ADDI .x6 .x6 lo2,                       -- 56
    .SD .x6 .x5 0,                           -- 57
    .AUIPC .x1 hi1,                          -- 58
    .ADDI .x1 .x1 lo1,                       -- 59
    .JALR .x0 .x1 0 ]                        -- 60

/-- Byte fidelity: the modelled tail is exactly 61 instructions. -/
@[simp] theorem revertTailProg_length
    (hiMem : BitVec 20) (loMem : BitVec 12) (hiMem2 : BitVec 20) (loMem2 : BitVec 12)
    (hi2 : BitVec 20) (lo2 : BitVec 12) (hi1 : BitVec 20) (lo1 : BitVec 12) :
    (revertTailProg hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1).length = 61 := rfl

/-! ## Composition -/

section Compose

variable (hiMem : BitVec 20) (loMem : BitVec 12) (hiMem2 : BitVec 20) (loMem2 : BitVec 12)
  (hi2 : BitVec 20) (lo2 : BitVec 12) (hi1 : BitVec 20) (lo1 : BitVec 12)

/-- Abbreviation for the full tail program at the current immediate params. -/
local notation "PROG" =>
  revertTailProg hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1

/-- Abbreviation for the full-tail CodeReq at base `hbase`. -/
local notation "TAILCR" hbase => CodeReq.ofProg hbase PROG

/-- **Prologue segment** (`hbase → hbase + 8`).  Reads the stack-scratch
    `offset`/`size` into `x14`/`x15`.  No `system_call_mode` capture block
    (kind ≠ 1), so the descriptor window follows immediately. -/
theorem revert_seg_prologue (hbase p off size x14o x15o : Word) :
    cpsTripleWithin 2 hbase (hbase + 8)
      (TAILCR hbase)
      ((.x12 ↦ᵣ p) ** (.x14 ↦ᵣ x14o) ** (.x15 ↦ᵣ x15o) **
        ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size))
      ((.x12 ↦ᵣ p) ** (.x14 ↦ᵣ off) ** (.x15 ↦ᵣ size) **
        ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size)) := by
  -- idx 0: ld x14, 0(x12)
  have t0 := ld_spec_within .x14 .x12 p x14o off 0 hbase (by nofun)
  have t0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 0 hbase
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) t0
  have t0f := cpsTripleWithin_frameR
    (((.x15 : Reg) ↦ᵣ x15o) ** ((p + signExtend12 32) ↦ₘ size)) (by pcFree) t0e
  -- idx 1: ld x15, 32(x12)
  have t1 := ld_spec_within .x15 .x12 p x15o size 32 (hbase + 4) (by nofun)
  rw [show (hbase + 4 : Word) + 4 = hbase + 8 from by bv_omega] at t1
  have t1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 1 (hbase + 4)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) t1
  have t1f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ off) ** ((p + signExtend12 0) ↦ₘ off)) (by pcFree) t1e
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) t0f t1f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c01)

/-- **Header + descriptor-body zeroing segment** (`hbase+8 → hbase+56`).  Loads
    the descriptor base into `x16`, zeroes the four header dwords, sets up the
    body pointer/count, and runs the 22-dword zeroing loop. -/
theorem revert_seg_header (hbase : Word) (x16o x19o x21o : Word)
    (descInit : List (BitVec 8)) (hlen : descInit.length = 256) :
    cpsTripleWithin 118 (hbase + 8) (hbase + 56)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ x16o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) **
        bytesRegion returnDescBase descInit)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0 + 22)))) **
        ((.x21 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion returnDescBase (returnDescZeroed descInit)) := by
  -- idx 2: li x16, descBase
  have s0 := li_spec_within .x16 x16o returnDescBase (hbase + 8) (by nofun)
  rw [show (hbase + 8 : Word) + 4 = hbase + 12 from by bv_omega] at s0
  have s0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 2 (hbase + 8)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) s0
  have s0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) **
      bytesRegion returnDescBase descInit) (by pcFreeR) s0e
  -- idx 3..6: sd x0 at 0/8/16/24 (header dwords)
  have hd0 := bytesRegion_sd_off_within .x16 .x0 returnDescBase (0 : Word) (hbase + 12)
    descInit 0 (0 : BitVec 12) (by decide) (by rw [hlen]; omega)
  rw [show (hbase + 12 : Word) + 4 = hbase + 16 from by bv_omega] at hd0
  have hd0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 3 (hbase + 12)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) hd0
  have hd0f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o)) (by pcFreeR) hd0e
  have hd1 := bytesRegion_sd_off_within .x16 .x0 returnDescBase (0 : Word) (hbase + 16)
    (setBytes descInit 0 (dwordBytes (0 : Word))) 1 (8 : BitVec 12) (by decide)
    (by rw [length_setBytes, hlen]; omega)
  rw [show (hbase + 16 : Word) + 4 = hbase + 20 from by bv_omega] at hd1
  have hd1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 4 (hbase + 16)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) hd1
  have hd1f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o)) (by pcFreeR) hd1e
  have hd2 := bytesRegion_sd_off_within .x16 .x0 returnDescBase (0 : Word) (hbase + 20)
    (setBytes (setBytes descInit 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word))) 2
    (16 : BitVec 12) (by decide) (by rw [length_setBytes, length_setBytes, hlen]; omega)
  rw [show (hbase + 20 : Word) + 4 = hbase + 24 from by bv_omega] at hd2
  have hd2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 5 (hbase + 20)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) hd2
  have hd2f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o)) (by pcFreeR) hd2e
  have hd3 := bytesRegion_sd_off_within .x16 .x0 returnDescBase (0 : Word) (hbase + 24)
    (setBytes (setBytes (setBytes descInit 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word)))
      16 (dwordBytes (0 : Word))) 3 (24 : BitVec 12) (by decide)
    (by rw [length_setBytes, length_setBytes, length_setBytes, hlen]; omega)
  rw [show (hbase + 24 : Word) + 4 = hbase + 28 from by bv_omega] at hd3
  have hd3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 6 (hbase + 24)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) hd3
  have hd3f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o)) (by pcFreeR) hd3e
  -- name the header-zeroed region (= zeroDwords descInit 0 4)
  set R0 := setBytes (setBytes (setBytes (setBytes descInit 0 (dwordBytes (0 : Word))) 8
    (dwordBytes (0 : Word))) 16 (dwordBytes (0 : Word))) 24 (dwordBytes (0 : Word)) with hR0
  -- idx 7: addi x19, x16, 72  →  x19 = descBase + 8*9
  have s1 := addi_spec_gen_within .x19 .x16 x19o returnDescBase (72 : BitVec 12)
    (hbase + 28) (by nofun)
  rw [show returnDescBase + signExtend12 (72 : BitVec 12)
        = returnDescBase + BitVec.ofNat 64 (8 * (9 + 0)) from by decide] at s1
  rw [show (hbase + 28 : Word) + 4 = hbase + 32 from by bv_omega] at s1
  have s1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 7 (hbase + 28)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) s1
  have s1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x21 : Reg) ↦ᵣ x21o) ** bytesRegion returnDescBase R0)
    (by pcFreeR) s1e
  -- idx 8: li x21, 22
  have s2 := li_spec_within .x21 x21o (BitVec.ofNat 64 22) (hbase + 32) (by nofun)
  rw [show (hbase + 32 : Word) + 4 = hbase + 36 from by bv_omega] at s2
  have s2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 8 (hbase + 32)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) s2
  have s2f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0)))) **
      bytesRegion returnDescBase R0) (by pcFreeR) s2e
  -- idx 9..13: the zeroing loop (returnZeroLoop, embedded via ofProg_mono_sub)
  have hloop := returnZeroLoop_spec_within (hbase + 36) returnDescBase R0 9 22 0
    (by rw [hR0, length_setBytes, length_setBytes, length_setBytes, length_setBytes, hlen]; omega)
    (by rw [hR0, length_setBytes, length_setBytes, length_setBytes, length_setBytes, hlen]; omega)
  rw [show zeroDwords R0 9 0 = R0 from rfl,
      show (hbase + 36 : Word) + 20 = hbase + 56 from by bv_omega] at hloop
  have hloopE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 36) PROG returnZeroLoop 9
      (by bv_omega) (by rfl)
      (by simp only [revertTailProg_length, returnZeroLoop_length]; omega)
      (by simp only [revertTailProg_length]; decide)) hloop
  have hloopf := cpsTripleWithin_frameR ((.x16 : Reg) ↦ᵣ returnDescBase) (by pcFreeR) hloopE
  -- compose the eight straight-line steps + loop
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s0f hd0f
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 hd1f
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 hd2f
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 hd3f
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 s1f
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c4 s2f
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c5 hloopf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by
      simp only [returnDescZeroed]
      xperm_chunked hq) c6)

/-- **Size-clamp-to-176 segment** (`hbase+56 → hbase+72`).  `x21 := x15`,
    `x22 := 176`, then `bgeu x22,x21,3f` skips `mv x21,x22` when `x15 ≤ᵤ 176`. -/
theorem revert_seg_clamp176 (hbase : Word) (x15v x21o x22o : Word) :
    cpsTripleWithin 4 (hbase + 56) (hbase + 72)
      (TAILCR hbase)
      (((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o))
      (((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) **
        ((.x22 : Reg) ↦ᵣ (176 : Word))) := by
  -- idx 14: mv x21, x15
  have s0 := mv_spec_within .x21 .x15 x15v x21o (hbase + 56) (by nofun)
  rw [show (hbase + 56 : Word) + 4 = hbase + 60 from by bv_omega] at s0
  have s0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 14 (hbase + 56)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) s0
  have s0f := cpsTripleWithin_frameR ((.x22 : Reg) ↦ᵣ x22o) (by pcFree) s0e
  -- idx 15: li x22, 176
  have s1 := li_spec_within .x22 x22o (176 : Word) (hbase + 60) (by nofun)
  rw [show (hbase + 60 : Word) + 4 = hbase + 64 from by bv_omega] at s1
  have s1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 15 (hbase + 60)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) s1
  have s1f := cpsTripleWithin_frameR
    (((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x15v)) (by pcFree) s1e
  have pre01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s0f s1f
  -- idx 16: bgeu x22, x21, 3f
  have hb := bgeu_spec_gen_within .x22 .x21 (BitVec.ofNat 13 8) (176 : Word) x15v (hbase + 64)
  rw [show (hbase + 64 : Word) + signExtend13 (BitVec.ofNat 13 8) = hbase + 72 from by
        rw [show signExtend13 (BitVec.ofNat 13 8) = (8 : Word) from by decide]; bv_omega,
      show (hbase + 64 : Word) + 4 = hbase + 68 from by bv_omega] at hb
  have hbe := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 16 (hbase + 64)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) hb
  by_cases h : BitVec.ult (176 : Word) x15v
  · -- size > 176: bgeu NOT taken; execute mv x21, x22 (idx 17)
    have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact (((sepConj_pure_right _).1 hQ).2) h)
    have hntf := cpsTripleWithin_frameR ((.x15 : Reg) ↦ᵣ x15v) (by pcFree) hnt
    have s2 := mv_spec_within .x21 .x22 (176 : Word) x15v (hbase + 68) (by nofun)
    rw [show (hbase + 68 : Word) + 4 = hbase + 72 from by bv_omega] at s2
    have s2e := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 17 (hbase + 68)
        (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) s2
    have s2f := cpsTripleWithin_frameR ((.x15 : Reg) ↦ᵣ x15v) (by pcFree) s2e
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre01 hntf
    have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 s2f
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
        simp only [returnClamp, if_pos h]; xperm_hyp hq) c2)
  · -- size ≤ 176: bgeu taken; skip mv, land at label3
    have ht := cpsBranchWithin_takenStripPure2 hbe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd (((sepConj_pure_right _).1 hQ).2) h)
    have htf := cpsTripleWithin_frameR ((.x15 : Reg) ↦ᵣ x15v) (by pcFree) ht
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre01 htf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
        simp only [returnClamp, if_neg h]; xperm_hyp hq) c1)

/-- **Size/clamped stores + `evm_memory → descriptor+72` copy segment**
    (`hbase+72 → hbase+128`).  Stores `size@+64` and `clamped@+248`, points `x17`
    at `evm_memory+offset`, `x19` at `descriptor+72`, `x22 := clamped`, and runs
    the copy loop.  `hlaMem` reconstructs the first `la x17, evm_memory`. -/
theorem revert_seg_copy1 (hbase evmMemBase : Word)
    (x14v x15v x17o x19o x22o x23o : Word) (descInit memBytes : List (BitVec 8))
    (hDescLen : descInit.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hOff : x14v.toNat + (returnClamp x15v).toNat ≤ memBytes.length)
    (hlaMem : (hbase + (80 : Word)) + ((hiMem.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem = evmMemBase) :
    cpsTripleWithin (7 * (returnClamp x15v).toNat + 8) (hbase + 72) (hbase + 128)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
        ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) **
        ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
        bytesRegion returnDescBase (returnDescZeroed descInit) **
        bytesRegion evmMemBase memBytes)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
        ((.x16 : Reg) ↦ᵣ returnDescBase) **
        ((.x17 : Reg) ↦ᵣ (evmMemBase + BitVec.ofNat 64 (x14v.toNat + 0 + (returnClamp x15v).toNat))) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (72 + 0 + (returnClamp x15v).toNat))) **
        ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
        bytesRegion returnDescBase
          (copyIntoRegion
            (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v))
              248 (dwordBytes (returnClamp x15v))) memBytes 72 x14v.toNat (returnClamp x15v).toNat) **
        bytesRegion evmMemBase memBytes) := by
  have hReg256 : (returnDescZeroed descInit).length = 256 := by
    simp only [returnDescZeroed, zeroDwords_length, hDescLen]
  have hclamp := returnClamp_toNat_le x15v
  -- idx 18: sd x16, size, 64(x16)
  have d0 := bytesRegion_sd_off_within .x16 .x15 returnDescBase x15v (hbase + 72)
    (returnDescZeroed descInit) 8 (64 : BitVec 12) (by decide) (by rw [hReg256]; omega)
  rw [show (hbase + 72 : Word) + 4 = hbase + 76 from by bv_omega] at d0
  have d0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 18 (hbase + 72)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) d0
  have d0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x17 : Reg) ↦ᵣ x17o) **
      ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ x22o) **
      ((.x23 : Reg) ↦ᵣ x23o) ** bytesRegion evmMemBase memBytes) (by pcFreeR) d0e
  -- idx 19: sd x16, clamped, 248(x16)
  have d1 := bytesRegion_sd_off_within .x16 .x21 returnDescBase (returnClamp x15v) (hbase + 76)
    (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 31 (248 : BitVec 12) (by decide)
    (by rw [length_setBytes, hReg256])
  rw [show (hbase + 76 : Word) + 4 = hbase + 80 from by bv_omega] at d1
  have d1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 19 (hbase + 76)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) d1
  have d1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x17 : Reg) ↦ᵣ x17o) ** ((.x19 : Reg) ↦ᵣ x19o) ** ((.x22 : Reg) ↦ᵣ x22o) **
      ((.x23 : Reg) ↦ᵣ x23o) ** bytesRegion evmMemBase memBytes) (by pcFreeR) d1e
  -- idx 20: auipc x17, evm_memory (hi)
  have a0 := auipc_spec_within .x17 x17o hiMem (hbase + 80) (by nofun)
  rw [show (hbase + 80 : Word) + 4 = hbase + 84 from by bv_omega] at a0
  set memAuipc := (hbase + (80 : Word)) + ((hiMem.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    with hMemAuipc
  have a0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 20 (hbase + 80)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a0
  have a0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x19 : Reg) ↦ᵣ x19o) **
      ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a0e
  -- idx 21: addi x17, x17, lo  (→ evmMemBase)
  have a1 := addi_spec_same_within .x17 memAuipc loMem (hbase + 84) (by nofun)
  rw [hlaMem, show (hbase + 84 : Word) + 4 = hbase + 88 from by bv_omega] at a1
  have a1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 21 (hbase + 84)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a1
  have a1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x19 : Reg) ↦ᵣ x19o) **
      ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a1e
  -- idx 22: add x17, x17, x14  (→ evmMemBase + offset)
  have a2 := add_spec_rd_eq_rs1_within .x17 .x14 evmMemBase x14v (hbase + 88) (by nofun)
  rw [show (hbase + 88 : Word) + 4 = hbase + 92 from by bv_omega] at a2
  have a2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 22 (hbase + 88)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a2
  have a2f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
      ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ x22o) **
      ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a2e
  -- idx 23: addi x19, x16, 72  (→ descBase + 72)
  have a3 := addi_spec_gen_within .x19 .x16 x19o returnDescBase (72 : BitVec 12) (hbase + 92) (by nofun)
  rw [show returnDescBase + signExtend12 (72 : BitVec 12)
        = returnDescBase + BitVec.ofNat 64 (72 + 0) from by decide,
      show (hbase + 92 : Word) + 4 = hbase + 96 from by bv_omega] at a3
  have a3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 23 (hbase + 92)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a3
  have a3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) **
      ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a3e
  -- idx 24: mv x22, x21  (→ clamped)
  have a4 := mv_spec_within .x22 .x21 (returnClamp x15v) x22o (hbase + 96) (by nofun)
  rw [show (hbase + 96 : Word) + 4 = hbase + 100 from by bv_omega] at a4
  have a4e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 24 (hbase + 96)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a4
  have a4f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (72 + 0))) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a4e
  -- idx 25..31: the copy loop
  have hStoresLen : (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
      (dwordBytes (returnClamp x15v))).length = 256 := by
    rw [length_setBytes, length_setBytes, hReg256]
  have hloop := returnCopyLoop_spec_within (hbase + 100) evmMemBase returnDescBase memBytes
    (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
      (dwordBytes (returnClamp x15v))) x14v.toNat 72 (returnClamp x15v).toNat 0 x23o
    hSrcAlign (by decide) (by simpa using hOff) (by rw [hStoresLen]; omega) hSrcOver
    (by rw [hStoresLen]; decide)
    hSrcValid (fun k hk => returnDescBase_valid k (by rw [hStoresLen] at hk; exact hk))
  rw [show copyIntoRegion
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) memBytes 72 x14v.toNat 0
        = setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v)) from rfl,
      show BitVec.ofNat 64 (returnClamp x15v).toNat = returnClamp x15v from word_ofNat_toNat _,
      show evmMemBase + BitVec.ofNat 64 (x14v.toNat + 0) = evmMemBase + x14v from by
        rw [Nat.add_zero, word_ofNat_toNat],
      show (0 : Nat) + (returnClamp x15v).toNat = (returnClamp x15v).toNat from Nat.zero_add _,
      show (hbase + 100 : Word) + 28 = hbase + 128 from by bv_omega] at hloop
  have hloopE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 100) PROG returnCopyLoop 25
      (by bv_omega) (by rfl)
      (by simp only [revertTailProg_length, returnCopyLoop_length]; omega)
      (by simp only [revertTailProg_length]; decide)) hloop
  have hloopf := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
      ((.x21 : Reg) ↦ᵣ returnClamp x15v)) (by pcFreeR) hloopE
  -- compose
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) d0f d1f
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 a0f
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 a1f
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 a2f
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 a3f
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c4 a4f
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c5 hloopf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c6)

/-- **Second `la x17, evm_memory` + clamp-to-32 segment** (`hbase+128 →
    hbase+156`).  Re-points `x17` at `evm_memory+offset`, then
    `x22 := min(x15,32) = returnClamp32 x15`, `x21 := 32`, via `bgeu x21,x22,6f`.
    `hlaMem2` reconstructs the second `la x17, evm_memory`. -/
theorem revert_seg_clamp32 (hbase evmMemBase : Word)
    (x14v x15v x17o x21o x22o : Word)
    (hlaMem2 : (hbase + (128 : Word)) + ((hiMem2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem2 = evmMemBase) :
    cpsTripleWithin 7 (hbase + 128) (hbase + 156)
      (TAILCR hbase)
      (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o))
      (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
        ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) ** ((.x21 : Reg) ↦ᵣ (32 : Word)) **
        ((.x22 : Reg) ↦ᵣ returnClamp32 x15v)) := by
  -- idx 32: auipc x17
  have a0 := auipc_spec_within .x17 x17o hiMem2 (hbase + 128) (by nofun)
  rw [show (hbase + 128 : Word) + 4 = hbase + 132 from by bv_omega] at a0
  set memAuipc2 := (hbase + (128 : Word)) + ((hiMem2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    with hMemAuipc2
  have a0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 32 (hbase + 128)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a0
  have a0f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x21o) **
      ((.x22 : Reg) ↦ᵣ x22o)) (by pcFree) a0e
  -- idx 33: addi x17, x17, lo  (→ evmMemBase)
  have a1 := addi_spec_same_within .x17 memAuipc2 loMem2 (hbase + 132) (by nofun)
  rw [hlaMem2, show (hbase + 132 : Word) + 4 = hbase + 136 from by bv_omega] at a1
  have a1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 33 (hbase + 132)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a1
  have a1f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x21o) **
      ((.x22 : Reg) ↦ᵣ x22o)) (by pcFree) a1e
  -- idx 34: add x17, x17, x14
  have a2 := add_spec_rd_eq_rs1_within .x17 .x14 evmMemBase x14v (hbase + 136) (by nofun)
  rw [show (hbase + 136 : Word) + 4 = hbase + 140 from by bv_omega] at a2
  have a2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 34 (hbase + 136)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a2
  have a2f := cpsTripleWithin_frameR
    (((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o)) (by pcFree) a2e
  -- idx 35: mv x22, x15
  have a3 := mv_spec_within .x22 .x15 x15v x22o (hbase + 140) (by nofun)
  rw [show (hbase + 140 : Word) + 4 = hbase + 144 from by bv_omega] at a3
  have a3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 35 (hbase + 140)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a3
  have a3f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) ** ((.x21 : Reg) ↦ᵣ x21o))
    (by pcFree) a3e
  -- idx 36: li x21, 32
  have a4 := li_spec_within .x21 x21o (32 : Word) (hbase + 144) (by nofun)
  rw [show (hbase + 144 : Word) + 4 = hbase + 148 from by bv_omega] at a4
  have a4e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 36 (hbase + 144)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) a4
  have a4f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) **
      ((.x22 : Reg) ↦ᵣ x15v)) (by pcFree) a4e
  have pre0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) a0f a1f
  have pre1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre0 a2f
  have pre2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre1 a3f
  have pre3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre2 a4f
  -- idx 37: bgeu x21, x22, 6f
  have hb := bgeu_spec_gen_within .x21 .x22 (BitVec.ofNat 13 8) (32 : Word) x15v (hbase + 148)
  rw [show (hbase + 148 : Word) + signExtend13 (BitVec.ofNat 13 8) = hbase + 156 from by
        rw [show signExtend13 (BitVec.ofNat 13 8) = (8 : Word) from by decide]; bv_omega,
      show (hbase + 148 : Word) + 4 = hbase + 152 from by bv_omega] at hb
  have hbe := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 37 (hbase + 148)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) hb
  by_cases h : BitVec.ult (32 : Word) x15v
  · -- size > 32: bgeu NOT taken; mv x22, x21 (idx 38)
    have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact (((sepConj_pure_right _).1 hQ).2) h)
    have hntf := cpsTripleWithin_frameR
      (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)))
      (by pcFree) hnt
    have s2 := mv_spec_within .x22 .x21 (32 : Word) x15v (hbase + 152) (by nofun)
    rw [show (hbase + 152 : Word) + 4 = hbase + 156 from by bv_omega] at s2
    have s2e := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 38 (hbase + 152)
        (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) s2
    have s2f := cpsTripleWithin_frameR
      (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)))
      (by pcFree) s2e
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre3 hntf
    have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 s2f
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
        simp only [returnClamp32, if_pos h]; xperm_hyp hq) c2)
  · -- size ≤ 32: bgeu taken; land at label6
    have ht := cpsBranchWithin_takenStripPure2 hbe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd (((sepConj_pure_right _).1 hQ).2) h)
    have htf := cpsTripleWithin_frameR
      (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)))
      (by pcFree) ht
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre3 htf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
        simp only [returnClamp32, if_neg h]; xperm_hyp hq) c1)

/-- **First-32-byte prefix copy segment** (`hbase+156 → hbase+188`).  Resets
    `x19` to the descriptor base and copies `min(x15,32)` bytes of
    `evm_memory[offset..]` into `descriptor[0..]`. -/
theorem revert_seg_copy2 (hbase evmMemBase : Word)
    (x14v x15v x19o : Word) (descBytes memBytes : List (BitVec 8))
    (hDescLen : descBytes.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hOff32 : x14v.toNat + (returnClamp32 x15v).toNat ≤ memBytes.length) :
    cpsTripleWithin (7 * (returnClamp32 x15v).toNat + 2) (hbase + 156) (hbase + 188)
      (TAILCR hbase)
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
        ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) ** ((.x19 : Reg) ↦ᵣ x19o) **
        ((.x22 : Reg) ↦ᵣ returnClamp32 x15v) **
        bytesRegion returnDescBase descBytes ** bytesRegion evmMemBase memBytes) ** regOwn .x23)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
        ((.x17 : Reg) ↦ᵣ (evmMemBase + BitVec.ofNat 64 (x14v.toNat + 0 + (returnClamp32 x15v).toNat))) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 x15v).toNat)) **
        ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
        bytesRegion returnDescBase
          (copyIntoRegion descBytes memBytes 0 x14v.toNat (returnClamp32 x15v).toNat) **
        bytesRegion evmMemBase memBytes) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun x23o => ?_)
  -- idx 39: mv x19, x16
  have m0 := mv_spec_within .x19 .x16 returnDescBase x19o (hbase + 156) (by nofun)
  rw [show (hbase + 156 : Word) + 4 = hbase + 160 from by bv_omega] at m0
  have m0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 39 (hbase + 156)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) m0
  have m0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) **
      ((.x22 : Reg) ↦ᵣ returnClamp32 x15v) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase descBytes ** bytesRegion evmMemBase memBytes) (by pcFreeR) m0e
  -- idx 40..46: copy loop 2 (dest +0)
  have hloop := returnCopyLoop_spec_within (hbase + 160) evmMemBase returnDescBase memBytes
    descBytes x14v.toNat 0 (returnClamp32 x15v).toNat 0 x23o
    hSrcAlign (by decide) (by simpa using hOff32)
    (by have := returnClamp32_toNat_le x15v; rw [hDescLen]; omega) hSrcOver
    (by rw [hDescLen]; decide)
    hSrcValid (fun k hk => returnDescBase_valid k (by rw [hDescLen] at hk; exact hk))
  rw [show copyIntoRegion descBytes memBytes 0 x14v.toNat 0 = descBytes from rfl,
      show BitVec.ofNat 64 (returnClamp32 x15v).toNat = returnClamp32 x15v from word_ofNat_toNat _,
      show evmMemBase + BitVec.ofNat 64 (x14v.toNat + 0) = evmMemBase + x14v from by
        rw [Nat.add_zero, word_ofNat_toNat],
      show returnDescBase + BitVec.ofNat 64 (0 + 0) = returnDescBase from by decide,
      show (0 : Nat) + (returnClamp32 x15v).toNat = (returnClamp32 x15v).toNat from Nat.zero_add _,
      show (hbase + 160 : Word) + 28 = hbase + 188 from by bv_omega] at hloop
  have hloopE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 160) PROG returnCopyLoop 40
      (by bv_omega) (by rfl)
      (by simp only [revertTailProg_length, returnCopyLoop_length]; omega)
      (by simp only [revertTailProg_length]; decide)) hloop
  have hloopf := cpsTripleWithin_frameR ((.x16 : Reg) ↦ᵣ returnDescBase) (by pcFreeR) hloopE
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) m0f hloopf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c0)

/-- **Kind store + rollback + halt core segment** (`hbase+188 → resume &&& ~~~1`).
    Stores `kind = 2 @ +32`, runs the five straight-line rollback env-cell stores
    on `x20` (`env+448 := env+456`, `env+464 := 0`, `env+472 := env+480`), then
    the shared `dispatchHaltRet 2` halt core: sets `evm_halt_flag := 2`, points
    `x1` at `.Ldispatch_resume`, and `ret`s.  `hla2`/`hla1` reconstruct the halt
    core's two `la`s. -/
theorem revert_seg_kindrollbackhalt (hbase envBase flag resume : Word)
    (x17o v5 v6 v1 f0 c448 c456 c464 c472 c480 : Word) (descBytes : List (BitVec 8))
    (hDescLen : descBytes.length = 256)
    (hla2 : (hbase + 216 + 4) + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla1 : (hbase + 216 + 16) + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = resume) :
    cpsTripleWithin 14 (hbase + 188) (resume &&& ~~~1)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
        ((.x17 : Reg) ↦ᵣ x17o) ** ((.x20 : Reg) ↦ᵣ envBase) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
        ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
        ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
        ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
        ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
        ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
        bytesRegion returnDescBase descBytes)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
        ((.x17 : Reg) ↦ᵣ c480) ** ((.x20 : Reg) ↦ᵣ envBase) ** ((.x5 : Reg) ↦ᵣ (2 : Word)) **
        ((.x6 : Reg) ↦ᵣ flag) ** ((.x1 : Reg) ↦ᵣ resume) ** (flag ↦ₘ (2 : Word)) **
        ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c456) **
        ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
        ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ (0 : Word)) **
        ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c480) **
        ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
        bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (2 : Word)))) := by
  -- idx 47: li x17, 2
  have k0 := li_spec_within .x17 x17o (2 : Word) (hbase + 188) (by nofun)
  rw [show (hbase + 188 : Word) + 4 = hbase + 192 from by bv_omega] at k0
  have k0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 47 (hbase + 188)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) k0
  have k0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x20 : Reg) ↦ᵣ envBase) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase descBytes) (by pcFreeR) k0e
  -- idx 48: sd x16, kind, 32(x16)
  have k1 := bytesRegion_sd_off_within .x16 .x17 returnDescBase (2 : Word) (hbase + 192)
    descBytes 4 (32 : BitVec 12) (by decide) (by rw [hDescLen]; omega)
  rw [show (hbase + 192 : Word) + 4 = hbase + 196 from by bv_omega] at k1
  have k1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 48 (hbase + 192)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) k1
  have k1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ envBase) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480)) (by pcFreeR) k1e
  -- idx 49: ld x17, 456(x20)  (x17 := env+456)
  have r0 := ld_spec_within .x17 .x20 envBase (2 : Word) c456 (456 : BitVec 12) (hbase + 196) (by nofun)
  rw [show (hbase + 196 : Word) + 4 = hbase + 200 from by bv_omega] at r0
  have r0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 49 (hbase + 196)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) r0
  have r0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (2 : Word)))) (by pcFreeR) r0e
  -- idx 50: sd x17, 448(x20)  (env+448 := env+456)
  have r1 := sd_spec_within .x20 .x17 envBase c456 c448 (448 : BitVec 12) (hbase + 200)
  rw [show (hbase + 200 : Word) + 4 = hbase + 204 from by bv_omega] at r1
  have r1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 50 (hbase + 200)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) r1
  have r1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (2 : Word)))) (by pcFreeR) r1e
  -- idx 51: sd x0, 464(x20)  (env+464 := 0)
  have r2 := sd_spec_within .x20 .x0 envBase (0 : Word) c464 (464 : BitVec 12) (hbase + 204)
  rw [show (hbase + 204 : Word) + 4 = hbase + 208 from by bv_omega] at r2
  have r2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 51 (hbase + 204)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) r2
  have r2f := cpsTripleWithin_frameR
    (((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ c456) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (2 : Word)))) (by pcFreeR) r2e
  -- idx 52: ld x17, 480(x20)  (x17 := env+480)
  have r3 := ld_spec_within .x17 .x20 envBase c456 c480 (480 : BitVec 12) (hbase + 208) (by nofun)
  rw [show (hbase + 208 : Word) + 4 = hbase + 212 from by bv_omega] at r3
  have r3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 52 (hbase + 208)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) r3
  have r3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (2 : Word)))) (by pcFreeR) r3e
  -- idx 53: sd x17, 472(x20)  (env+472 := env+480)
  have r4 := sd_spec_within .x20 .x17 envBase c480 c472 (472 : BitVec 12) (hbase + 212)
  rw [show (hbase + 212 : Word) + 4 = hbase + 216 from by bv_omega] at r4
  have r4e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 53 (hbase + 212)
      (by simp only [revertTailProg_length]; decide) (by simp only [revertTailProg_length]; decide) (by bv_omega))) r4
  have r4f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (2 : Word)))) (by pcFreeR) r4e
  -- idx 54..60: the halt core
  have hh := evm_return_halt_spec_within hi2 lo2 hi1 lo1 (hbase + 216) flag resume v5 v6 v1 f0
    hla2 hla1
  have hhE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 216) PROG (evm_return_halt hi2 lo2 hi1 lo1) 54
      (by bv_omega) (by rfl)
      (by simp only [revertTailProg_length, evm_return_halt_length]; omega)
      (by simp only [revertTailProg_length]; decide)) hh
  have hhf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ c480) **
      ((.x20 : Reg) ↦ᵣ envBase) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c480) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (2 : Word)))) (by pcFreeR) hhE
  -- compose all seven straight-line steps + halt core
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) k0f k1f
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 r0f
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 r1f
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 r2f
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 r3f
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c4 r4f
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c5 hhf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c6)

/-! ## The public witness -/

/-- **The verified REVERT (0xfd) return-data window + rollback + halt core.**
    From the post-gas handler entry `hbase`, the standalone tail reads
    `offset`/`size` off the stack scratch (`x12`), builds the `0xa0010000`
    return-data descriptor (header zeroed, 22-dword body zeroed, `size@+64`,
    `clamped = min(size,176)@+248`, `evm_memory[offset..offset+clamped]` copied to
    `+72`, the first `min(size,32)` bytes copied to `+0`, `kind = 2@+32`),
    executes the five straight-line rollback env-cell stores
    (`env+448 := env+456`, `env+464 := 0`, `env+472 := env+480`), and halts via
    the shared `dispatchHaltRet 2` core (`evm_halt_flag := 2`, `x1 :=` resume,
    `ret` to `resume &&& ~~~1`).

    Unlike RETURN there is NO `system_call_mode = 0` precondition (the capture
    block is `kind == 1`-only and absent).  The memory-gas `preBody`
    (`.exit_outofgas`) is framed OUT (decision-1 TCB); the `la` immediates stay as
    reconstruction hypotheses (`hlaMem`/`hlaMem2`/`hla2`/`hla1`), the shared
    deferred byte-check. -/
theorem evm_revert_stack_spec_within
    (hbase p evmMemBase envBase flag resume : Word)
    (off size x1o x5o x6o x14o x15o x16o x17o x19o x21o x22o x23o f0
      c448 c456 c464 c472 c480 : Word)
    (descInit memBytes : List (BitVec 8))
    (hDescLen : descInit.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hOff : off.toNat + (returnClamp size).toNat ≤ memBytes.length)
    (hOff32 : off.toNat + (returnClamp32 size).toNat ≤ memBytes.length)
    (hlaMem : (hbase + (80 : Word)) + ((hiMem.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem = evmMemBase)
    (hlaMem2 : (hbase + (128 : Word)) + ((hiMem2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem2 = evmMemBase)
    (hla2 : (hbase + 216 + 4) + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla1 : (hbase + 216 + 16) + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = resume) :
    cpsTripleWithin (155 + 7 * (returnClamp size).toNat + 7 * (returnClamp32 size).toNat)
      hbase (resume &&& ~~~1)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) **
        ((.x6 : Reg) ↦ᵣ x6o) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ x14o) **
        ((.x15 : Reg) ↦ᵣ x15o) ** ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x20 : Reg) ↦ᵣ envBase) ** ((.x21 : Reg) ↦ᵣ x21o) **
        ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** (flag ↦ₘ f0) **
        ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
        ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
        ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
        ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
        ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
        bytesRegion returnDescBase descInit ** bytesRegion evmMemBase memBytes)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ resume) ** ((.x5 : Reg) ↦ᵣ (2 : Word)) **
        ((.x6 : Reg) ↦ᵣ flag) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
        ((.x15 : Reg) ↦ᵣ size) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ c480) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 size).toNat)) **
        ((.x20 : Reg) ↦ᵣ envBase) ** ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x23 ** ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
        (flag ↦ₘ (2 : Word)) **
        ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c456) **
        ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
        ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ (0 : Word)) **
        ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c480) **
        ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
        bytesRegion returnDescBase
          (setBytes
            (copyIntoRegion
              (copyIntoRegion
                (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
                  (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
              memBytes 0 off.toNat (returnClamp32 size).toNat) 32 (dwordBytes (2 : Word))) **
        bytesRegion evmMemBase memBytes) := by
  -- length lemmas for the intermediate descriptor images
  have hRc1len : (copyIntoRegion
      (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
        (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat).length = 256 := by
    simp only [copyIntoRegion_length, length_setBytes, returnDescZeroed, zeroDwords_length, hDescLen]
  have hRc2len : (copyIntoRegion
      (copyIntoRegion
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
          (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
      memBytes 0 off.toNat (returnClamp32 size).toNat).length = 256 := by
    simp only [copyIntoRegion_length, length_setBytes, returnDescZeroed, zeroDwords_length, hDescLen]
  -- Segment 1: prologue (hbase → hbase+8)
  have S1 := revert_seg_prologue hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1
    hbase p off size x14o x15o
  have S1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) **
      ((.x6 : Reg) ↦ᵣ x6o) ** ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) **
      ((.x19 : Reg) ↦ᵣ x19o) ** ((.x20 : Reg) ↦ᵣ envBase) ** ((.x21 : Reg) ↦ᵣ x21o) **
      ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase descInit ** bytesRegion evmMemBase memBytes) (by pcFreeR) S1
  -- Segment 2: header + zero loop (hbase+8 → hbase+56)
  have S2 := revert_seg_header hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1
    hbase x16o x19o x21o descInit hDescLen
  have S2f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) **
      ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x17 : Reg) ↦ᵣ x17o) ** ((.x20 : Reg) ↦ᵣ envBase) ** ((.x22 : Reg) ↦ᵣ x22o) **
      ((.x23 : Reg) ↦ᵣ x23o) ** ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S2
  -- Segment 3: clamp to 176 (hbase+56 → hbase+72)
  have S3 := revert_seg_clamp176 hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1
    hbase size (0 : Word) x22o
  have S3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) **
      ((.x6 : Reg) ↦ᵣ x6o) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ x17o) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0 + 22)))) **
      ((.x20 : Reg) ↦ᵣ envBase) ** ((.x23 : Reg) ↦ᵣ x23o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase (returnDescZeroed descInit) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S3
  -- Segment 4: size/clamped stores + copy loop 1 (hbase+72 → hbase+128)
  have S4 := revert_seg_copy1 hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1
    hbase evmMemBase off size x17o
    (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0 + 22))) (176 : Word) x23o descInit memBytes
    hDescLen hSrcAlign hSrcOver hSrcValid hOff hlaMem
  have S4f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) **
      ((.x12 : Reg) ↦ᵣ p) ** ((.x20 : Reg) ↦ᵣ envBase) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480)) (by pcFreeR) S4
  -- Segment 5: second la + clamp to 32 (hbase+128 → hbase+156)
  have S5 := revert_seg_clamp32 hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1
    hbase evmMemBase off size
    (evmMemBase + BitVec.ofNat 64 (off.toNat + 0 + (returnClamp size).toNat))
    (returnClamp size) (0 : Word) hlaMem2
  have S5f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) **
      ((.x6 : Reg) ↦ᵣ x6o) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (72 + 0 + (returnClamp size).toNat))) **
      ((.x20 : Reg) ↦ᵣ envBase) ** regOwn .x23 ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480) **
      bytesRegion returnDescBase
        (copyIntoRegion
          (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
            (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S5
  -- Segment 6: first-32 prefix copy loop (hbase+156 → hbase+188)
  have S6 := revert_seg_copy2 hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1
    hbase evmMemBase off size
    (returnDescBase + BitVec.ofNat 64 (72 + 0 + (returnClamp size).toNat))
    (copyIntoRegion
      (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
        (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
    memBytes hRc1len hSrcAlign hSrcOver hSrcValid hOff32
  have S6f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) **
      ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x20 : Reg) ↦ᵣ envBase) ** ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** (flag ↦ₘ f0) **
      ((envBase + signExtend12 (448 : BitVec 12)) ↦ₘ c448) **
      ((envBase + signExtend12 (456 : BitVec 12)) ↦ₘ c456) **
      ((envBase + signExtend12 (464 : BitVec 12)) ↦ₘ c464) **
      ((envBase + signExtend12 (472 : BitVec 12)) ↦ₘ c472) **
      ((envBase + signExtend12 (480 : BitVec 12)) ↦ₘ c480)) (by pcFreeR) S6
  -- Segment 7: kind store + rollback + halt core (hbase+188 → resume &&& ~~~1)
  have S7 := revert_seg_kindrollbackhalt hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1
    hbase envBase flag resume
    (evmMemBase + BitVec.ofNat 64 (off.toNat + 0 + (returnClamp32 size).toNat))
    x5o x6o x1o f0 c448 c456 c464 c472 c480
    (copyIntoRegion
      (copyIntoRegion
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
          (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
      memBytes 0 off.toNat (returnClamp32 size).toNat) hRc2len hla2 hla1
  have S7f := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 size).toNat)) **
      ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S7
  -- chain the seven framed segments
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) S1f S2f
  have c13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c12 S3f
  have c14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c13 S4f
  have c15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c14 S5f
  have c16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c15 S6f
  have c17 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c16 S7f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c17)

end Compose

/-! ## Anti-vacuity cover (the `.conditional` `coverRef`) -/

/-- **Cover lemma for the REVERT `.conditional` registry entry**
    (`OpcodeEntry.coverRef`, R-A3 anti-near-vacuity).  On a representative small
    revert (`size = 5`) both descriptor clamps are the identity
    (`returnClamp 5 = returnClamp32 5 = 5`), so the window copies the revert data
    unclamped — the spec is not a vacuous or degenerate statement.  Unlike RETURN
    there is no gating precondition, so this cover records only the clamp
    non-degeneracy.  `decide`-checked. -/
theorem revert_window_nondegenerate :
    returnClamp (5 : Word) = 5 ∧ returnClamp32 (5 : Word) = 5 := by decide

end Terminating
end EvmAsm.Evm64
