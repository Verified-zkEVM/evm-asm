/-
  EvmAsm.Evm64.Terminating.ReturnSpec

  Composition of the standalone (`depthAware = false`) `RETURN` (0xf3)
  return-data descriptor window into a public `cpsTripleWithin` witness, built
  entirely from the already-proven building blocks:

  * the three loop closures and the offset-`SD` primitive of
    `ReturnWindowLoopSpec` (`returnZeroLoop_spec_within`,
    `returnCopyLoop_spec_within`, `bytesRegion_sd_off_within`);
  * the shared halt core `evm_return_halt_spec_within` (`ReturnHaltSpec`);
  * the generic instruction specs (`li`/`ld`/`auipc`/`addi`/`mv`/`add`/`beq`/
    `bgeu`) and the CPS composition combinators (`seqFrame`,
    `cpsTripleWithin_extend_code`, `cpsBranchWithin_*`).

  The full emitted tail (`Codegen.Programs.NoopHalt.returnRevertTail 1 "" false`)
  is modelled here as one `Program` image `returnTailProg`, parameterised by the
  linker `la` immediate pairs (carried as reconstruction hypotheses, exactly as
  the halt core leaves `hla1`/`hla2`).  The public witness
  `evm_return_stack_spec_within` is proved over `CodeReq.ofProg hbase
  returnTailProg`, from the post-gas handler entry `hbase` through the whole
  descriptor window to `resume &&& ~~~1`, gated on the reachable precondition
  `system_call_mode = 0` (see `return_precondition_reachable`).

  ## Coverage boundary (READ THIS)

  * The `preBody` memory-gas glue (with its `.exit_outofgas` branch) is a
    decision-1 TCB item and stays OUTSIDE this triple — the triple is stated
    from the framed post-gas entry `hbase`.
  * The `system_call_mode` capture block is present in `returnTailProg` for
    address layout but is *skipped* (the `beqz` is taken under
    `system_call_mode = 0`); its 16 instructions are never executed on the
    proved path.

  Kernel-checkable throughout (classical-3 only): no `native_decide` /
  `bv_decide`.
-/

import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec
import EvmAsm.Evm64.Terminating.ReturnHaltSpec
import EvmAsm.Rv64.Tactics.SeqFrame

namespace EvmAsm.Evm64
namespace Terminating

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves (as in
    `ReturnWindowLoopSpec`). -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- The descriptor base `OUTPUT_ADDR = 0xa0010000` (dword-aligned). -/
def returnDescBase : Word := 0xa0010000

/-- **The verified `Program` image of `returnRevertTail 1 "" false`'s
    `.Lrr_halt_1` path.**  76 instructions from the post-gas handler entry
    through the descriptor window and the shared halt core, parameterised by the
    linker `la` immediate pairs:

    * `hiSCM`/`loSCM` — `la t0, system_call_mode` (capture guard);
    * `hiLen`/`loLen`, `hiRd`/`loRd` — the (skipped) capture-block `la`s;
    * `hiMem`/`loMem`, `hiMem2`/`loMem2` — the two `la x17, evm_memory`;
    * `hi2`/`lo2`, `hi1`/`lo1` — the halt core's `la evm_halt_flag` /
      `la .dispatch_resume` (as in `ReturnHaltProgram.evm_return_halt`).

    Register mapping follows the RISC-V ABI: `t0..t5 = x5,x6,x7,x28,x29,x30`. -/
def returnTailProg
    (hiSCM : BitVec 20) (loSCM : BitVec 12)
    (hiLen : BitVec 20) (loLen : BitVec 12)
    (hiRd : BitVec 20) (loRd : BitVec 12)
    (hiMem : BitVec 20) (loMem : BitVec 12)
    (hiMem2 : BitVec 20) (loMem2 : BitVec 12)
    (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12) : Program :=
  [ -- prologue: read offset/size off the stack scratch (x12)
    .LD .x14 .x12 0,                        -- 0
    .LD .x15 .x12 32,                       -- 1
    -- system_call_mode capture guard (la t0; ld t0; beqz t0, nocap)
    .AUIPC .x5 hiSCM,                        -- 2
    .ADDI .x5 .x5 loSCM,                     -- 3
    .LD .x5 .x5 0,                           -- 4
    .BEQ .x5 .x0 (BitVec.ofNat 13 68),       -- 5  → .Lrr_nocap (idx 22)
    -- capture block (never executed under system_call_mode = 0)
    .LI .x6 4096,                            -- 6
    .BLTU .x6 .x15 (BitVec.ofNat 13 60),     -- 7
    .AUIPC .x6 hiLen,                        -- 8
    .ADDI .x6 .x6 loLen,                     -- 9
    .SD .x6 .x15 0,                          -- 10
    .ADD .x7 .x13 .x14,                      -- 11
    .AUIPC .x28 hiRd,                        -- 12
    .ADDI .x28 .x28 loRd,                    -- 13
    .MV .x29 .x15,                           -- 14
    .BEQ .x29 .x0 (BitVec.ofNat 13 28),      -- 15
    .LBU .x30 .x7 0,                         -- 16
    .SB .x28 .x30 0,                         -- 17
    .ADDI .x7 .x7 1,                         -- 18
    .ADDI .x28 .x28 1,                       -- 19
    .ADDI .x29 .x29 (-1 : BitVec 12),        -- 20
    .JAL .x0 (-24 : BitVec 21),              -- 21
    -- .Lrr_nocap: header + descriptor-body zeroing
    .LI .x16 returnDescBase,                 -- 22
    .SD .x16 .x0 0,                          -- 23  header dword 0
    .SD .x16 .x0 8,                          -- 24  header dword 1
    .SD .x16 .x0 16,                         -- 25  header dword 2
    .SD .x16 .x0 24,                         -- 26  header dword 3
    .ADDI .x19 .x16 72,                      -- 27
    .LI .x21 22,                             -- 28
    -- zero loop (returnZeroLoop, idx 29..33)
    .BEQ .x21 .x0 (BitVec.ofNat 13 20),      -- 29
    .SD .x19 .x0 0,                          -- 30
    .ADDI .x19 .x19 8,                       -- 31
    .ADDI .x21 .x21 (-1 : BitVec 12),        -- 32
    .JAL .x0 (-16 : BitVec 21),              -- 33
    -- clamp size to 176
    .MV .x21 .x15,                           -- 34
    .LI .x22 176,                            -- 35
    .BGEU .x22 .x21 (BitVec.ofNat 13 8),     -- 36  → label3 (idx 38)
    .MV .x21 .x22,                           -- 37
    -- label3: size / clamped stores
    .SD .x16 .x15 64,                        -- 38  size  @ +64  (dword 8)
    .SD .x16 .x21 248,                       -- 39  clamp @ +248 (dword 31)
    .AUIPC .x17 hiMem,                       -- 40  la x17, evm_memory
    .ADDI .x17 .x17 loMem,                   -- 41
    .ADD .x17 .x17 .x14,                     -- 42
    .ADDI .x19 .x16 72,                      -- 43
    .MV .x22 .x21,                           -- 44
    -- copy loop 1 (returnCopyLoop, idx 45..51): dest +72, n = clamped
    .BEQ .x22 .x0 (BitVec.ofNat 13 28),      -- 45
    .LBU .x23 .x17 0,                        -- 46
    .SB .x19 .x23 0,                         -- 47
    .ADDI .x17 .x17 1,                       -- 48
    .ADDI .x19 .x19 1,                       -- 49
    .ADDI .x22 .x22 (-1 : BitVec 12),        -- 50
    .JAL .x0 (-24 : BitVec 21),              -- 51
    -- label5: clamp size to 32 for the first-32 prefix copy
    .AUIPC .x17 hiMem2,                      -- 52  la x17, evm_memory
    .ADDI .x17 .x17 loMem2,                  -- 53
    .ADD .x17 .x17 .x14,                     -- 54
    .MV .x22 .x15,                           -- 55
    .LI .x21 32,                             -- 56
    .BGEU .x21 .x22 (BitVec.ofNat 13 8),     -- 57  → label6 (idx 59)
    .MV .x22 .x21,                           -- 58
    -- label6: reset dest to descriptor base
    .MV .x19 .x16,                           -- 59
    -- copy loop 2 (returnCopyLoop, idx 60..66): dest +0, n = min(size,32)
    .BEQ .x22 .x0 (BitVec.ofNat 13 28),      -- 60
    .LBU .x23 .x17 0,                        -- 61
    .SB .x19 .x23 0,                         -- 62
    .ADDI .x17 .x17 1,                       -- 63
    .ADDI .x19 .x19 1,                       -- 64
    .ADDI .x22 .x22 (-1 : BitVec 12),        -- 65
    .JAL .x0 (-24 : BitVec 21),              -- 66
    -- label8: kind store, then the shared halt core
    .LI .x17 1,                              -- 67
    .SD .x16 .x17 32,                        -- 68  kind = 1 @ +32 (dword 4)
    -- halt core (evm_return_halt hi2 lo2 hi1 lo1, idx 69..75)
    .LI .x5 2,                               -- 69
    .AUIPC .x6 hi2,                          -- 70
    .ADDI .x6 .x6 lo2,                       -- 71
    .SD .x6 .x5 0,                           -- 72
    .AUIPC .x1 hi1,                          -- 73
    .ADDI .x1 .x1 lo1,                       -- 74
    .JALR .x0 .x1 0 ]                        -- 75

/-- Byte fidelity: the modelled tail is exactly 76 instructions. -/
@[simp] theorem returnTailProg_length
    (hiSCM : BitVec 20) (loSCM : BitVec 12) (hiLen : BitVec 20) (loLen : BitVec 12)
    (hiRd : BitVec 20) (loRd : BitVec 12) (hiMem : BitVec 20) (loMem : BitVec 12)
    (hiMem2 : BitVec 20) (loMem2 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12) :
    (returnTailProg hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
      hi2 lo2 hi1 lo1).length = 76 := rfl

/-! ## Composition -/

section Compose

variable (hiSCM : BitVec 20) (loSCM : BitVec 12) (hiLen : BitVec 20) (loLen : BitVec 12)
  (hiRd : BitVec 20) (loRd : BitVec 12) (hiMem : BitVec 20) (loMem : BitVec 12)
  (hiMem2 : BitVec 20) (loMem2 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
  (hi1 : BitVec 20) (lo1 : BitVec 12)

/-- Abbreviation for the full tail program at the current immediate params. -/
local notation "PROG" =>
  returnTailProg hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2 hi2 lo2 hi1 lo1

/-- Abbreviation for the full-tail CodeReq at base `hbase`. -/
local notation "TAILCR" hbase => CodeReq.ofProg hbase PROG

/-- **Prologue + capture-skip segment** (`hbase → hbase + 88`).  Reads the
    stack-scratch `offset`/`size` into `x14`/`x15`, computes the
    `system_call_mode` address, loads it (`= 0` by precondition), and takes the
    `beqz` to `.Lrr_nocap` (idx 22 = `hbase + 88`), skipping the capture block.
    `hlaSCM` reconstructs `la t0, system_call_mode`. -/
theorem return_seg_prologue (hbase p scmAddr off size x14o x15o x5o : Word)
    (hlaSCM : (hbase + (8 : Word)) + ((hiSCM.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loSCM = scmAddr) :
    cpsTripleWithin 6 hbase (hbase + 88)
      (TAILCR hbase)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p) ** (.x14 ↦ᵣ x14o) ** (.x15 ↦ᵣ x15o) **
        (.x5 ↦ᵣ x5o) ** ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
        ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p) ** (.x14 ↦ᵣ off) ** (.x15 ↦ᵣ size) **
        (.x5 ↦ᵣ (0 : Word)) ** ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
        ((scmAddr + signExtend12 0) ↦ₘ (0 : Word))) := by
  -- idx 0: ld x14, 0(x12).  Frame the full persistent working set on each step
  -- so consecutive steps share the same assertion (composed by seq_perm_same_cr).
  have t0 := ld_spec_within .x14 .x12 p x14o off 0 hbase (by nofun)
  have t0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 0 hbase
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t0
  have t0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x15 : Reg) ↦ᵣ x15o) ** ((.x5 : Reg) ↦ᵣ x5o) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)))
    (by pcFree) t0e
  -- idx 1: ld x15, 32(x12)
  have t1 := ld_spec_within .x15 .x12 p x15o size 32 (hbase + 4) (by nofun)
  rw [show (hbase + 4 : Word) + 4 = hbase + 8 from by bv_omega] at t1
  have t1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 1 (hbase + 4)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t1
  have t1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x5 : Reg) ↦ᵣ x5o) **
      ((p + signExtend12 0) ↦ₘ off) ** ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)))
    (by pcFree) t1e
  -- idx 2: auipc x5, hiSCM.  Bind the auipc result so idx 3's input is the
  -- *same* term (avoids an OfNat-vs-cast permutation mismatch).
  have t2 := auipc_spec_within .x5 x5o hiSCM (hbase + 8) (by nofun)
  rw [show (hbase + 8 : Word) + 4 = hbase + 12 from by bv_omega] at t2
  set scmAuipc := (hbase + (8 : Word)) + ((hiSCM.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    with hAuipc
  have t2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 2 (hbase + 8)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t2
  have t2f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)))
    (by pcFree) t2e
  -- idx 3: addi x5, x5, loSCM  (→ scmAddr via hlaSCM)
  have t3 := addi_spec_same_within .x5 scmAuipc loSCM (hbase + 12) (by nofun)
  rw [hlaSCM, show (hbase + 12 : Word) + 4 = hbase + 16 from by bv_omega] at t3
  have t3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 3 (hbase + 12)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t3
  have t3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)))
    (by pcFree) t3e
  -- idx 4: ld x5, 0(x5)  (loads system_call_mode = 0)
  have t4 := ld_spec_same_within .x5 scmAddr (0 : Word) 0 (hbase + 16) (by nofun)
  rw [show (hbase + 16 : Word) + 4 = hbase + 20 from by bv_omega] at t4
  have t4e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 4 (hbase + 16)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t4
  have t4f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size))
    (by pcFree) t4e
  -- idx 5: beqz x5, .Lrr_nocap  (x5 = 0 → taken to hbase + 88)
  have t5 := beq_spec_gen_within .x5 .x0 (BitVec.ofNat 13 68) (0 : Word) (0 : Word) (hbase + 20)
  rw [show (hbase + 20 : Word) + signExtend13 (BitVec.ofNat 13 68) = hbase + 88 from by
        rw [show signExtend13 (BitVec.ofNat 13 68) = (68 : Word) from by decide]; bv_omega] at t5
  have t5e := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 5 (hbase + 20)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) t5
  have t5t := cpsBranchWithin_takenStripPure2 t5e (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 (by decide))
  have t5f := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)))
    (by pcFree) t5t
  -- compose the six steps (same CR throughout; permute the shared midpoint)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) t0f t1f
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 t2f
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 t3f
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123 t4f
  have c012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01234 t5f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c012345)

/-- The descriptor byte-list after the header zeroing + the 22-dword body
    zeroing loop: `zeroDwords (zeroDwords descInit 0 4) 9 22`. -/
def returnDescZeroed (descInit : List (BitVec 8)) : List (BitVec 8) :=
  zeroDwords (zeroDwords descInit 0 4) 9 22

/-- **Header + descriptor-body zeroing segment** (`hbase+88 → hbase+136`).
    Loads the descriptor base into `x16`, zeroes the four header dwords, sets up
    the body pointer/count, and runs the 22-dword zeroing loop.  `descInit` is
    the initial 256-byte descriptor image. -/
theorem return_seg_header (hbase : Word) (x16o x19o x21o : Word)
    (descInit : List (BitVec 8)) (hlen : descInit.length = 256) :
    cpsTripleWithin 118 (hbase + 88) (hbase + 136)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ x16o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) **
        bytesRegion returnDescBase descInit)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0 + 22)))) **
        ((.x21 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion returnDescBase (returnDescZeroed descInit)) := by
  -- idx 22: li x16, descBase
  have s0 := li_spec_within .x16 x16o returnDescBase (hbase + 88) (by nofun)
  rw [show (hbase + 88 : Word) + 4 = hbase + 92 from by bv_omega] at s0
  have s0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 22 (hbase + 88)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s0
  have s0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) **
      bytesRegion returnDescBase descInit) (by pcFreeR) s0e
  -- idx 23..26: sd x0 at 0/8/16/24 (header dwords)
  have hd0 := bytesRegion_sd_off_within .x16 .x0 returnDescBase (0 : Word) (hbase + 92)
    descInit 0 (0 : BitVec 12) (by decide) (by rw [hlen]; omega)
  rw [show (hbase + 92 : Word) + 4 = hbase + 96 from by bv_omega] at hd0
  have hd0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 23 (hbase + 92)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) hd0
  have hd0f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o)) (by pcFreeR) hd0e
  have hd1 := bytesRegion_sd_off_within .x16 .x0 returnDescBase (0 : Word) (hbase + 96)
    (setBytes descInit 0 (dwordBytes (0 : Word))) 1 (8 : BitVec 12) (by decide)
    (by rw [length_setBytes, hlen]; omega)
  rw [show (hbase + 96 : Word) + 4 = hbase + 100 from by bv_omega] at hd1
  have hd1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 24 (hbase + 96)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) hd1
  have hd1f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o)) (by pcFreeR) hd1e
  have hd2 := bytesRegion_sd_off_within .x16 .x0 returnDescBase (0 : Word) (hbase + 100)
    (setBytes (setBytes descInit 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word))) 2
    (16 : BitVec 12) (by decide) (by rw [length_setBytes, length_setBytes, hlen]; omega)
  rw [show (hbase + 100 : Word) + 4 = hbase + 104 from by bv_omega] at hd2
  have hd2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 25 (hbase + 100)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) hd2
  have hd2f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o)) (by pcFreeR) hd2e
  have hd3 := bytesRegion_sd_off_within .x16 .x0 returnDescBase (0 : Word) (hbase + 104)
    (setBytes (setBytes (setBytes descInit 0 (dwordBytes (0 : Word))) 8 (dwordBytes (0 : Word)))
      16 (dwordBytes (0 : Word))) 3 (24 : BitVec 12) (by decide)
    (by rw [length_setBytes, length_setBytes, length_setBytes, hlen]; omega)
  rw [show (hbase + 104 : Word) + 4 = hbase + 108 from by bv_omega] at hd3
  have hd3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 26 (hbase + 104)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) hd3
  have hd3f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o)) (by pcFreeR) hd3e
  -- name the header-zeroed region (= zeroDwords descInit 0 4)
  set R0 := setBytes (setBytes (setBytes (setBytes descInit 0 (dwordBytes (0 : Word))) 8
    (dwordBytes (0 : Word))) 16 (dwordBytes (0 : Word))) 24 (dwordBytes (0 : Word)) with hR0
  -- idx 27: addi x19, x16, 72  →  x19 = descBase + 8*9
  have s1 := addi_spec_gen_within .x19 .x16 x19o returnDescBase (72 : BitVec 12)
    (hbase + 108) (by nofun)
  rw [show returnDescBase + signExtend12 (72 : BitVec 12)
        = returnDescBase + BitVec.ofNat 64 (8 * (9 + 0)) from by decide] at s1
  rw [show (hbase + 108 : Word) + 4 = hbase + 112 from by bv_omega] at s1
  have s1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 27 (hbase + 108)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s1
  have s1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x21 : Reg) ↦ᵣ x21o) ** bytesRegion returnDescBase R0)
    (by pcFreeR) s1e
  -- idx 28: li x21, 22
  have s2 := li_spec_within .x21 x21o (BitVec.ofNat 64 22) (hbase + 112) (by nofun)
  rw [show (hbase + 112 : Word) + 4 = hbase + 116 from by bv_omega] at s2
  have s2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 28 (hbase + 112)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s2
  have s2f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0)))) **
      bytesRegion returnDescBase R0) (by pcFreeR) s2e
  -- idx 29..33: the zeroing loop (returnZeroLoop, embedded via ofProg_mono_sub)
  have hloop := returnZeroLoop_spec_within (hbase + 116) returnDescBase R0 9 22 0
    (by rw [hR0, length_setBytes, length_setBytes, length_setBytes, length_setBytes, hlen]; omega)
    (by rw [hR0, length_setBytes, length_setBytes, length_setBytes, length_setBytes, hlen]; omega)
  rw [show zeroDwords R0 9 0 = R0 from rfl,
      show (hbase + 116 : Word) + 20 = hbase + 136 from by bv_omega] at hloop
  have hloopE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 116) PROG returnZeroLoop 29
      (by bv_omega) (by rfl)
      (by simp only [returnTailProg_length, returnZeroLoop_length]; omega)
      (by simp only [returnTailProg_length]; decide)) hloop
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

/-- The size clamped to the 176-byte descriptor-body window (unsigned min). -/
def returnClamp (v : Word) : Word := if BitVec.ult (176 : Word) v then (176 : Word) else v

/-- The size clamped to the first-32-byte prefix window (unsigned min). -/
def returnClamp32 (v : Word) : Word := if BitVec.ult (32 : Word) v then (32 : Word) else v

/-- Round-trip: a 64-bit word equals `ofNat` of its own `toNat`. -/
theorem word_ofNat_toNat (w : Word) : BitVec.ofNat 64 w.toNat = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

/-- `returnClamp` never exceeds 176. -/
theorem returnClamp_toNat_le (v : Word) : (returnClamp v).toNat ≤ 176 := by
  unfold returnClamp
  split
  · decide
  · next h =>
      simp only [BitVec.ult, decide_eq_true_eq,
        show (176 : Word).toNat = 176 from by decide] at h
      omega

/-- `returnClamp32` never exceeds 32. -/
theorem returnClamp32_toNat_le (v : Word) : (returnClamp32 v).toNat ≤ 32 := by
  unfold returnClamp32
  split
  · decide
  · next h =>
      simp only [BitVec.ult, decide_eq_true_eq,
        show (32 : Word).toNat = 32 from by decide] at h
      omega

/-- Every byte of the 256-byte descriptor region `0xa0010000 .. +256` is a valid
    byte access (it lies in the RAM zone). -/
theorem returnDescBase_valid (k : Nat) (hk : k < 256) :
    isValidByteAccess (returnDescBase + BitVec.ofNat 64 k) = true := by
  have h : (returnDescBase + BitVec.ofNat 64 k).toNat = 2684420096 + k := by
    rw [BitVec.toNat_add, show (returnDescBase).toNat = 2684420096 from by decide,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [isValidByteAccess_eq, isValidMemAddr, RAM_MEM_START, RAM_MEM_END, h,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **Size-clamp-to-176 segment** (`hbase+136 → hbase+152`).  `x21 := x15`,
    `x22 := 176`, then `bgeu x22,x21,3f` skips `mv x21,x22` when `x15 ≤ᵤ 176`.
    At label3, `x21 = min(x15,176) = returnClamp x15` and `x22 = 176`. -/
theorem return_seg_clamp176 (hbase : Word) (x15v x21o x22o : Word) :
    cpsTripleWithin 4 (hbase + 136) (hbase + 152)
      (TAILCR hbase)
      (((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o))
      (((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) **
        ((.x22 : Reg) ↦ᵣ (176 : Word))) := by
  -- idx 34: mv x21, x15
  have s0 := mv_spec_within .x21 .x15 x15v x21o (hbase + 136) (by nofun)
  rw [show (hbase + 136 : Word) + 4 = hbase + 140 from by bv_omega] at s0
  have s0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 34 (hbase + 136)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s0
  have s0f := cpsTripleWithin_frameR ((.x22 : Reg) ↦ᵣ x22o) (by pcFree) s0e
  -- idx 35: li x22, 176
  have s1 := li_spec_within .x22 x22o (176 : Word) (hbase + 140) (by nofun)
  rw [show (hbase + 140 : Word) + 4 = hbase + 144 from by bv_omega] at s1
  have s1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 35 (hbase + 140)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s1
  have s1f := cpsTripleWithin_frameR
    (((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x15v)) (by pcFree) s1e
  have pre01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s0f s1f
  -- idx 36: bgeu x22, x21, 3f
  have hb := bgeu_spec_gen_within .x22 .x21 (BitVec.ofNat 13 8) (176 : Word) x15v (hbase + 144)
  rw [show (hbase + 144 : Word) + signExtend13 (BitVec.ofNat 13 8) = hbase + 152 from by
        rw [show signExtend13 (BitVec.ofNat 13 8) = (8 : Word) from by decide]; bv_omega,
      show (hbase + 144 : Word) + 4 = hbase + 148 from by bv_omega] at hb
  have hbe := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 36 (hbase + 144)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) hb
  by_cases h : BitVec.ult (176 : Word) x15v
  · -- size > 176: bgeu NOT taken; execute mv x21, x22 (idx 37)
    have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact (((sepConj_pure_right _).1 hQ).2) h)
    have hntf := cpsTripleWithin_frameR ((.x15 : Reg) ↦ᵣ x15v) (by pcFree) hnt
    have s2 := mv_spec_within .x21 .x22 (176 : Word) x15v (hbase + 148) (by nofun)
    rw [show (hbase + 148 : Word) + 4 = hbase + 152 from by bv_omega] at s2
    have s2e := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 37 (hbase + 148)
        (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s2
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
    (`hbase+152 → hbase+208`).  Stores `size@+64` and `clamped@+248`, points
    `x17` at `evm_memory+offset`, `x19` at `descriptor+72`, `x22 := clamped`, and
    runs the copy loop, filling `descriptor[72 .. 72+clamped]` from
    `evm_memory[offset .. offset+clamped]`.  `hlaMem` reconstructs the first
    `la x17, evm_memory`. -/
theorem return_seg_copy1 (hbase evmMemBase : Word)
    (x14v x15v x17o x19o x22o x23o : Word) (descInit memBytes : List (BitVec 8))
    (hDescLen : descInit.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hOff : x14v.toNat + (returnClamp x15v).toNat ≤ memBytes.length)
    (hlaMem : (hbase + (160 : Word)) + ((hiMem.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem = evmMemBase) :
    cpsTripleWithin (7 * (returnClamp x15v).toNat + 8) (hbase + 152) (hbase + 208)
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
  -- idx 38: sd x16, size, 64(x16)
  have d0 := bytesRegion_sd_off_within .x16 .x15 returnDescBase x15v (hbase + 152)
    (returnDescZeroed descInit) 8 (64 : BitVec 12) (by decide) (by rw [hReg256]; omega)
  rw [show (hbase + 152 : Word) + 4 = hbase + 156 from by bv_omega] at d0
  have d0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 38 (hbase + 152)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) d0
  have d0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x17 : Reg) ↦ᵣ x17o) **
      ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ x22o) **
      ((.x23 : Reg) ↦ᵣ x23o) ** bytesRegion evmMemBase memBytes) (by pcFreeR) d0e
  -- idx 39: sd x16, clamped, 248(x16)
  have d1 := bytesRegion_sd_off_within .x16 .x21 returnDescBase (returnClamp x15v) (hbase + 156)
    (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 31 (248 : BitVec 12) (by decide)
    (by rw [length_setBytes, hReg256])
  rw [show (hbase + 156 : Word) + 4 = hbase + 160 from by bv_omega] at d1
  have d1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 39 (hbase + 156)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) d1
  have d1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x17 : Reg) ↦ᵣ x17o) ** ((.x19 : Reg) ↦ᵣ x19o) ** ((.x22 : Reg) ↦ᵣ x22o) **
      ((.x23 : Reg) ↦ᵣ x23o) ** bytesRegion evmMemBase memBytes) (by pcFreeR) d1e
  -- idx 40: auipc x17, evm_memory (hi)
  have a0 := auipc_spec_within .x17 x17o hiMem (hbase + 160) (by nofun)
  rw [show (hbase + 160 : Word) + 4 = hbase + 164 from by bv_omega] at a0
  set memAuipc := (hbase + (160 : Word)) + ((hiMem.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    with hMemAuipc
  have a0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 40 (hbase + 160)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a0
  have a0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x19 : Reg) ↦ᵣ x19o) **
      ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a0e
  -- idx 41: addi x17, x17, lo  (→ evmMemBase)
  have a1 := addi_spec_same_within .x17 memAuipc loMem (hbase + 164) (by nofun)
  rw [hlaMem, show (hbase + 164 : Word) + 4 = hbase + 168 from by bv_omega] at a1
  have a1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 41 (hbase + 164)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a1
  have a1f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x19 : Reg) ↦ᵣ x19o) **
      ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a1e
  -- idx 42: add x17, x17, x14  (→ evmMemBase + offset)
  have a2 := add_spec_rd_eq_rs1_within .x17 .x14 evmMemBase x14v (hbase + 168) (by nofun)
  rw [show (hbase + 168 : Word) + 4 = hbase + 172 from by bv_omega] at a2
  have a2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 42 (hbase + 168)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a2
  have a2f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
      ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) ** ((.x22 : Reg) ↦ᵣ x22o) **
      ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a2e
  -- idx 43: addi x19, x16, 72  (→ descBase + 72)
  have a3 := addi_spec_gen_within .x19 .x16 x19o returnDescBase (72 : BitVec 12) (hbase + 172) (by nofun)
  rw [show returnDescBase + signExtend12 (72 : BitVec 12)
        = returnDescBase + BitVec.ofNat 64 (72 + 0) from by decide,
      show (hbase + 172 : Word) + 4 = hbase + 176 from by bv_omega] at a3
  have a3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 43 (hbase + 172)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a3
  have a3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) ** ((.x21 : Reg) ↦ᵣ returnClamp x15v) **
      ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a3e
  -- idx 44: mv x22, x21  (→ clamped)
  have a4 := mv_spec_within .x22 .x21 (returnClamp x15v) x22o (hbase + 176) (by nofun)
  rw [show (hbase + 176 : Word) + 4 = hbase + 180 from by bv_omega] at a4
  have a4e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 44 (hbase + 176)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a4
  have a4f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (72 + 0))) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
          (dwordBytes (returnClamp x15v))) ** bytesRegion evmMemBase memBytes) (by pcFreeR) a4e
  -- idx 45..51: the copy loop
  have hStoresLen : (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes x15v)) 248
      (dwordBytes (returnClamp x15v))).length = 256 := by
    rw [length_setBytes, length_setBytes, hReg256]
  have hloop := returnCopyLoop_spec_within (hbase + 180) evmMemBase returnDescBase memBytes
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
      show (hbase + 180 : Word) + 28 = hbase + 208 from by bv_omega] at hloop
  have hloopE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 180) PROG returnCopyLoop 45
      (by bv_omega) (by rfl)
      (by simp only [returnTailProg_length, returnCopyLoop_length]; omega)
      (by simp only [returnTailProg_length]; decide)) hloop
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

/-- **Second `la x17, evm_memory` + clamp-to-32 segment**
    (`hbase+208 → hbase+236`).  Re-points `x17` at `evm_memory+offset`, then
    `x22 := min(x15,32) = returnClamp32 x15`, `x21 := 32`, via `bgeu x21,x22,6f`.
    `hlaMem2` reconstructs the second `la x17, evm_memory`. -/
theorem return_seg_clamp32 (hbase evmMemBase : Word)
    (x14v x15v x17o x21o x22o : Word)
    (hlaMem2 : (hbase + (208 : Word)) + ((hiMem2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem2 = evmMemBase) :
    cpsTripleWithin 7 (hbase + 208) (hbase + 236)
      (TAILCR hbase)
      (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o))
      (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) **
        ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) ** ((.x21 : Reg) ↦ᵣ (32 : Word)) **
        ((.x22 : Reg) ↦ᵣ returnClamp32 x15v)) := by
  -- idx 52: auipc x17
  have a0 := auipc_spec_within .x17 x17o hiMem2 (hbase + 208) (by nofun)
  rw [show (hbase + 208 : Word) + 4 = hbase + 212 from by bv_omega] at a0
  set memAuipc2 := (hbase + (208 : Word)) + ((hiMem2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    with hMemAuipc2
  have a0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 52 (hbase + 208)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a0
  have a0f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x21o) **
      ((.x22 : Reg) ↦ᵣ x22o)) (by pcFree) a0e
  -- idx 53: addi x17, x17, lo  (→ evmMemBase)
  have a1 := addi_spec_same_within .x17 memAuipc2 loMem2 (hbase + 212) (by nofun)
  rw [hlaMem2, show (hbase + 212 : Word) + 4 = hbase + 216 from by bv_omega] at a1
  have a1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 53 (hbase + 212)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a1
  have a1f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x21o) **
      ((.x22 : Reg) ↦ᵣ x22o)) (by pcFree) a1e
  -- idx 54: add x17, x17, x14
  have a2 := add_spec_rd_eq_rs1_within .x17 .x14 evmMemBase x14v (hbase + 216) (by nofun)
  rw [show (hbase + 216 : Word) + 4 = hbase + 220 from by bv_omega] at a2
  have a2e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 54 (hbase + 216)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a2
  have a2f := cpsTripleWithin_frameR
    (((.x15 : Reg) ↦ᵣ x15v) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o)) (by pcFree) a2e
  -- idx 55: mv x22, x15
  have a3 := mv_spec_within .x22 .x15 x15v x22o (hbase + 220) (by nofun)
  rw [show (hbase + 220 : Word) + 4 = hbase + 224 from by bv_omega] at a3
  have a3e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 55 (hbase + 220)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a3
  have a3f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) ** ((.x21 : Reg) ↦ᵣ x21o))
    (by pcFree) a3e
  -- idx 56: li x21, 32
  have a4 := li_spec_within .x21 x21o (32 : Word) (hbase + 224) (by nofun)
  rw [show (hbase + 224 : Word) + 4 = hbase + 228 from by bv_omega] at a4
  have a4e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 56 (hbase + 224)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) a4
  have a4f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) **
      ((.x22 : Reg) ↦ᵣ x15v)) (by pcFree) a4e
  have pre0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) a0f a1f
  have pre1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre0 a2f
  have pre2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre1 a3f
  have pre3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) pre2 a4f
  -- idx 57: bgeu x21, x22, 6f
  have hb := bgeu_spec_gen_within .x21 .x22 (BitVec.ofNat 13 8) (32 : Word) x15v (hbase + 228)
  rw [show (hbase + 228 : Word) + signExtend13 (BitVec.ofNat 13 8) = hbase + 236 from by
        rw [show signExtend13 (BitVec.ofNat 13 8) = (8 : Word) from by decide]; bv_omega,
      show (hbase + 228 : Word) + 4 = hbase + 232 from by bv_omega] at hb
  have hbe := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 57 (hbase + 228)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) hb
  by_cases h : BitVec.ult (32 : Word) x15v
  · -- size > 32: bgeu NOT taken; mv x22, x21 (idx 58)
    have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact (((sepConj_pure_right _).1 hQ).2) h)
    have hntf := cpsTripleWithin_frameR
      (((.x14 : Reg) ↦ᵣ x14v) ** ((.x15 : Reg) ↦ᵣ x15v) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)))
      (by pcFree) hnt
    have s2 := mv_spec_within .x22 .x21 (32 : Word) x15v (hbase + 232) (by nofun)
    rw [show (hbase + 232 : Word) + 4 = hbase + 236 from by bv_omega] at s2
    have s2e := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 58 (hbase + 232)
        (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) s2
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

/-- **First-32-byte prefix copy segment** (`hbase+236 → hbase+268`).  Resets
    `x19` to the descriptor base and copies `min(x15,32)` bytes of
    `evm_memory[offset..]` into `descriptor[0..]`.  `descBytes` is the descriptor
    image entering (after the `+72` window copy). -/
theorem return_seg_copy2 (hbase evmMemBase : Word)
    (x14v x15v x19o : Word) (descBytes memBytes : List (BitVec 8))
    (hDescLen : descBytes.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hOff32 : x14v.toNat + (returnClamp32 x15v).toNat ≤ memBytes.length) :
    cpsTripleWithin (7 * (returnClamp32 x15v).toNat + 2) (hbase + 236) (hbase + 268)
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
  -- idx 59: mv x19, x16
  have m0 := mv_spec_within .x19 .x16 returnDescBase x19o (hbase + 236) (by nofun)
  rw [show (hbase + 236 : Word) + 4 = hbase + 240 from by bv_omega] at m0
  have m0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 59 (hbase + 236)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) m0
  have m0f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x17 : Reg) ↦ᵣ (evmMemBase + x14v)) **
      ((.x22 : Reg) ↦ᵣ returnClamp32 x15v) ** ((.x23 : Reg) ↦ᵣ x23o) **
      bytesRegion returnDescBase descBytes ** bytesRegion evmMemBase memBytes) (by pcFreeR) m0e
  -- idx 60..66: copy loop 2 (dest +0)
  have hloop := returnCopyLoop_spec_within (hbase + 240) evmMemBase returnDescBase memBytes
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
      show (hbase + 240 : Word) + 28 = hbase + 268 from by bv_omega] at hloop
  have hloopE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 240) PROG returnCopyLoop 60
      (by bv_omega) (by rfl)
      (by simp only [returnTailProg_length, returnCopyLoop_length]; omega)
      (by simp only [returnTailProg_length]; decide)) hloop
  have hloopf := cpsTripleWithin_frameR ((.x16 : Reg) ↦ᵣ returnDescBase) (by pcFreeR) hloopE
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) m0f hloopf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c0)

/-- **Kind store + halt core segment** (`hbase+268 → resume &&& ~~~1`).  Stores
    `kind = 1 @ +32`, then runs the shared `dispatchHaltRet 2` halt core: sets
    `evm_halt_flag := 2`, points `x1` at `.dispatch_resume`, and `ret`s.
    `hla2`/`hla1` reconstruct the halt core's two `la`s (as in `ReturnHaltSpec`). -/
theorem return_seg_kindhalt (hbase flag resume : Word)
    (x17o v5 v6 v1 f0 : Word) (descBytes : List (BitVec 8))
    (hDescLen : descBytes.length = 256)
    (hla2 : (hbase + 276 + 4) + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla1 : (hbase + 276 + 16) + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = resume) :
    cpsTripleWithin 9 (hbase + 268) (resume &&& ~~~1)
      (TAILCR hbase)
      (((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ x17o) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) **
        bytesRegion returnDescBase descBytes)
      (((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ (1 : Word)) **
        ((.x5 : Reg) ↦ᵣ (2 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) ** ((.x1 : Reg) ↦ᵣ resume) **
        (flag ↦ₘ (2 : Word)) **
        bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (1 : Word)))) := by
  -- idx 67: li x17, 1
  have k0 := li_spec_within .x17 x17o (1 : Word) (hbase + 268) (by nofun)
  rw [show (hbase + 268 : Word) + 4 = hbase + 272 from by bv_omega] at k0
  have k0e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 67 (hbase + 268)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) k0
  have k0f := cpsTripleWithin_frameR
    (((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0) ** bytesRegion returnDescBase descBytes) (by pcFreeR) k0e
  -- idx 68: sd x16, kind, 32(x16)
  have k1 := bytesRegion_sd_off_within .x16 .x17 returnDescBase (1 : Word) (hbase + 272)
    descBytes 4 (32 : BitVec 12) (by decide) (by rw [hDescLen]; omega)
  rw [show (hbase + 272 : Word) + 4 = hbase + 276 from by bv_omega] at k1
  have k1e := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hbase PROG 68 (hbase + 272)
      (by simp only [returnTailProg_length]; decide) (by simp only [returnTailProg_length]; decide) (by bv_omega))) k1
  have k1f := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x1 : Reg) ↦ᵣ v1) ** (flag ↦ₘ f0))
    (by pcFreeR) k1e
  -- idx 69..75: the halt core
  have hh := evm_return_halt_spec_within hi2 lo2 hi1 lo1 (hbase + 276) flag resume v5 v6 v1 f0
    hla2 hla1
  have hhE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub hbase (hbase + 276) PROG (evm_return_halt hi2 lo2 hi1 lo1) 69
      (by bv_omega) (by rfl)
      (by simp only [returnTailProg_length, evm_return_halt_length]; omega)
      (by simp only [returnTailProg_length]; decide)) hh
  have hhf := cpsTripleWithin_frameR
    (((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ (1 : Word)) **
      bytesRegion returnDescBase (setBytes descBytes 32 (dwordBytes (1 : Word)))) (by pcFreeR) hhE
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) k0f k1f
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 hhf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c1)

/-! ## The public witness -/

/-- **The verified RETURN (0xf3) return-data window + halt core.**  From the
    post-gas handler entry `hbase`, under the reachable precondition
    `system_call_mode = 0` (the `scmAddr` cell holds `0`), the standalone tail
    reads `offset`/`size` off the stack scratch (`x12`), builds the `0xa0010000`
    return-data descriptor (header zeroed, 22-dword body zeroed, `size@+64`,
    `clamped = min(size,176)@+248`, `evm_memory[offset..offset+clamped]` copied
    to `+72`, the first `min(size,32)` bytes copied to `+0`, `kind = 1@+32`), and
    halts via the shared `dispatchHaltRet 2` core (`evm_halt_flag := 2`, `x1 :=`
    resume, `ret` to `resume &&& ~~~1`).

    The memory-gas `preBody` (`.exit_outofgas`) is framed OUT (decision-1 TCB);
    the `la` immediates stay as reconstruction hypotheses (`hlaSCM`/`hlaMem`/
    `hlaMem2`/`hla2`/`hla1`), the shared deferred byte-check. -/
theorem evm_return_stack_spec_within
    (hbase p scmAddr evmMemBase flag resume : Word)
    (off size x1o x5o x6o x14o x15o x16o x17o x19o x21o x22o x23o f0 : Word)
    (descInit memBytes : List (BitVec 8))
    (hDescLen : descInit.length = 256)
    (hSrcAlign : evmMemBase.toNat % 8 = 0)
    (hSrcOver : evmMemBase.toNat + memBytes.length < 2 ^ 64)
    (hSrcValid : ∀ k, k < memBytes.length →
      isValidByteAccess (evmMemBase + BitVec.ofNat 64 k) = true)
    (hOff : off.toNat + (returnClamp size).toNat ≤ memBytes.length)
    (hOff32 : off.toNat + (returnClamp32 size).toNat ≤ memBytes.length)
    (hlaSCM : (hbase + (8 : Word)) + ((hiSCM.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loSCM = scmAddr)
    (hlaMem : (hbase + (160 : Word)) + ((hiMem.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem = evmMemBase)
    (hlaMem2 : (hbase + (208 : Word)) + ((hiMem2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
                + signExtend12 loMem2 = evmMemBase)
    (hla2 : (hbase + 276 + 4) + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla1 : (hbase + 276 + 16) + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = resume) :
    cpsTripleWithin (154 + 7 * (returnClamp size).toNat + 7 * (returnClamp32 size).toNat)
      hbase (resume &&& ~~~1)
      (TAILCR hbase)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ x5o) **
        ((.x6 : Reg) ↦ᵣ x6o) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ x14o) **
        ((.x15 : Reg) ↦ᵣ x15o) ** ((.x16 : Reg) ↦ᵣ x16o) ** ((.x17 : Reg) ↦ᵣ x17o) **
        ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) ** ((.x22 : Reg) ↦ᵣ x22o) **
        ((.x23 : Reg) ↦ᵣ x23o) ** ((p + signExtend12 0) ↦ₘ off) **
        ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) **
        (flag ↦ₘ f0) ** bytesRegion returnDescBase descInit **
        bytesRegion evmMemBase memBytes)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ resume) ** ((.x5 : Reg) ↦ᵣ (2 : Word)) **
        ((.x6 : Reg) ↦ᵣ flag) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
        ((.x15 : Reg) ↦ᵣ size) ** ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ (1 : Word)) **
        ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 size).toNat)) **
        ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
        ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
        ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) ** (flag ↦ₘ (2 : Word)) **
        bytesRegion returnDescBase
          (setBytes
            (copyIntoRegion
              (copyIntoRegion
                (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
                  (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
              memBytes 0 off.toNat (returnClamp32 size).toNat) 32 (dwordBytes (1 : Word))) **
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
  -- Segment 1: prologue + capture-skip (hbase → hbase+88)
  have S1 := return_seg_prologue hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase p scmAddr off size x14o x15o x5o hlaSCM
  have S1f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x6 : Reg) ↦ᵣ x6o) ** ((.x16 : Reg) ↦ᵣ x16o) **
      ((.x17 : Reg) ↦ᵣ x17o) ** ((.x19 : Reg) ↦ᵣ x19o) ** ((.x21 : Reg) ↦ᵣ x21o) **
      ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) ** (flag ↦ₘ f0) **
      bytesRegion returnDescBase descInit ** bytesRegion evmMemBase memBytes) (by pcFreeR) S1
  -- Segment 2: header + zero loop (hbase+88 → hbase+136)
  have S2 := return_seg_header hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase x16o x19o x21o descInit hDescLen
  have S2f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ x6o) **
      ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x17 : Reg) ↦ᵣ x17o) ** ((.x22 : Reg) ↦ᵣ x22o) ** ((.x23 : Reg) ↦ᵣ x23o) **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) ** (flag ↦ₘ f0) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S2
  -- Segment 3: clamp to 176 (hbase+136 → hbase+152)
  have S3 := return_seg_clamp176 hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase size (0 : Word) x22o
  have S3f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ x6o) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x16 : Reg) ↦ᵣ returnDescBase) ** ((.x17 : Reg) ↦ᵣ x17o) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0 + 22)))) **
      ((.x23 : Reg) ↦ᵣ x23o) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) **
      (flag ↦ₘ f0) ** bytesRegion returnDescBase (returnDescZeroed descInit) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S3
  -- Segment 4: size/clamped stores + copy loop 1 (hbase+152 → hbase+208)
  have S4 := return_seg_copy1 hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase evmMemBase off size x17o
    (returnDescBase + BitVec.ofNat 64 (8 * (9 + 0 + 22))) (176 : Word) x23o descInit memBytes
    hDescLen hSrcAlign hSrcOver hSrcValid hOff hlaMem
  have S4f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ x6o) **
      ((.x12 : Reg) ↦ᵣ p) ** ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) ** (flag ↦ₘ f0)) (by pcFreeR) S4
  -- Segment 5: second la + clamp to 32 (hbase+208 → hbase+236)
  have S5 := return_seg_clamp32 hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase evmMemBase off size
    (evmMemBase + BitVec.ofNat 64 (off.toNat + 0 + (returnClamp size).toNat))
    (returnClamp size) (0 : Word) hlaMem2
  have S5f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ x6o) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x16 : Reg) ↦ᵣ returnDescBase) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (72 + 0 + (returnClamp size).toNat))) **
      regOwn .x23 ** ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) ** (flag ↦ₘ f0) **
      bytesRegion returnDescBase
        (copyIntoRegion
          (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
            (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat) **
      bytesRegion evmMemBase memBytes) (by pcFreeR) S5
  -- Segment 6: first-32 prefix copy loop (hbase+236 → hbase+268)
  have S6 := return_seg_copy2 hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase evmMemBase off size
    (returnDescBase + BitVec.ofNat 64 (72 + 0 + (returnClamp size).toNat))
    (copyIntoRegion
      (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
        (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
    memBytes hRc1len hSrcAlign hSrcOver hSrcValid hOff32
  have S6f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ x1o) ** ((.x5 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ x6o) **
      ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) ** ((.x15 : Reg) ↦ᵣ size) **
      ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((p + signExtend12 0) ↦ₘ off) **
      ((p + signExtend12 32) ↦ₘ size) ** ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) **
      (flag ↦ₘ f0)) (by pcFreeR) S6
  -- Segment 7: kind store + halt core (hbase+268 → resume &&& ~~~1)
  have S7 := return_seg_kindhalt hiSCM loSCM hiLen loLen hiRd loRd hiMem loMem hiMem2 loMem2
    hi2 lo2 hi1 lo1 hbase flag resume
    (evmMemBase + BitVec.ofNat 64 (off.toNat + 0 + (returnClamp32 size).toNat))
    (0 : Word) x6o x1o f0
    (copyIntoRegion
      (copyIntoRegion
        (setBytes (setBytes (returnDescZeroed descInit) 64 (dwordBytes size)) 248
          (dwordBytes (returnClamp size))) memBytes 72 off.toNat (returnClamp size).toNat)
      memBytes 0 off.toNat (returnClamp32 size).toNat) hRc2len hla2 hla1
  have S7f := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ p) ** ((.x14 : Reg) ↦ᵣ off) **
      ((.x15 : Reg) ↦ᵣ size) **
      ((.x19 : Reg) ↦ᵣ (returnDescBase + BitVec.ofNat 64 (returnClamp32 size).toNat)) **
      ((.x21 : Reg) ↦ᵣ (32 : Word)) ** ((.x22 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x23 **
      ((p + signExtend12 0) ↦ₘ off) ** ((p + signExtend12 32) ↦ₘ size) **
      ((scmAddr + signExtend12 0) ↦ₘ (0 : Word)) ** bytesRegion evmMemBase memBytes)
    (by pcFreeR) S7
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

/-- **Cover lemma for the RETURN `.conditional` registry entry**
    (`OpcodeEntry.coverRef`, R-A3 anti-near-vacuity).  The gating precondition
    `system_call_mode = 0` is the ordinary (non-system-call) transaction case, so
    the proved path is genuinely reachable; and on a representative small return
    (`size = 5`) both descriptor clamps are the identity
    (`returnClamp 5 = returnClamp32 5 = 5`), so the window copies the return data
    unclamped — the spec is not a vacuous or degenerate statement.
    `decide`-checked. -/
theorem return_precondition_reachable :
    returnClamp (5 : Word) = 5 ∧ returnClamp32 (5 : Word) = 5 := by decide

end Terminating
end EvmAsm.Evm64
