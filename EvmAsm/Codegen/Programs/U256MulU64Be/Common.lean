/-
  EvmAsm.Codegen.Programs.U256MulU64Be.Common

  Shared setup for the `u256_mul_u64_be` spec: program / base / code
  requirement abbreviations, the concrete `u256m_acc` accumulator facts
  (alignment, `la` composition), and the prologue / epilogue Hoare triples.

  Emitted layout anchors (base `GuestAddrs.u256_mul_u64_be = 0x800051c0`):
    +0   ADDI sp, sp, -48 ; +4..+24 SD ra/s0..s4 at sp+0..40
    +28  MV x8, x10 ; +32 MV x9, x11 ; +36 MV x18, x12
    +40  AUIPC x19, hi ; +44 ADDI x19, x19, lo   (la x19, u256m_acc)
    ...
    +320 LD ra, 0(sp) ; +324 LD s0, 8(sp) ; +328 LD s1, 16(sp)
    +332 LD s2, 24(sp) ; +336 LD s3, 32(sp) ; +340 LD s4, 40(sp)
    +344 ADDI sp, sp, 48 ; +348 JALR x0, ra, 0
-/
import EvmAsm.Codegen.Programs.U256MulU64Be.Basic
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Rv64.SAsm.TwoBreakWritable
import EvmAsm.Rv64.SAsm.AccumLoop
import EvmAsm.Rv64.LaResolve
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

/-- The emitted program under proof (byte-pinned by `#guard` next to
    `u256MulU64Be_prog` in `EvmAsm.Codegen.Programs.U256`). -/
abbrev mulProg : Program := u256MulU64Be_prog

/-- Linked base of `u256_mul_u64_be` (`0x800051c0`). -/
abbrev mulBase : Word := (GuestAddrs.u256_mul_u64_be : Nat)

/-- Whole-program code requirement. -/
abbrev mulCR : CodeReq := CodeReq.ofProg mulBase mulProg

/-- The 40-byte little-endian multiply accumulator in `.bss`
    (`0xa557f860`). -/
abbrev accBase : Word := (GuestAddrs.u256m_acc : Nat)

theorem accBase_align : accBase.toNat % 8 = 0 := by decide

-- ============================================================================
-- §1  Prologue
-- ============================================================================

/-- The 48-byte stack frame: six saved-register slots, modelled as six
    `memOwn` cells so loads/stores need no byte-list splitting. -/
abbrev frameSlots (spNew : Word) (vRa v8 v9 v18 v19 v20 : Word) : Assertion :=
  ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
  ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
  ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
  ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ v18) **
  ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ v19) **
  ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ v20)

/-- **Prologue** (+0..+44, 12 instructions): build the frame, save the six
    registers, latch the three argument registers into callee-saved slots,
    and materialise `x19 = u256m_acc`. -/
theorem prologue_spec (spOld vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (f0 f1 f2 f3 f4 f5 : Word) :
    cpsTripleWithin 12 mulBase (mulBase + 48) mulCR
      (((.x2 : Reg) ↦ᵣ spOld) ** ((.x1 : Reg) ↦ᵣ vRa) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x20 : Reg) ↦ᵣ v20) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        frameSlots (spOld + Rv64.signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5)
      (((.x2 : Reg) ↦ᵣ (spOld + Rv64.signExtend12 (-48 : BitVec 12))) **
        ((.x1 : Reg) ↦ᵣ vRa) **
        ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
        ((.x20 : Reg) ↦ᵣ v20) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        frameSlots (spOld + Rv64.signExtend12 (-48 : BitVec 12)) vRa v8 v9 v18 v19 v20) := by
  set spNew := spOld + Rv64.signExtend12 (-48 : BitVec 12)
  -- +0 ADDI sp, sp, -48
  have h0 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (addi_spec_gen_same_within .x2 spOld (-48 : BitVec 12) mulBase (by decide))
  -- +4 SD ra, 0(sp)
  have h1 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (sd_spec_within .x2 .x1 spNew vRa f0 (0 : BitVec 12) (mulBase + 4))
  rw [show mulBase + 4 + 4 = mulBase + 8 from by decide] at h1
  -- +8 SD s0, 8(sp)
  have h2 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (sd_spec_within .x2 .x8 spNew v8 f1 (8 : BitVec 12) (mulBase + 8))
  rw [show mulBase + 8 + 4 = mulBase + 12 from by decide] at h2
  -- +12 SD s1, 16(sp)
  have h3 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (sd_spec_within .x2 .x9 spNew v9 f2 (16 : BitVec 12) (mulBase + 12))
  rw [show mulBase + 12 + 4 = mulBase + 16 from by decide] at h3
  -- +16 SD s2, 24(sp)
  have h4 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (sd_spec_within .x2 .x18 spNew v18 f3 (24 : BitVec 12) (mulBase + 16))
  rw [show mulBase + 16 + 4 = mulBase + 20 from by decide] at h4
  -- +20 SD s3, 32(sp)
  have h5 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (sd_spec_within .x2 .x19 spNew v19 f4 (32 : BitVec 12) (mulBase + 20))
  rw [show mulBase + 20 + 4 = mulBase + 24 from by decide] at h5
  -- +24 SD s4, 40(sp)
  have h6 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (sd_spec_within .x2 .x20 spNew v20 f5 (40 : BitVec 12) (mulBase + 24))
  rw [show mulBase + 24 + 4 = mulBase + 28 from by decide] at h6
  -- +28 MV x8, x10
  have h7 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (mv_spec_gen_within .x8 .x10 aPtr v8 (mulBase + 28) (by decide))
  rw [show mulBase + 28 + 4 = mulBase + 32 from by decide] at h7
  -- +32 MV x9, x11
  have h8 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (mv_spec_gen_within .x9 .x11 b v9 (mulBase + 32) (by decide))
  rw [show mulBase + 32 + 4 = mulBase + 36 from by decide] at h8
  -- +36 MV x18, x12
  have h9 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (mv_spec_gen_within .x18 .x12 outPtr v18 (mulBase + 36) (by decide))
  rw [show mulBase + 36 + 4 = mulBase + 40 from by decide] at h9
  -- +40/+44 la x19, u256m_acc
  have hla := la_materialize_within (cr := mulCR) .x19 v19 (mulBase + 40) accBase (by decide)
    (by unfold mulBase accBase; decide) (by code_mem) (by code_mem)
  -- chain
  have hf0 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
      ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      frameSlots spNew f0 f1 f2 f3 f4 f5)
    (by pcf) h0
  have hf1 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
      ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ f1) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ f2) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ f3) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ f4) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ f5))
    (by pcf) h1
  have hf2 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x9 : Reg) ↦ᵣ v9) **
      ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ f2) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ f3) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ f4) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ f5))
    (by pcf) h2
  have hf3 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) **
      ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ f3) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ f4) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ f5))
    (by pcf) h3
  have hf4 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ f4) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ f5))
    (by pcf) h4
  have hf5 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ v18) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ f5))
    (by pcf) h5
  have hf6 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ v18) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ v19))
    (by pcf) h6
  have hf7 := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
      ((.x20 : Reg) ↦ᵣ v20) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) h7
  have hf8 := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ aPtr) **
      ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) h8
  have hf9 := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ aPtr) **
      ((.x9 : Reg) ↦ᵣ b) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) h9
  have hf10 := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ aPtr) **
      ((.x9 : Reg) ↦ᵣ b) ** ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) hla
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hf0 hf1
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf2
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf3
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf4
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf5
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf6
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf7
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf8
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf9
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf10
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

-- ============================================================================
-- §2  Epilogue
-- ============================================================================

/-- **Epilogue** (+320..+348, 8 instructions): restore the six saved
    registers, pop the frame, and return (`pc = vRa`, the slot-0 value).
    The frame cells stay owned (with their saved values) so the caller can
    reuse them. -/
theorem epilogue_spec (spNew vRa v8 v9 v18 v19 v20 : Word)
    (j1 j8 j9 j18 j19 j20 : Word)
    (hret : (vRa &&& ~~~(1 : Word)) = vRa) :
    cpsTripleWithin 8 (mulBase + 320) vRa mulCR
      (((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ j1) **
        ((.x8 : Reg) ↦ᵣ j8) ** ((.x9 : Reg) ↦ᵣ j9) **
        ((.x18 : Reg) ↦ᵣ j18) ** ((.x19 : Reg) ↦ᵣ j19) ** ((.x20 : Reg) ↦ᵣ j20) **
        frameSlots spNew vRa v8 v9 v18 v19 v20)
      (((.x2 : Reg) ↦ᵣ (spNew + Rv64.signExtend12 (48 : BitVec 12))) **
        ((.x1 : Reg) ↦ᵣ vRa) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
        frameSlots spNew vRa v8 v9 v18 v19 v20) := by
  -- +320 LD ra, 0(sp)
  have h0 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (ld_spec_within .x1 .x2 spNew j1 vRa (0 : BitVec 12) (mulBase + 320) (by decide))
  rw [show mulBase + 320 + 4 = mulBase + 324 from by decide] at h0
  -- +324 LD s0, 8(sp)
  have h1 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (ld_spec_within .x8 .x2 spNew j8 v8 (8 : BitVec 12) (mulBase + 324) (by decide))
  rw [show mulBase + 324 + 4 = mulBase + 328 from by decide] at h1
  -- +328 LD s1, 16(sp)
  have h2 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (ld_spec_within .x9 .x2 spNew j9 v9 (16 : BitVec 12) (mulBase + 328) (by decide))
  rw [show mulBase + 328 + 4 = mulBase + 332 from by decide] at h2
  -- +332 LD s2, 24(sp)
  have h3 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (ld_spec_within .x18 .x2 spNew j18 v18 (24 : BitVec 12) (mulBase + 332)
      (by decide))
  rw [show mulBase + 332 + 4 = mulBase + 336 from by decide] at h3
  -- +336 LD s3, 32(sp)
  have h4 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (ld_spec_within .x19 .x2 spNew j19 v19 (32 : BitVec 12) (mulBase + 336)
      (by decide))
  rw [show mulBase + 336 + 4 = mulBase + 340 from by decide] at h4
  -- +340 LD s4, 40(sp)
  have h5 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (ld_spec_within .x20 .x2 spNew j20 v20 (40 : BitVec 12) (mulBase + 340)
      (by decide))
  rw [show mulBase + 340 + 4 = mulBase + 344 from by decide] at h5
  -- +344 ADDI sp, sp, 48
  have h6 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (addi_spec_gen_same_within .x2 spNew (48 : BitVec 12) (mulBase + 344) (by decide))
  rw [show mulBase + 344 + 4 = mulBase + 348 from by decide] at h6
  -- +348 JALR x0, ra, 0
  have h7 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (EvmAsm.Evm64.ret_spec_within' (mulBase + 348) vRa)
  rw [hret] at h7
  -- frames
  have hf0 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ j8) ** ((.x9 : Reg) ↦ᵣ j9) **
      ((.x18 : Reg) ↦ᵣ j18) ** ((.x19 : Reg) ↦ᵣ j19) ** ((.x20 : Reg) ↦ᵣ j20) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ v18) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ v19) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ v20))
    (by pcf) h0
  have hf1 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x9 : Reg) ↦ᵣ j9) **
      ((.x18 : Reg) ↦ᵣ j18) ** ((.x19 : Reg) ↦ᵣ j19) ** ((.x20 : Reg) ↦ᵣ j20) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ v18) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ v19) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ v20))
    (by pcf) h1
  have hf2 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) **
      ((.x18 : Reg) ↦ᵣ j18) ** ((.x19 : Reg) ↦ᵣ j19) ** ((.x20 : Reg) ↦ᵣ j20) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ v18) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ v19) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ v20))
    (by pcf) h2
  have hf3 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x19 : Reg) ↦ᵣ j19) ** ((.x20 : Reg) ↦ᵣ j20) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ v19) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ v20))
    (by pcf) h3
  have hf4 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x20 : Reg) ↦ᵣ j20) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ v18) **
      ((spNew + Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ v20))
    (by pcf) h4
  have hf5 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
      ((spNew + Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ vRa) **
      ((spNew + Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ v8) **
      ((spNew + Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ v9) **
      ((spNew + Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ v18) **
      ((spNew + Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ v19))
    (by pcf) h5
  have hf6 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
      ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) h6
  have hf7 := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ (spNew + Rv64.signExtend12 (48 : BitVec 12))) **
      ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
      ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by pcf) h7
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hf0 hf1
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf2
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf3
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf4
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf5
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf6
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc hf7
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

end EvmAsm.Codegen.U256MulU64Be
