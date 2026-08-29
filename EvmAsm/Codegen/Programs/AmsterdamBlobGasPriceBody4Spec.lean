/-
Split-out parts of the swapDiv core-window proof (see AmsterdamBlobGasPriceBody4Spec.lean).
File split only for the Codegen/Programs line cap; content unchanged.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody3Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody4P1
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody4P3
namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody4Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody3Spec

set_option maxRecDepth 8000

theorem swapdiv_core (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 3894 (PriceK + 680) priceCode
      ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) **
        (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)
      [(PriceK + 964, QOVFDIV newSp excess outPtr iVal vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR),
       (PriceK + 144, QBACK newSp excess outPtr iVal vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR)] := by
  -- Phase 1 (proven separately): swap + divisor mul/mulhu
  have hP1 := swapdiv_p1 newSp excess outPtr iVal vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 FR hFR
  -- Overflow dispatch: bnez t1 (P+700) -> ovf P+964 / fall P+704
  have hb := bne_spec_gen_within .x6 .x0 (264 : BitVec 13) (rv64_mulhu taylorDW iVal) (0 : Word) (PriceK + 700)
  rw [show (PriceK + 700 : Word) + signExtend13 (264 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (264 : BitVec 13) = (264 : Word) from by decide]; decide,
    show (PriceK + 700 : Word) + 4 = PriceK + 704 from by decide] at hb
  have hbF := cpsBranchWithin_frameR ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR) (by pcFree; exact hFR) hb
  have hbE : cpsBranchWithin 1 (PriceK + 700) priceCode
      (((.x6 ↦ᵣ (rv64_mulhu taylorDW iVal)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))
      (PriceK + 964)
      (((.x6 ↦ᵣ (rv64_mulhu taylorDW iVal)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rv64_mulhu taylorDW iVal) ≠ (0 : Word)⌝) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))
      (PriceK + 704)
      (((.x6 ↦ᵣ (rv64_mulhu taylorDW iVal)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rv64_mulhu taylorDW iVal) = (0 : Word)⌝) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)) := by
    refine cpsBranchWithin_extend_code ?_ hbF
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[175]'(by decide) =
        .BNE .x6 .x0 (264 : BitVec 13) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 700) amsterdamBlobGasPriceU256_prog
      175 (.BNE .x6 .x0 (264 : BitVec 13)) (by decide) (by decide) hins (by decide) a i hi
  have hB := cpsTripleWithin_seq_cpsBranchWithin_same_cr hP1 hbE
  -- Phase 3: mv t1,zero; mv t5,s3; addi t5,40; li t6,6 (4 instrs, P+704 -> P+720), manual
  have hP3' := swapdiv_p3 newSp excess outPtr iVal vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  -- The 6-limb fold
  have hLF := swapdiv_limbfold (taylorDW * iVal) (newSp + signExtend12 (112 : BitVec 12)) p5 p4 p3 p2 p1 p0 v7 v28 v29
    ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR) (by pcFree; exact hFR)
  have hA := cpsTripleWithin_seq_same_cr hP3' hLF
  -- Epilogue: i++ and back-edge
  have hEP1l := addi_spec_gen_same_within .x18 iVal (1 : BitVec 12) (PriceK + 796) (by decide)
  have hEP1F : cpsTripleWithin 1 (PriceK + 796) (PriceK + 800) priceCode
      ((.x18 ↦ᵣ iVal) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)))
      ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hEP1l)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[199]'(by decide) =
        .ADDI .x18 .x18 (1 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 796) amsterdamBlobGasPriceU256_prog
      199 (.ADDI .x18 .x18 (1 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have hEP1 : cpsTripleWithin 1 (PriceK + 796) (PriceK + 800) priceCode
            (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))
      ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hEP1F
  have hB2 := cpsTripleWithin_seq_same_cr hA hEP1
  have hj := jal_x0_spec_gen_within (-656 : BitVec 21) (PriceK + 800)
  rw [show (PriceK + 800 : Word) + signExtend21 (-656 : BitVec 21) = PriceK + 144 from by
      rw [show signExtend21 (-656 : BitVec 21) = (-656 : Word) from by decide]; decide] at hj
  have hjF0 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)))
    (by pcFree; exact hFR) hj
  have hpre4 : ∀ h, ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))) h →
      ((empAssertion ** ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)))) h) := by
    intro h hx
    exact ⟨PartialState.empty, h, PartialState.Disjoint_empty_left,
      PartialState.union_empty_left, rfl, hx⟩
  have hjF : cpsTripleWithin 1 (PriceK + 800) (PriceK + 144)
      (CodeReq.singleton (PriceK + 800) (.JAL .x0 (-656 : BitVec 21)))
      ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)))
      ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))) :=
    have hjF1 : cpsTripleWithin 1 (PriceK + 800) (PriceK + 144)
        (CodeReq.singleton (PriceK + 800) (.JAL .x0 (-656 : BitVec 21)))
        (empAssertion ** ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))))
        (empAssertion ** ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)))) :=
      hjF0
    have ho4 : ∀ h,
        ((empAssertion ** ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)))) h) →
        (((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))) h) := by
      intro h hx
      obtain ⟨h1, h2, hd, hu, he, hF⟩ := hx
      have h1e : h1 = PartialState.empty := he
      rw [h1e, PartialState.union_empty_left] at hu
      rw [hu] at hF
      exact hF
    cpsTripleWithin_weaken hpre4 ho4 hjF1
  have hEP2 : cpsTripleWithin 1 (PriceK + 800) (PriceK + 144) priceCode
      ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)))
      ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))) := by
    refine cpsTripleWithin_extend_code ?_ hjF
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[200]'(by decide) =
        .JAL .x0 (-656 : BitVec 21) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 800) amsterdamBlobGasPriceU256_prog
      200 (.JAL .x0 (-656 : BitVec 21)) (by decide) (by decide) hins (by decide) a i hi
  have hFALL := cpsTripleWithin_seq_same_cr hB2 hEP2
  have hFin := cpsBranchWithin_seq_cpsTripleWithin_same_cr hB hFALL (fun _ hx => hx)
  exact cpsBranchWithin_as_cpsNBranchWithin hFin

#print axioms swapdiv_core

