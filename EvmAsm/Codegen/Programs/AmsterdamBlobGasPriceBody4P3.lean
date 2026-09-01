/-
Split-out parts of the swapDiv core-window proof (see AmsterdamBlobGasPriceBody4Spec.lean).
File split only for the Codegen/Programs line cap; content unchanged.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody3Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody4P1
namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody4Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody3Spec

set_option maxRecDepth 8000

theorem swapdiv_p3 (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 4 (PriceK + 704) (PriceK + 720) priceCode
      (((.x6 ↦ᵣ (rv64_mulhu taylorDW iVal)) ** ((.x0 ↦ᵣ (0 : Word)) ** ⌜(rv64_mulhu taylorDW iVal) = (0 : Word)⌝)) ** ((.x2 ↦ᵣ newSp) **
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
            (((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 0) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0)** ((.x2 ↦ᵣ newSp) **
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
        FR)) := by
  have hmvz := mv_spec_gen_within .x6 .x0 (0 : Word) (rv64_mulhu taylorDW iVal) (PriceK + 704) (by decide)
  have hmvzF : cpsTripleWithin 1 (PriceK + 704) (PriceK + 708) priceCode
      (((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (rv64_mulhu taylorDW iVal))) ** ((.x2 ↦ᵣ newSp) **
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
      (((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) **
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
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hmvz)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[176]'(by decide) = .MV .x6 .x0 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 704) amsterdamBlobGasPriceU256_prog
      176 (.MV .x6 .x0) (by decide) (by decide) hins (by decide) a i hi
  have hmvt := mv_spec_gen_within .x30 .x19 (newSp + signExtend12 (112 : BitVec 12)) v30 (PriceK + 708) (by decide)
  have hmvtF : cpsTripleWithin 1 (PriceK + 708) (PriceK + 712) priceCode
      (((.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** (.x30 ↦ᵣ v30)) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        FR))
      (((.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** (.x30 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hmvt)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[177]'(by decide) = .MV .x30 .x19 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 708) amsterdamBlobGasPriceU256_prog
      177 (.MV .x30 .x19) (by decide) (by decide) hins (by decide) a i hi
  have hmvtF' : cpsTripleWithin 1 (PriceK + 708) (PriceK + 712) priceCode
      (((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) **
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
      (((.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** (.x30 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) hmvtF
  have hs1 := cpsTripleWithin_seq_same_cr hmvzF hmvtF'
  have haddi := addi_spec_gen_same_within .x30 (newSp + signExtend12 (112 : BitVec 12)) (40 : BitVec 12) (PriceK + 712)
    (by decide)
  have haddiF : cpsTripleWithin 1 (PriceK + 712) (PriceK + 716) priceCode
      ((.x30 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        FR))
      ((.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) haddi)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[178]'(by decide) =
        .ADDI .x30 .x30 (40 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 712) amsterdamBlobGasPriceU256_prog
      178 (.ADDI .x30 .x30 (40 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi
  have haddiF' : cpsTripleWithin 1 (PriceK + 712) (PriceK + 716) priceCode
      (((.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** (.x30 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        FR))
      ((.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) haddiF
  have hs2 := cpsTripleWithin_seq_same_cr hs1 haddiF'
  have hli := li_spec_gen_within .x31 v31 (6 : Word) (PriceK + 716) (by decide)
  have hliF : cpsTripleWithin 1 (PriceK + 716) (PriceK + 720) priceCode
      ((.x31 ↦ᵣ v31) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) **
        FR))
      ((.x31 ↦ᵣ (6 : Word)) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) **
        FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hli)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[179]'(by decide) = .LI .x31 (6 : Word) := by
      decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 716) amsterdamBlobGasPriceU256_prog
      179 (.LI .x31 (6 : Word)) (by decide) (by decide) hins (by decide) a i hi
  have hliF' : cpsTripleWithin 1 (PriceK + 716) (PriceK + 720) priceCode
      ((.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        FR))
      ((.x31 ↦ᵣ (6 : Word)) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) **
        FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hliF
  have hliF'' : cpsTripleWithin 1 (PriceK + 716) (PriceK + 720) priceCode
      ((.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        FR))
      ((.x31 ↦ᵣ lcnt 0) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) **
        FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; rw [show lcnt 0 = (6 : Word) from rfl]; exact hx) hliF'
  have hs3 := cpsTripleWithin_seq_same_cr hs2 hliF''
  have hP3raw : cpsTripleWithin 4 (PriceK + 704) (PriceK + 720) priceCode
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
            (((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 0) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0)** ((.x2 ↦ᵣ newSp) **
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
        FR)) := by
    have hpost3 : ∀ h, (((.x31 ↦ᵣ lcnt 0) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
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
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) **
        FR)) h) →
        ((      (((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 0) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0)** ((.x2 ↦ᵣ newSp) **
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
        FR))) h) := by
      intro h hx; xperm_hyp hx
    have hpre3 : ∀ h, (((.x6 ↦ᵣ (rv64_mulhu taylorDW iVal)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x2 ↦ᵣ newSp) **
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
        FR)) h →
        (((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (rv64_mulhu taylorDW iVal))) ** ((.x2 ↦ᵣ newSp) **
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
        FR)) h := by
      intro h hx; xperm_hyp hx
    exact cpsTripleWithin_weaken hpre3 hpost3 hs3
  have hP3' : cpsTripleWithin 4 (PriceK + 704) (PriceK + 720) priceCode
      (((.x6 ↦ᵣ (rv64_mulhu taylorDW iVal)) ** ((.x0 ↦ᵣ (0 : Word)) ** ⌜(rv64_mulhu taylorDW iVal) = (0 : Word)⌝)) ** ((.x2 ↦ᵣ newSp) **
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
            (((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ ((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12))) ** (.x31 ↦ᵣ lcnt 0) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((newSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ p0)** ((.x2 ↦ᵣ newSp) **
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
        FR)) :=
    cpsTripleWithin_weaken pure_drop_mid (fun _ hx => hx) hP3raw
  exact hP3'
