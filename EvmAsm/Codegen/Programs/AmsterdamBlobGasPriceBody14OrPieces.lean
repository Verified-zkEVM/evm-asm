/- Parametric OR-chain leaves for the Body14 Taylor-round proof. -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody10Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody11Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody13Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody13Spec

set_option maxRecDepth 8000

theorem or2p_li (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 144) (PriceK + 148) priceCode
      (((.x5 ↦ᵣ v5) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) (((.x5 ↦ᵣ (0 : Word)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hli := li_spec_gen_within .x5 v5 (0 : Word) (PriceK + 144) (by decide)
  have hliF : cpsTripleWithin 1 (PriceK + 144) (PriceK + 148) priceCode
      ((.x5 ↦ᵣ v5) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) ((.x5 ↦ᵣ (0 : Word)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         frameSlotsSaved priceFrame newSp vals ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hli)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[36]'(by decide) = .LI .x5 (0 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 144) amsterdamBlobGasPriceU256_prog
      36 (.LI .x5 (0 : Word)) (by decide) (by decide) hins (by decide) a i hi

  exact hliF
theorem or2p_ld0 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 148) (PriceK + 152) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ v6) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld0 := ld_spec_gen_within .x6 .x19 (AB) v6 a0 (0 : BitVec 12)
    (PriceK + 148) (by decide)
  have hld0F : cpsTripleWithin 1 (PriceK + 148) (PriceK + 152) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ v6) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld0)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[37]'(by decide) = .LD .x6 .x19 (0 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 148) amsterdamBlobGasPriceU256_prog
      37 (.LD .x6 .x19 (0 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld0F
theorem or2p_or0 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 152) (PriceK + 156) priceCode
      ((((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor0 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (0 : Word) a0 (PriceK + 152) (by decide)
  have hor0F : cpsTripleWithin 1 (PriceK + 152) (PriceK + 156) priceCode
      (((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a0)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor0)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[38]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 152) amsterdamBlobGasPriceU256_prog
      38 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor0F
theorem or2p_ld1 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 156) (PriceK + 160) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld1 := ld_spec_gen_within .x6 .x19 (AB) a0 a1 (8 : BitVec 12)
    (PriceK + 156) (by decide)
  have hld1F : cpsTripleWithin 1 (PriceK + 156) (PriceK + 160) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((0 : Word) ||| a0)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld1)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[39]'(by decide) = .LD .x6 .x19 (8 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 156) amsterdamBlobGasPriceU256_prog
      39 (.LD .x6 .x19 (8 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld1F
theorem or2p_or1 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 160) (PriceK + 164) priceCode
      ((((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor1 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((0 : Word) ||| a0) a1 (PriceK + 160) (by decide)
  have hor1F : cpsTripleWithin 1 (PriceK + 160) (PriceK + 164) priceCode
      (((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a1)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor1)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[40]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 160) amsterdamBlobGasPriceU256_prog
      40 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor1F
theorem or2p_ld2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 164) (PriceK + 168) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld2 := ld_spec_gen_within .x6 .x19 (AB) a1 a2 (16 : BitVec 12)
    (PriceK + 164) (by decide)
  have hld2F : cpsTripleWithin 1 (PriceK + 164) (PriceK + 168) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld2)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[41]'(by decide) = .LD .x6 .x19 (16 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 164) amsterdamBlobGasPriceU256_prog
      41 (.LD .x6 .x19 (16 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld2F
theorem or2p_or2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 168) (PriceK + 172) priceCode
      ((((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor2 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (((0 : Word) ||| a0) ||| a1) a2 (PriceK + 168) (by decide)
  have hor2F : cpsTripleWithin 1 (PriceK + 168) (PriceK + 172) priceCode
      (((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a2)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor2)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[42]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 168) amsterdamBlobGasPriceU256_prog
      42 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor2F
theorem or2p_ld3 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 172) (PriceK + 176) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld3 := ld_spec_gen_within .x6 .x19 (AB) a2 a3 (24 : BitVec 12)
    (PriceK + 172) (by decide)
  have hld3F : cpsTripleWithin 1 (PriceK + 172) (PriceK + 176) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld3)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[43]'(by decide) = .LD .x6 .x19 (24 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 172) amsterdamBlobGasPriceU256_prog
      43 (.LD .x6 .x19 (24 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld3F
theorem or2p_or3 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 176) (PriceK + 180) priceCode
      ((((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor3 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((((0 : Word) ||| a0) ||| a1) ||| a2) a3 (PriceK + 176) (by decide)
  have hor3F : cpsTripleWithin 1 (PriceK + 176) (PriceK + 180) priceCode
      (((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a3)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor3)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[44]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 176) amsterdamBlobGasPriceU256_prog
      44 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor3F
theorem or2p_ld4 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 180) (PriceK + 184) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld4 := ld_spec_gen_within .x6 .x19 (AB) a3 a4 (32 : BitVec 12)
    (PriceK + 180) (by decide)
  have hld4F : cpsTripleWithin 1 (PriceK + 180) (PriceK + 184) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld4)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[45]'(by decide) = .LD .x6 .x19 (32 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 180) amsterdamBlobGasPriceU256_prog
      45 (.LD .x6 .x19 (32 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld4F
theorem or2p_or4 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 184) (PriceK + 188) priceCode
      ((((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor4 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) a4 (PriceK + 184) (by decide)
  have hor4F : cpsTripleWithin 1 (PriceK + 184) (PriceK + 188) priceCode
      (((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a4)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor4)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[46]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 184) amsterdamBlobGasPriceU256_prog
      46 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor4F
theorem or2p_ld5 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 188) (PriceK + 192) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a5) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) := by
  have hld5 := ld_spec_gen_within .x6 .x19 (AB) a4 a5 (40 : BitVec 12)
    (PriceK + 188) (by decide)
  have hld5F : cpsTripleWithin 1 (PriceK + 188) (PriceK + 192) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) (((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a5) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x20 ↦ᵣ (PB)) **
         (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
         (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
         (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
         (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hld5)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[47]'(by decide) = .LD .x6 .x19 (40 : BitVec 12) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 188) amsterdamBlobGasPriceU256_prog
      47 (.LD .x6 .x19 (40 : BitVec 12)) (by decide) (by decide) hins (by decide) a i hi

  exact hld5F
theorem or2p_or5 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 192) (PriceK + 196) priceCode
      ((((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) ((((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR))) := by
  have hor5 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) a5 (PriceK + 192) (by decide)
  have hor5F : cpsTripleWithin 1 (PriceK + 192) (PriceK + 196) priceCode
      (((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x6 ↦ᵣ a5)) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
         (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
         (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
         (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
         (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
         (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
         (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
         (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
         (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
         (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
         (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
         (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
         FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hor5)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[48]'(by decide) = .OR .x5 .x5 .x6 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 192) amsterdamBlobGasPriceU256_prog
      48 (.OR .x5 .x5 .x6) (by decide) (by decide) hins (by decide) a i hi

  exact hor5F

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

