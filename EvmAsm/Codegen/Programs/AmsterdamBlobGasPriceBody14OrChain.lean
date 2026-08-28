/- Composition of the parametric Body14 OR-chain leaves. -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14OrPieces

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody13Spec

set_option maxRecDepth 8000

/-- Parametric or-chain window (13 instrs, PriceK+144..196): x5 := OR of the six
acc limbs; PB-parametric cells (safe for both parities). -/
theorem or_chainP2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 13 (PriceK + 144) (PriceK + 196) priceCode
      (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
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
       FR))
      (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x6 ↦ᵣ a5) **
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
  have hli := or2p_li newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 FR hFR
  have hld0 := or2p_ld0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v6 v7 v28 v29 v30 v31 FR hFR
  have hld0F' : cpsTripleWithin 1 (PriceK + 148) (PriceK + 152) priceCode
      (((.x5 ↦ᵣ (0 : Word)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld0
  have hor0 := or2p_or0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor0F' : cpsTripleWithin 1 (PriceK + 152) (PriceK + 156) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a0) ** (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a0)) **
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
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor0
  have hld1 := or2p_ld1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld1F' : cpsTripleWithin 1 (PriceK + 156) (PriceK + 160) priceCode
      ((((.x5 ↦ᵣ ((0 : Word) ||| a0)) ** (.x6 ↦ᵣ a0)) **
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
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld1
  have hor1 := or2p_or1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor1F' : cpsTripleWithin 1 (PriceK + 160) (PriceK + 164) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a1) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a1)) **
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
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor1
  have hld2 := or2p_ld2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld2F' : cpsTripleWithin 1 (PriceK + 164) (PriceK + 168) priceCode
      ((((.x5 ↦ᵣ (((0 : Word) ||| a0) ||| a1)) ** (.x6 ↦ᵣ a1)) **
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
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld2
  have hor2 := or2p_or2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor2F' : cpsTripleWithin 1 (PriceK + 168) (PriceK + 172) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a2) ** (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a2)) **
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
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor2
  have hld3 := or2p_ld3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld3F' : cpsTripleWithin 1 (PriceK + 172) (PriceK + 176) priceCode
      ((((.x5 ↦ᵣ ((((0 : Word) ||| a0) ||| a1) ||| a2)) ** (.x6 ↦ᵣ a2)) **
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
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld3
  have hor3 := or2p_or3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor3F' : cpsTripleWithin 1 (PriceK + 176) (PriceK + 180) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a3) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a3)) **
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
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor3
  have hld4 := or2p_ld4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld4F' : cpsTripleWithin 1 (PriceK + 180) (PriceK + 184) priceCode
      ((((.x5 ↦ᵣ (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3)) ** (.x6 ↦ᵣ a3)) **
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
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld4
  have hor4 := or2p_or4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor4F' : cpsTripleWithin 1 (PriceK + 184) (PriceK + 188) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a4) ** (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a4)) **
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
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor4
  have hld5 := or2p_ld5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hld5F' : cpsTripleWithin 1 (PriceK + 188) (PriceK + 192) priceCode
      ((((.x5 ↦ᵣ ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4)) ** (.x6 ↦ᵣ a4)) **
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
         FR))) ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a5) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hld5
  have hor5 := or2p_or5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR hFR
  have hor5F' : cpsTripleWithin 1 (PriceK + 192) (PriceK + 196) priceCode
      ((((.x19 ↦ᵣ (AB)) ** (.x6 ↦ᵣ a5) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5)) **
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
         (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR))) ((((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x6 ↦ᵣ a5)) **
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
         FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx) hor5
  have hs1 := cpsTripleWithin_seq_same_cr hli hld0F'
  have hs2 := cpsTripleWithin_seq_same_cr hs1 hor0F'
  have hs3 := cpsTripleWithin_seq_same_cr hs2 hld1F'
  have hs4 := cpsTripleWithin_seq_same_cr hs3 hor1F'
  have hs5 := cpsTripleWithin_seq_same_cr hs4 hld2F'
  have hs6 := cpsTripleWithin_seq_same_cr hs5 hor2F'
  have hs7 := cpsTripleWithin_seq_same_cr hs6 hld3F'
  have hs8 := cpsTripleWithin_seq_same_cr hs7 hor3F'
  have hs9 := cpsTripleWithin_seq_same_cr hs8 hld4F'
  have hs10 := cpsTripleWithin_seq_same_cr hs9 hor4F'
  have hs11 := cpsTripleWithin_seq_same_cr hs10 hld5F'
  have hs12 := cpsTripleWithin_seq_same_cr hs11 hor5F'
  exact cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) hs12

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

