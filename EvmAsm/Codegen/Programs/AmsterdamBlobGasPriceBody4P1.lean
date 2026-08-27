/-
Split-out parts of the swapDiv core-window proof (see AmsterdamBlobGasPriceBody4Spec.lean).
File split only for the Codegen/Programs line cap; content unchanged.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody3Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody4Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody2Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody3Spec

set_option maxRecDepth 8000

/-- Drop a trailing pure from the second position of a two-atom lead group. -/
theorem pure_drop_mid {L1 L2 : Assertion} {P : Prop} {R : Assertion} :
    ∀ h, ((L1 ** (L2 ** ⌜P⌝)) ** R) h → ((L1 ** L2) ** R) h := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hl1, hr⟩ := hx
  obtain ⟨g1, g2, gd, gu, hg1, hg2⟩ := hl1
  rw [sepConj_comm'] at hg2
  obtain ⟨e, g2', ed, eu, he, hL2⟩ := hg2
  obtain ⟨heE, -⟩ := he
  have hg2eq : g2 = g2' := by
    rw [← eu, heE]
    exact PartialState.union_empty_left
  rw [hg2eq] at gd gu
  exact ⟨h1, h2, hd, hu, ⟨g1, g2', gd, gu, hg1, hL2⟩, hr⟩

@[reducible] def QOVFDIV (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 : Word)
    (FR : Assertion) : Assertion :=
  (((.x6 ↦ᵣ (rv64_mulhu taylorDW iVal)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rv64_mulhu taylorDW iVal) ≠ (0 : Word)⌝) **
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

@[reducible] def QBACK (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 _v7 _v28 _v29 _v30 _v31 : Word)
    (FR : Assertion) : Assertion :=
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

theorem swapdiv_p1 (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 5 (PriceK + 680) (PriceK + 700) priceCode
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
        FR)) := by
  have h1 := mv_spec_gen_within .x5 .x19 (newSp + signExtend12 (64 : BitVec 12)) v5 (PriceK + 680) (by decide)
  have h1F : cpsTripleWithin 1 (PriceK + 680) (PriceK + 684) priceCode
      (((.x19 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ v5)) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR))
      (((.x19 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h1)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[170]'(by decide) = .MV .x5 .x19 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 680) amsterdamBlobGasPriceU256_prog
      170 (.MV .x5 .x19) (by decide) (by decide) hins (by decide) a i hi
  have h2 := mv_spec_gen_within .x19 .x20 (newSp + signExtend12 (112 : BitVec 12)) (newSp + signExtend12 (64 : BitVec 12)) (PriceK + 684) (by decide)
  have h2F : cpsTripleWithin 1 (PriceK + 684) (PriceK + 688) priceCode
      (((.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** (.x19 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
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
        FR))
      (((.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
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
        FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h2)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[171]'(by decide) = .MV .x19 .x20 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 684) amsterdamBlobGasPriceU256_prog
      171 (.MV .x19 .x20) (by decide) (by decide) hins (by decide) a i hi
  have h2F' : cpsTripleWithin 1 (PriceK + 684) (PriceK + 688) priceCode
      (((.x19 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR))
      (((.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
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
        FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) h2F
  have hs1 := cpsTripleWithin_seq_same_cr h1F h2F'
  have h3 := mv_spec_gen_within .x20 .x5 (newSp + signExtend12 (64 : BitVec 12)) (newSp + signExtend12 (112 : BitVec 12)) (PriceK + 688) (by decide)
  have h3F : cpsTripleWithin 1 (PriceK + 688) (PriceK + 692) priceCode
      (((.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) ** (.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR))
      (((.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) ** (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h3)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[172]'(by decide) = .MV .x20 .x5 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 688) amsterdamBlobGasPriceU256_prog
      172 (.MV .x20 .x5) (by decide) (by decide) hins (by decide) a i hi
  have h3F' : cpsTripleWithin 1 (PriceK + 688) (PriceK + 692) priceCode
      (((.x20 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) ** (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
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
        FR))
      (((.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) ** (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) h3F
  have hs2 := cpsTripleWithin_seq_same_cr hs1 h3F'
  have h4 := mul_spec_gen_within .x5 .x9 .x18 (newSp + signExtend12 (64 : BitVec 12)) taylorDW iVal (PriceK + 692)
    (by decide)
  have h4F : cpsTripleWithin 1 (PriceK + 692) (PriceK + 696) priceCode
      (((.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR))
      (((.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR)) := by
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h4)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[173]'(by decide) =
        .MUL .x5 .x9 .x18 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 692) amsterdamBlobGasPriceU256_prog
      173 (.MUL .x5 .x9 .x18) (by decide) (by decide) hins (by decide) a i hi
  have h4F' : cpsTripleWithin 1 (PriceK + 692) (PriceK + 696) priceCode
      (((.x5 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) ** (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12)))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR))
      (((.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) h4F
  have hs3 := cpsTripleWithin_seq_same_cr hs2 h4F'
  have h5 := mulhu_spec_gen_within .x6 .x9 .x18 v6 taylorDW iVal (PriceK + 696) (by decide)
  have h5F : cpsTripleWithin 1 (PriceK + 696) (PriceK + 700) priceCode
      (((.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) ** (.x6 ↦ᵣ v6)) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
      (((.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) ** (.x6 ↦ᵣ (rv64_mulhu taylorDW iVal))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
    refine cpsTripleWithin_extend_code ?_ (cpsTripleWithin_frameR _ (by pcFree; exact hFR) h5)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[174]'(by decide) =
        .MULHU .x6 .x9 .x18 := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 696) amsterdamBlobGasPriceU256_prog
      174 (.MULHU .x6 .x9 .x18) (by decide) (by decide) hins (by decide) a i hi
  have h5F' : cpsTripleWithin 1 (PriceK + 696) (PriceK + 700) priceCode
      (((.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x19 ↦ᵣ (newSp + signExtend12 (112 : BitVec 12))) **
        (.x20 ↦ᵣ (newSp + signExtend12 (64 : BitVec 12))) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
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
        FR))
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
        FR)) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx)
      (by intro h hx; xperm_hyp hx) h5F
  exact cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (fun _ hx => hx)
    (cpsTripleWithin_seq_same_cr hs3 h5F')
