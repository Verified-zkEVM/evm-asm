/-
Parametric mul6 window (instrs 108..169) of `amsterdam_blob_gas_price_u256`
(#12851 outer-loop assembly): identical to `mul6_core` but with the acc/prod
buffer bases as parameters `AB`/`PB`, so the same theorem instantiates at
both buffer orientations of the outer loop (x19/x20 swap each iteration).
Mechanical copy of Body2Spec's mul6 block with renaming + base substitution.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec

set_option maxRecDepth 8000

/-! ## mul6P window (instrs 108..169, `PriceK+432 .. PriceK+680`) -/

private theorem pure_drop_mid {L1 L2 : Assertion} {P : Prop} {R : Assertion} :
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


@[reducible] def mul6PQOVF0 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) : Assertion :=
  (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0) ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
    (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a0) **
    (.x6 ↦ᵣ (a0 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a0 excess)) **
    (.x28 ↦ᵣ ((a0 * excess) + (0 : Word))) ** (.x30 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) **
    (.x31 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ p0) ** (((PB) + signExtend12 8) ↦ₘ p1) **
    (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
    (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))

@[reducible] def mul6PQOVF1 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) : Assertion :=
  (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0) ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
    (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a1) **
    (.x6 ↦ᵣ (a1 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a1 excess)) **
    (.x28 ↦ᵣ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) **
    (.x31 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ p1) **
    (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
    (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))

@[reducible] def mul6PQOVF2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) : Assertion :=
  (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0) ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
    (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a2) **
    (.x6 ↦ᵣ (a2 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a2 excess)) **
    (.x28 ↦ᵣ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) **
    (.x31 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
    (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))

@[reducible] def mul6PQOVF3 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) : Assertion :=
  (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0) ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
    (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a3) **
    (.x6 ↦ᵣ (a3 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a3 excess)) **
    (.x28 ↦ᵣ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) **
    (.x31 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ p3) **
    (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))

@[reducible] def mul6PQOVF4 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5 : Word) : Assertion :=
  (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0) ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
    (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a4) **
    (.x6 ↦ᵣ (a4 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a4 excess)) **
    (.x28 ↦ᵣ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) **
    (.x31 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))

@[reducible] def mul6PQOVF5 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5 : Word) : Assertion :=
  (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0) ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
    (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
    (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
    (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) **
    (.x31 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))

@[reducible] def mul6PQOVFF (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) : Assertion :=
  (((.x31 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
    (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
    (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
    (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) **
    (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))

@[reducible] def mul6PQFALL (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) : Assertion :=
  (((.x31 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) = (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
    (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
    (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
    (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
    (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
    (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) **
    (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
    (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))

@[reducible] def mul6PPRE (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
  (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
  (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
  (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
  (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
  (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ v5) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
  (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
  (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
  (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
  (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
  (((PB) + signExtend12 0) ↦ₘ p0) ** (((PB) + signExtend12 8) ↦ₘ p1) **
  (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
  (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
  (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
  (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
  (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)

private theorem mul6P_pre0 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word) :
    cpsTripleWithin 8 (PriceK + 432) (PriceK + 464) priceCode
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ v5) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ p0) ** (((PB) + signExtend12 8) ↦ₘ p1) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a0) **
        (.x6 ↦ᵣ (a0 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a0 excess)) **
        (.x28 ↦ᵣ ((a0 * excess) + (0 : Word))) ** (.x30 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ p0) ** (((PB) + signExtend12 8) ↦ₘ p1) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))) := by
  have hli0 := li_spec_gen_within .x31 v31 (0 : Word) (PriceK + 432) (by decide)
  have hldA0 := ld_spec_gen_within .x5 .x19 (AB) v5 a0 (0 : BitVec 12) (PriceK + 436) (by decide)
  have hmul0 := mul_spec_gen_within .x6 .x5 .x8 v6 a0 excess (PriceK + 440) (by decide)
  have hmhu0 := mulhu_spec_gen_within .x7 .x5 .x8 v7 a0 excess (PriceK + 444) (by decide)
  have had10 := add_spec_gen_within .x28 .x6 .x31 (a0 * excess) (0 : Word) v28 (PriceK + 448) (by decide)
  have hsl10 := sltu_spec_gen_within .x29 .x28 .x6 v29 ((a0 * excess) + (0 : Word)) (a0 * excess) (PriceK + 452) (by decide)
  have had20 := add_spec_gen_within .x30 .x7 .x29 (rv64_mulhu a0 excess) (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0) v30 (PriceK + 456) (by decide)
  have hsl20 := sltu_spec_gen_within .x29 .x30 .x7 (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0) ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) (PriceK + 460) (by decide)
  runBlock hli0 hldA0 hmul0 hmhu0 had10 hsl10 had20 hsl20

private theorem mul6P_pre1 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 7 (PriceK + 476) (PriceK + 504) priceCode
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a0) **
      (.x6 ↦ᵣ (a0 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a0 excess)) **
      (.x28 ↦ᵣ ((a0 * excess) + (0 : Word))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ p1) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a1) **
        (.x6 ↦ᵣ (a1 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a1 excess)) **
        (.x28 ↦ᵣ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ p1) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))) := by
  have hldA1 := ld_spec_gen_within .x5 .x19 (AB) a0 a1 (8 : BitVec 12) (PriceK + 476) (by decide)
  have hmul1 := mul_spec_gen_within .x6 .x5 .x8 (a0 * excess) a1 excess (PriceK + 480) (by decide)
  have hmhu1 := mulhu_spec_gen_within .x7 .x5 .x8 (rv64_mulhu a0 excess) a1 excess (PriceK + 484) (by decide)
  have had11 := add_spec_gen_within .x28 .x6 .x31 (a1 * excess) ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) ((a0 * excess) + (0 : Word)) (PriceK + 488) (by decide)
  have hsl11 := sltu_spec_gen_within .x29 .x28 .x6 (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) (PriceK + 492) (by decide)
  have had21 := add_spec_gen_within .x30 .x7 .x29 (rv64_mulhu a1 excess) (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0) ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (PriceK + 496) (by decide)
  have hsl21 := sltu_spec_gen_within .x29 .x30 .x7 (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0) ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) (PriceK + 500) (by decide)
  runBlock hldA1 hmul1 hmhu1 had11 hsl11 had21 hsl21

private theorem mul6P_pre2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 7 (PriceK + 516) (PriceK + 544) priceCode
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a1) **
      (.x6 ↦ᵣ (a1 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a1 excess)) **
      (.x28 ↦ᵣ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a2) **
        (.x6 ↦ᵣ (a2 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a2 excess)) **
        (.x28 ↦ᵣ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))) := by
  have hldA2 := ld_spec_gen_within .x5 .x19 (AB) a1 a2 (16 : BitVec 12) (PriceK + 516) (by decide)
  have hmul2 := mul_spec_gen_within .x6 .x5 .x8 (a1 * excess) a2 excess (PriceK + 520) (by decide)
  have hmhu2 := mulhu_spec_gen_within .x7 .x5 .x8 (rv64_mulhu a1 excess) a2 excess (PriceK + 524) (by decide)
  have had12 := add_spec_gen_within .x28 .x6 .x31 (a2 * excess) ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (PriceK + 528) (by decide)
  have hsl12 := sltu_spec_gen_within .x29 .x28 .x6 (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) (PriceK + 532) (by decide)
  have had22 := add_spec_gen_within .x30 .x7 .x29 (rv64_mulhu a2 excess) (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0) ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (PriceK + 536) (by decide)
  have hsl22 := sltu_spec_gen_within .x29 .x30 .x7 (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0) ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) (PriceK + 540) (by decide)
  runBlock hldA2 hmul2 hmhu2 had12 hsl12 had22 hsl22

private theorem mul6P_pre3 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 7 (PriceK + 556) (PriceK + 584) priceCode
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a2) **
      (.x6 ↦ᵣ (a2 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a2 excess)) **
      (.x28 ↦ᵣ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a3) **
        (.x6 ↦ᵣ (a3 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a3 excess)) **
        (.x28 ↦ᵣ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))) := by
  have hldA3 := ld_spec_gen_within .x5 .x19 (AB) a2 a3 (24 : BitVec 12) (PriceK + 556) (by decide)
  have hmul3 := mul_spec_gen_within .x6 .x5 .x8 (a2 * excess) a3 excess (PriceK + 560) (by decide)
  have hmhu3 := mulhu_spec_gen_within .x7 .x5 .x8 (rv64_mulhu a2 excess) a3 excess (PriceK + 564) (by decide)
  have had13 := add_spec_gen_within .x28 .x6 .x31 (a3 * excess) ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (PriceK + 568) (by decide)
  have hsl13 := sltu_spec_gen_within .x29 .x28 .x6 (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) (PriceK + 572) (by decide)
  have had23 := add_spec_gen_within .x30 .x7 .x29 (rv64_mulhu a3 excess) (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0) ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (PriceK + 576) (by decide)
  have hsl23 := sltu_spec_gen_within .x29 .x30 .x7 (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0) ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) (PriceK + 580) (by decide)
  runBlock hldA3 hmul3 hmhu3 had13 hsl13 had23 hsl23

private theorem mul6P_pre4 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 7 (PriceK + 596) (PriceK + 624) priceCode
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a3) **
      (.x6 ↦ᵣ (a3 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a3 excess)) **
      (.x28 ↦ᵣ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a4) **
        (.x6 ↦ᵣ (a4 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a4 excess)) **
        (.x28 ↦ᵣ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))) := by
  have hldA4 := ld_spec_gen_within .x5 .x19 (AB) a3 a4 (32 : BitVec 12) (PriceK + 596) (by decide)
  have hmul4 := mul_spec_gen_within .x6 .x5 .x8 (a3 * excess) a4 excess (PriceK + 600) (by decide)
  have hmhu4 := mulhu_spec_gen_within .x7 .x5 .x8 (rv64_mulhu a3 excess) a4 excess (PriceK + 604) (by decide)
  have had14 := add_spec_gen_within .x28 .x6 .x31 (a4 * excess) ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (PriceK + 608) (by decide)
  have hsl14 := sltu_spec_gen_within .x29 .x28 .x6 (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) (PriceK + 612) (by decide)
  have had24 := add_spec_gen_within .x30 .x7 .x29 (rv64_mulhu a4 excess) (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0) ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (PriceK + 616) (by decide)
  have hsl24 := sltu_spec_gen_within .x29 .x30 .x7 (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0) ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) (PriceK + 620) (by decide)
  runBlock hldA4 hmul4 hmhu4 had14 hsl14 had24 hsl24

private theorem mul6P_pre5 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 7 (PriceK + 636) (PriceK + 664) priceCode
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a4) **
      (.x6 ↦ᵣ (a4 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a4 excess)) **
      (.x28 ↦ᵣ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
        (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
        (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))) := by
  have hldA5 := ld_spec_gen_within .x5 .x19 (AB) a4 a5 (40 : BitVec 12) (PriceK + 636) (by decide)
  have hmul5 := mul_spec_gen_within .x6 .x5 .x8 (a4 * excess) a5 excess (PriceK + 640) (by decide)
  have hmhu5 := mulhu_spec_gen_within .x7 .x5 .x8 (rv64_mulhu a4 excess) a5 excess (PriceK + 644) (by decide)
  have had15 := add_spec_gen_within .x28 .x6 .x31 (a5 * excess) ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (PriceK + 648) (by decide)
  have hsl15 := sltu_spec_gen_within .x29 .x28 .x6 (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) (PriceK + 652) (by decide)
  have had25 := add_spec_gen_within .x30 .x7 .x29 (rv64_mulhu a5 excess) (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0) ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (PriceK + 656) (by decide)
  have hsl25 := sltu_spec_gen_within .x29 .x30 .x7 (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0) ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) (PriceK + 660) (by decide)
  runBlock hldA5 hmul5 hmhu5 had15 hsl15 had25 hsl25

private theorem mul6P_tail0_core (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 468) (PriceK + 476) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a0) **
        (.x6 ↦ᵣ (a0 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a0 excess)) **
        (.x28 ↦ᵣ ((a0 * excess) + (0 : Word))) ** (.x30 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ p0) ** (((PB) + signExtend12 8) ↦ₘ p1) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a0) **
      (.x6 ↦ᵣ (a0 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a0 excess)) **
      (.x28 ↦ᵣ ((a0 * excess) + (0 : Word))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ p1) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  have hsd0 := sd_spec_gen_within .x20 .x28 (PB) ((a0 * excess) + (0 : Word)) p0 (0 : BitVec 12) (PriceK + 468)
  have hmv0 := mv_spec_gen_within .x31 .x30 ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (0 : Word) (PriceK + 472) (by decide)
  runBlock hsd0 hmv0

private theorem mul6P_tail0 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 468) (PriceK + 476) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0) = (0 : Word)⌝) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a0) **
        (.x6 ↦ᵣ (a0 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a0 excess)) **
        (.x28 ↦ᵣ ((a0 * excess) + (0 : Word))) ** (.x30 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ p0) ** (((PB) + signExtend12 8) ↦ₘ p1) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a0) **
      (.x6 ↦ᵣ (a0 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a0 excess)) **
      (.x28 ↦ᵣ ((a0 * excess) + (0 : Word))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ p1) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  refine cpsTripleWithin_weaken (pure_drop_mid) (fun _ hx => hx)
    (mul6P_tail0_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5)

private theorem mul6P_tail1_core (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 508) (PriceK + 516) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a1) **
        (.x6 ↦ᵣ (a1 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a1 excess)) **
        (.x28 ↦ᵣ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ p1) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a1) **
      (.x6 ↦ᵣ (a1 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a1 excess)) **
      (.x28 ↦ᵣ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  have hsd1 := sd_spec_gen_within .x20 .x28 (PB) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) p1 (8 : BitVec 12) (PriceK + 508)
  have hmv1 := mv_spec_gen_within .x31 .x30 ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (PriceK + 512) (by decide)
  runBlock hsd1 hmv1

private theorem mul6P_tail1 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 508) (PriceK + 516) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0) = (0 : Word)⌝) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a1) **
        (.x6 ↦ᵣ (a1 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a1 excess)) **
        (.x28 ↦ᵣ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ p1) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a1) **
      (.x6 ↦ᵣ (a1 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a1 excess)) **
      (.x28 ↦ᵣ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  refine cpsTripleWithin_weaken (pure_drop_mid) (fun _ hx => hx)
    (mul6P_tail1_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5)

private theorem mul6P_tail2_core (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 548) (PriceK + 556) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a2) **
        (.x6 ↦ᵣ (a2 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a2 excess)) **
        (.x28 ↦ᵣ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a2) **
      (.x6 ↦ᵣ (a2 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a2 excess)) **
      (.x28 ↦ᵣ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  have hsd2 := sd_spec_gen_within .x20 .x28 (PB) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) p2 (16 : BitVec 12) (PriceK + 548)
  have hmv2 := mv_spec_gen_within .x31 .x30 ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (PriceK + 552) (by decide)
  runBlock hsd2 hmv2

private theorem mul6P_tail2 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 548) (PriceK + 556) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0) = (0 : Word)⌝) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a2) **
        (.x6 ↦ᵣ (a2 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a2 excess)) **
        (.x28 ↦ᵣ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a2) **
      (.x6 ↦ᵣ (a2 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a2 excess)) **
      (.x28 ↦ᵣ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  refine cpsTripleWithin_weaken (pure_drop_mid) (fun _ hx => hx)
    (mul6P_tail2_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5)

private theorem mul6P_tail3_core (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 588) (PriceK + 596) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a3) **
        (.x6 ↦ᵣ (a3 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a3 excess)) **
        (.x28 ↦ᵣ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a3) **
      (.x6 ↦ᵣ (a3 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a3 excess)) **
      (.x28 ↦ᵣ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  have hsd3 := sd_spec_gen_within .x20 .x28 (PB) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) p3 (24 : BitVec 12) (PriceK + 588)
  have hmv3 := mv_spec_gen_within .x31 .x30 ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (PriceK + 592) (by decide)
  runBlock hsd3 hmv3

private theorem mul6P_tail3 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 588) (PriceK + 596) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0) = (0 : Word)⌝) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a3) **
        (.x6 ↦ᵣ (a3 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a3 excess)) **
        (.x28 ↦ᵣ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ p3) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a3) **
      (.x6 ↦ᵣ (a3 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a3 excess)) **
      (.x28 ↦ᵣ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  refine cpsTripleWithin_weaken (pure_drop_mid) (fun _ hx => hx)
    (mul6P_tail3_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5)

private theorem mul6P_tail4_core (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 628) (PriceK + 636) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a4) **
        (.x6 ↦ᵣ (a4 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a4 excess)) **
        (.x28 ↦ᵣ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a4) **
      (.x6 ↦ᵣ (a4 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a4 excess)) **
      (.x28 ↦ᵣ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  have hsd4 := sd_spec_gen_within .x20 .x28 (PB) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) p4 (32 : BitVec 12) (PriceK + 628)
  have hmv4 := mv_spec_gen_within .x31 .x30 ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (PriceK + 632) (by decide)
  runBlock hsd4 hmv4

private theorem mul6P_tail4 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 628) (PriceK + 636) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0) = (0 : Word)⌝) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a4) **
        (.x6 ↦ᵣ (a4 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a4 excess)) **
        (.x28 ↦ᵣ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a4) **
      (.x6 ↦ᵣ (a4 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a4 excess)) **
      (.x28 ↦ᵣ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) ** (.x31 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)) := by
  refine cpsTripleWithin_weaken (pure_drop_mid) (fun _ hx => hx)
    (mul6P_tail4_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5)

private theorem mul6P_tail5_core (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 668) (PriceK + 676) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
        (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
        (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (((.x31 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
        (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
        (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) **
        (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))) := by
  have hsd5 := sd_spec_gen_within .x20 .x28 (PB) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) p5 (40 : BitVec 12) (PriceK + 668)
  have hmv5 := mv_spec_gen_within .x31 .x30 ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (PriceK + 672) (by decide)
  runBlock hsd5 hmv5

private theorem mul6P_tail5 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 2 (PriceK + 668) (PriceK + 676) priceCode
      (      (((.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0) = (0 : Word)⌝) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
        (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
        (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) **
        (.x31 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5)))
      (      (((.x31 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
        (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
        (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) **
        (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
        (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
        (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))) := by
  refine cpsTripleWithin_weaken (pure_drop_mid) (fun _ hx => hx)
    (mul6P_tail5_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5)

theorem mul6P_core (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word) :
    cpsNBranchWithin 62 (PriceK + 432) priceCode (mul6PPRE newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31)
    [(PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5),
    (PriceK + 680, mul6PQFALL newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5)] := by
  -- limb 0
  have hpre0 := mul6P_pre0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31
  have hleaf0 := bne_spec_gen_within .x29 .x0 (500 : BitVec 13) (if BitVec.ult ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)) (rv64_mulhu a0 excess) then 1 else 0) (0 : Word) (PriceK + 464)
  rw [show (PriceK + 464 : Word) + signExtend13 (500 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (500 : BitVec 13) = (500 : Word) from by decide]; decide,
    show (PriceK + 464 : Word) + 4 = PriceK + 468 from by decide] at hleaf0
  have hins0 : amsterdamBlobGasPriceU256_prog[116]'(by decide) =
      .BNE .x29 .x0 (500 : BitVec 13) := by decide
  have hbr0 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 464) amsterdamBlobGasPriceU256_prog 116
      (.BNE .x29 .x0 (500 : BitVec 13)) (by decide) (by decide) hins0 (by decide))
    (cpsBranchWithin_frameR
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a0) **
      (.x6 ↦ᵣ (a0 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a0 excess)) **
      (.x28 ↦ᵣ ((a0 * excess) + (0 : Word))) ** (.x30 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) **
      (.x31 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ p0) ** (((PB) + signExtend12 8) ↦ₘ p1) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (by pcFree) hleaf0)
  have htail0 := mul6P_tail0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
  have hlimb0 := cpsBranchWithin_seq_cpsTripleWithin_same_cr hbr0 htail0 (fun _ hx => hx)
  have hseq0 := cpsTripleWithin_seq_cpsBranchWithin_same_cr hpre0 hlimb0
  -- limb 1
  have hpre1 := mul6P_pre1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
  have hleaf1 := bne_spec_gen_within .x29 .x0 (460 : BitVec 13) (if BitVec.ult ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)) (rv64_mulhu a1 excess) then 1 else 0) (0 : Word) (PriceK + 504)
  rw [show (PriceK + 504 : Word) + signExtend13 (460 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (460 : BitVec 13) = (460 : Word) from by decide]; decide,
    show (PriceK + 504 : Word) + 4 = PriceK + 508 from by decide] at hleaf1
  have hins1 : amsterdamBlobGasPriceU256_prog[126]'(by decide) =
      .BNE .x29 .x0 (460 : BitVec 13) := by decide
  have hbr1 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 504) amsterdamBlobGasPriceU256_prog 126
      (.BNE .x29 .x0 (460 : BitVec 13)) (by decide) (by decide) hins1 (by decide))
    (cpsBranchWithin_frameR
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a1) **
      (.x6 ↦ᵣ (a1 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a1 excess)) **
      (.x28 ↦ᵣ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) **
      (.x31 ↦ᵣ ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ p1) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (by pcFree) hleaf1)
  have htail1 := mul6P_tail1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
  have hlimb1 := cpsBranchWithin_seq_cpsTripleWithin_same_cr hbr1 htail1 (fun _ hx => hx)
  have hseq1 := cpsTripleWithin_seq_cpsBranchWithin_same_cr hpre1 hlimb1
  -- limb 2
  have hpre2 := mul6P_pre2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
  have hleaf2 := bne_spec_gen_within .x29 .x0 (420 : BitVec 13) (if BitVec.ult ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)) (rv64_mulhu a2 excess) then 1 else 0) (0 : Word) (PriceK + 544)
  rw [show (PriceK + 544 : Word) + signExtend13 (420 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (420 : BitVec 13) = (420 : Word) from by decide]; decide,
    show (PriceK + 544 : Word) + 4 = PriceK + 548 from by decide] at hleaf2
  have hins2 : amsterdamBlobGasPriceU256_prog[136]'(by decide) =
      .BNE .x29 .x0 (420 : BitVec 13) := by decide
  have hbr2 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 544) amsterdamBlobGasPriceU256_prog 136
      (.BNE .x29 .x0 (420 : BitVec 13)) (by decide) (by decide) hins2 (by decide))
    (cpsBranchWithin_frameR
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a2) **
      (.x6 ↦ᵣ (a2 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a2 excess)) **
      (.x28 ↦ᵣ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) **
      (.x31 ↦ᵣ ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ p2) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (by pcFree) hleaf2)
  have htail2 := mul6P_tail2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
  have hlimb2 := cpsBranchWithin_seq_cpsTripleWithin_same_cr hbr2 htail2 (fun _ hx => hx)
  have hseq2 := cpsTripleWithin_seq_cpsBranchWithin_same_cr hpre2 hlimb2
  -- limb 3
  have hpre3 := mul6P_pre3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5
  have hleaf3 := bne_spec_gen_within .x29 .x0 (380 : BitVec 13) (if BitVec.ult ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)) (rv64_mulhu a3 excess) then 1 else 0) (0 : Word) (PriceK + 584)
  rw [show (PriceK + 584 : Word) + signExtend13 (380 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (380 : BitVec 13) = (380 : Word) from by decide]; decide,
    show (PriceK + 584 : Word) + 4 = PriceK + 588 from by decide] at hleaf3
  have hins3 : amsterdamBlobGasPriceU256_prog[146]'(by decide) =
      .BNE .x29 .x0 (380 : BitVec 13) := by decide
  have hbr3 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 584) amsterdamBlobGasPriceU256_prog 146
      (.BNE .x29 .x0 (380 : BitVec 13)) (by decide) (by decide) hins3 (by decide))
    (cpsBranchWithin_frameR
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a3) **
      (.x6 ↦ᵣ (a3 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a3 excess)) **
      (.x28 ↦ᵣ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) **
      (.x31 ↦ᵣ ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ p3) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (by pcFree) hleaf3)
  have htail3 := mul6P_tail3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5
  have hlimb3 := cpsBranchWithin_seq_cpsTripleWithin_same_cr hbr3 htail3 (fun _ hx => hx)
  have hseq3 := cpsTripleWithin_seq_cpsBranchWithin_same_cr hpre3 hlimb3
  -- limb 4
  have hpre4 := mul6P_pre4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5
  have hleaf4 := bne_spec_gen_within .x29 .x0 (340 : BitVec 13) (if BitVec.ult ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)) (rv64_mulhu a4 excess) then 1 else 0) (0 : Word) (PriceK + 624)
  rw [show (PriceK + 624 : Word) + signExtend13 (340 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (340 : BitVec 13) = (340 : Word) from by decide]; decide,
    show (PriceK + 624 : Word) + 4 = PriceK + 628 from by decide] at hleaf4
  have hins4 : amsterdamBlobGasPriceU256_prog[156]'(by decide) =
      .BNE .x29 .x0 (340 : BitVec 13) := by decide
  have hbr4 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 624) amsterdamBlobGasPriceU256_prog 156
      (.BNE .x29 .x0 (340 : BitVec 13)) (by decide) (by decide) hins4 (by decide))
    (cpsBranchWithin_frameR
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a4) **
      (.x6 ↦ᵣ (a4 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a4 excess)) **
      (.x28 ↦ᵣ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) **
      (.x31 ↦ᵣ ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ p4) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (by pcFree) hleaf4)
  have htail4 := mul6P_tail4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5
  have hlimb4 := cpsBranchWithin_seq_cpsTripleWithin_same_cr hbr4 htail4 (fun _ hx => hx)
  have hseq4 := cpsTripleWithin_seq_cpsBranchWithin_same_cr hpre4 hlimb4
  -- limb 5
  have hpre5 := mul6P_pre5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5
  have hleaf5 := bne_spec_gen_within .x29 .x0 (300 : BitVec 13) (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0) (0 : Word) (PriceK + 664)
  rw [show (PriceK + 664 : Word) + signExtend13 (300 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (300 : BitVec 13) = (300 : Word) from by decide]; decide,
    show (PriceK + 664 : Word) + 4 = PriceK + 668 from by decide] at hleaf5
  have hins5 : amsterdamBlobGasPriceU256_prog[166]'(by decide) =
      .BNE .x29 .x0 (300 : BitVec 13) := by decide
  have hbr5 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 664) amsterdamBlobGasPriceU256_prog 166
      (.BNE .x29 .x0 (300 : BitVec 13)) (by decide) (by decide) hins5 (by decide))
    (cpsBranchWithin_frameR
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
      (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
      (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) **
      (.x31 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (by pcFree) hleaf5)
  have htail5 := mul6P_tail5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5
  have hlimb5 := cpsBranchWithin_seq_cpsTripleWithin_same_cr hbr5 htail5 (fun _ hx => hx)
  have hseq5 := cpsTripleWithin_seq_cpsBranchWithin_same_cr hpre5 hlimb5
  have hleafF := bne_spec_gen_within .x31 .x0 (288 : BitVec 13) ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (0 : Word) (PriceK + 676)
  rw [show (PriceK + 676 : Word) + signExtend13 (288 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (288 : BitVec 13) = (288 : Word) from by decide]; decide,
    show (PriceK + 676 : Word) + 4 = PriceK + 680 from by decide] at hleafF
  have hinsF : amsterdamBlobGasPriceU256_prog[169]'(by decide) =
      .BNE .x31 .x0 (288 : BitVec 13) := by decide
  have hfin := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 676) amsterdamBlobGasPriceU256_prog 169
      (.BNE .x31 .x0 (288 : BitVec 13)) (by decide) (by decide) hinsF (by decide))
    (cpsBranchWithin_frameR
      (      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
      (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
      (.x22 ↦ᵣ (newSp + signExtend12 160)) ** (.x5 ↦ᵣ a5) **
      (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
      (.x28 ↦ᵣ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0)) (rv64_mulhu a5 excess) then 1 else 0)) **
      (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0))) (a5 * excess) then 1 else 0))) ** frameSlotsSaved priceFrame newSp vals **
      (((AB) + signExtend12 0) ↦ₘ a0) ** (((AB) + signExtend12 8) ↦ₘ a1) **
      (((AB) + signExtend12 16) ↦ₘ a2) ** (((AB) + signExtend12 24) ↦ₘ a3) **
      (((AB) + signExtend12 32) ↦ₘ a4) ** (((AB) + signExtend12 40) ↦ₘ a5) **
      (((PB) + signExtend12 0) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 8) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 16) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0)))) ** (((PB) + signExtend12 24) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0)))) **
      (((PB) + signExtend12 32) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0)))) ** (((PB) + signExtend12 40) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then 1 else 0))) (a1 * excess) then 1 else 0))) (a2 * excess) then 1 else 0))) (a3 * excess) then 1 else 0))) (a4 * excess) then 1 else 0)))) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) ** (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) ** (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) ** (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5))
      (by pcFree) hleafF)
  have hL0 := cpsTripleWithin_seq_cpsBranchWithin_same_cr hpre0 hlimb0
  have hrest5 := cpsTripleWithin_seq_cpsNBranchWithin_same_cr htail5
    (cpsBranchWithin_as_cpsNBranchWithin hfin)
  have hbr5N := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hbr5 hrest5
  have h5 := cpsTripleWithin_seq_cpsNBranchWithin_same_cr hpre5 hbr5N
  have h4 := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hseq4 h5
  have h3 := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hseq3 h4
  have h2 := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hseq2 h3
  have h1 := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hseq1 h2
  exact cpsBranchWithin_cons_cpsNBranchWithin_same_cr hL0 h1

#print axioms mul6P_core
