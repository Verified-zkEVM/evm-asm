/-
Parametric windows for the outer-loop assembly (#12851): or-chain, add6, and
the swapDiv prologue/Q-posts, with the acc/prod buffer bases as parameters
`AB`/`PB` so each theorem instantiates at both buffer orientations (the loop
swaps x19/x20 every iteration). Mechanical copies with renaming + base
substitution; statements otherwise identical to the originals.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody3Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody3Spec

set_option maxRecDepth 8000

theorem loop_test_or_chainP (newSp excess outPtr iVal v6 AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 13 (PriceK + 144) (PriceK + 196) priceCode
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        frameSlotsSaved priceFrame newSp vals **
        (regOwn .x5 ** (.x6 ↦ᵣ v6) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31) **
        (((AB) + signExtend12 0) ↦ₘ a0) **
        (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) **
        (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) **
        (((AB) + signExtend12 40) ↦ₘ a5) **
        ((PB) ↦ₘ p0) ** ((newSp + signExtend12 120) ↦ₘ p1) **
        ((newSp + signExtend12 128) ↦ₘ p2) ** ((newSp + signExtend12 136) ↦ₘ p3) **
        ((newSp + signExtend12 144) ↦ₘ p4) ** ((newSp + signExtend12 152) ↦ₘ p5) **
        ((newSp + signExtend12 160) ↦ₘ s0) ** ((newSp + signExtend12 168) ↦ₘ s1) **
        ((newSp + signExtend12 176) ↦ₘ s2) ** ((newSp + signExtend12 184) ↦ₘ s3) **
        ((newSp + signExtend12 192) ↦ₘ s4) ** ((newSp + signExtend12 200) ↦ₘ s5))
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        frameSlotsSaved priceFrame newSp vals **
        ((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) **
          (.x6 ↦ᵣ a5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31) **
        (((AB) + signExtend12 0) ↦ₘ a0) **
        (((AB) + signExtend12 8) ↦ₘ a1) **
        (((AB) + signExtend12 16) ↦ₘ a2) **
        (((AB) + signExtend12 24) ↦ₘ a3) **
        (((AB) + signExtend12 32) ↦ₘ a4) **
        (((AB) + signExtend12 40) ↦ₘ a5) **
        ((PB) ↦ₘ p0) ** ((newSp + signExtend12 120) ↦ₘ p1) **
        ((newSp + signExtend12 128) ↦ₘ p2) ** ((newSp + signExtend12 136) ↦ₘ p3) **
        ((newSp + signExtend12 144) ↦ₘ p4) ** ((newSp + signExtend12 152) ↦ₘ p5) **
        ((newSp + signExtend12 160) ↦ₘ s0) ** ((newSp + signExtend12 168) ↦ₘ s1) **
        ((newSp + signExtend12 176) ↦ₘ s2) ** ((newSp + signExtend12 184) ↦ₘ s3) **
        ((newSp + signExtend12 192) ↦ₘ s4) ** ((newSp + signExtend12 200) ↦ₘ s5)) := by
  have hli := li_spec_gen_own_within .x5 (0 : Word) (PriceK + 144) (by decide)
  have hld1 := ld_spec_gen_within .x6 .x19 (AB) v6 a0
    (0 : BitVec 12) (PriceK + 148) (by decide)
  have hor1 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (0 : Word) a0 (PriceK + 152) (by decide)
  have hld2 := ld_spec_gen_within .x6 .x19 (AB) a0 a1
    (8 : BitVec 12) (PriceK + 156) (by decide)
  have hor2 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((0 : Word) ||| a0) a1
    (PriceK + 160) (by decide)
  have hld3 := ld_spec_gen_within .x6 .x19 (AB) a1 a2
    (16 : BitVec 12) (PriceK + 164) (by decide)
  have hor3 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (((0 : Word) ||| a0) ||| a1) a2
    (PriceK + 168) (by decide)
  have hld4 := ld_spec_gen_within .x6 .x19 (AB) a2 a3
    (24 : BitVec 12) (PriceK + 172) (by decide)
  have hor4 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((((0 : Word) ||| a0) ||| a1) ||| a2) a3
    (PriceK + 176) (by decide)
  have hld5 := ld_spec_gen_within .x6 .x19 (AB) a3 a4
    (32 : BitVec 12) (PriceK + 180) (by decide)
  have hor5 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) a4
    (PriceK + 184) (by decide)
  have hld6 := ld_spec_gen_within .x6 .x19 (AB) a4 a5
    (40 : BitVec 12) (PriceK + 188) (by decide)
  have hor6 := or_spec_gen_rd_eq_rs1_within .x5 .x6
    ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) a5 (PriceK + 192) (by decide)
  runBlock hli hld1 hor1 hld2 hor2 hld3 hor3 hld4 hor4 hld5 hor5 hld6 hor6

/-! ## Loop-head dispatch branches -/

/-- `beqz t0` at `PriceK+196`: acc == 0 → exit tail at `PriceK+804`. -/
theorem loop_test_beqz_branch (w : Word) :
    cpsBranchWithin 1 (PriceK + 196) priceCode ((.x5 ↦ᵣ w) ** (.x0 ↦ᵣ (0 : Word)))
      (PriceK + 804) ((.x5 ↦ᵣ w) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜w = (0 : Word)⌝)
      (PriceK + 200) ((.x5 ↦ᵣ w) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜w ≠ (0 : Word)⌝) := by
  have hleaf := beq_spec_gen_within .x5 .x0 (608 : BitVec 13) w (0 : Word) (PriceK + 196)
  rw [show (PriceK + 196 : Word) + signExtend13 (608 : BitVec 13) = PriceK + 804 from by
      rw [show signExtend13 (608 : BitVec 13) = (608 : Word) from by decide]; decide,
    show (PriceK + 196 : Word) + 4 = PriceK + 200 from by decide] at hleaf
  have hins : amsterdamBlobGasPriceU256_prog[49]'(by decide) =
      .BEQ .x5 .x0 (608 : BitVec 13) := by decide
  exact cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 196) amsterdamBlobGasPriceU256_prog 49
      (.BEQ .x5 .x0 (608 : BitVec 13)) (by decide) (by decide) hins (by decide)) hleaf

/-- `bgeu s2,t0` at `PriceK+204` (after `li t0,496`): i >= 496 → overflow tail at
`PriceK+964`; fall-through into the add6 window at `PriceK+208`. -/
theorem loop_test_bgeu_branch (iVal v5 : Word) :
    cpsBranchWithin 1 (PriceK + 204) priceCode ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ v5))
      (PriceK + 964) ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ v5) ** ⌜¬BitVec.ult iVal v5⌝)
      (PriceK + 208) ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ v5) ** ⌜BitVec.ult iVal v5⌝) := by
  have hleaf := bgeu_spec_gen_within .x18 .x5 (760 : BitVec 13) iVal v5 (PriceK + 204)
  rw [show (PriceK + 204 : Word) + signExtend13 (760 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (760 : BitVec 13) = (760 : Word) from by decide]; decide,
    show (PriceK + 204 : Word) + 4 = PriceK + 208 from by decide] at hleaf
  have hins : amsterdamBlobGasPriceU256_prog[51]'(by decide) =
      .BGEU .x18 .x5 (760 : BitVec 13) := by decide
  exact cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 204) amsterdamBlobGasPriceU256_prog 51
      (.BGEU .x18 .x5 (760 : BitVec 13)) (by decide) (by decide) hins (by decide)) hleaf

/-! ## add6 window (instrs 52..107): 6-limb ripple-carry `sum += acc` with carry-out branch. -/

/-- Add-with-carry parts: `rAdc x y c` is the limb sum, `rCry x y c` the carry-out bit. -/
@[reducible] def rAdc (x y c : Word) : Word := (x + y) + c

@[reducible] def rCry (x y c : Word) : Word :=
  (if BitVec.ult (x + y) x then (1 : Word) else (0 : Word)) |||
    (if BitVec.ult ((x + y) + c) (x + y) then (1 : Word) else (0 : Word))

theorem add6P_core (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) :
    cpsTripleWithin 55 (PriceK + 208) (PriceK + 428) priceCode
      (        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ s5))
      (        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        (.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) ** (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
        (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) **
        (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
        (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) **
        (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
        (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) **
        (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))) := by
  have hli := li_spec_gen_within .x5 v5 (0 : Word) (PriceK + 208) (by decide)
  have hldA0 := ld_spec_gen_within .x6 .x19 (AB) v6 a0 (0 : BitVec 12) (PriceK + 212) (by decide)
  have hldB0 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) v7 s0 (0 : BitVec 12) (PriceK + 216) (by decide)
  have hadd0 := add_spec_gen_within .x28 .x6 .x7 a0 s0 v28 (PriceK + 220) (by decide)
  have hsl10 := sltu_spec_gen_within .x29 .x28 .x6 v29 (a0 + s0) a0 (PriceK + 224) (by decide)
  have hadd20 := add_spec_gen_within .x30 .x28 .x5 (a0 + s0) (0 : Word) v30 (PriceK + 228) (by decide)
  have hsl20 := sltu_spec_gen_within .x31 .x30 .x28 v31 ((a0 + s0) + (0 : Word)) (a0 + s0) (PriceK + 232) (by decide)
  have hor0 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a0 + s0) a0 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a0 + s0) + (0 : Word)) (a0 + s0) then (1 : Word) else (0 : Word)) (PriceK + 236) (by decide)
  have hsd0 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a0 + s0) + (0 : Word)) s0 (0 : BitVec 12) (PriceK + 240)
  have hmv0 := mv_spec_gen_within .x5 .x29 (rCry a0 s0 (0 : Word)) (0 : Word) (PriceK + 244) (by decide)
  have hldA1 := ld_spec_gen_within .x6 .x19 (AB) a0 a1 (8 : BitVec 12) (PriceK + 248) (by decide)
  have hldB1 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s0 s1 (8 : BitVec 12) (PriceK + 252) (by decide)
  have hadd1 := add_spec_gen_within .x28 .x6 .x7 a1 s1 (a0 + s0) (PriceK + 256) (by decide)
  have hsl11 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a0 s0 (0 : Word)) (a1 + s1) a1 (PriceK + 260) (by decide)
  have hadd21 := add_spec_gen_within .x30 .x28 .x5 (a1 + s1) (rCry a0 s0 (0 : Word)) ((a0 + s0) + (0 : Word)) (PriceK + 264) (by decide)
  have hsl21 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a0 + s0) + (0 : Word)) (a0 + s0) then (1 : Word) else (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) (a1 + s1) (PriceK + 268) (by decide)
  have hor1 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a1 + s1) a1 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a1 + s1) + (rCry a0 s0 (0 : Word))) (a1 + s1) then (1 : Word) else (0 : Word)) (PriceK + 272) (by decide)
  have hsd1 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a1 + s1) + (rCry a0 s0 (0 : Word))) s1 (8 : BitVec 12) (PriceK + 276)
  have hmv1 := mv_spec_gen_within .x5 .x29 (rCry a1 s1 (rCry a0 s0 (0 : Word))) (rCry a0 s0 (0 : Word)) (PriceK + 280) (by decide)
  have hldA2 := ld_spec_gen_within .x6 .x19 (AB) a1 a2 (16 : BitVec 12) (PriceK + 284) (by decide)
  have hldB2 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s1 s2 (16 : BitVec 12) (PriceK + 288) (by decide)
  have hadd2 := add_spec_gen_within .x28 .x6 .x7 a2 s2 (a1 + s1) (PriceK + 292) (by decide)
  have hsl12 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a1 s1 (rCry a0 s0 (0 : Word))) (a2 + s2) a2 (PriceK + 296) (by decide)
  have hadd22 := add_spec_gen_within .x30 .x28 .x5 (a2 + s2) (rCry a1 s1 (rCry a0 s0 (0 : Word))) ((a1 + s1) + (rCry a0 s0 (0 : Word))) (PriceK + 300) (by decide)
  have hsl22 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a1 + s1) + (rCry a0 s0 (0 : Word))) (a1 + s1) then (1 : Word) else (0 : Word)) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (a2 + s2) (PriceK + 304) (by decide)
  have hor2 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a2 + s2) a2 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (a2 + s2) then (1 : Word) else (0 : Word)) (PriceK + 308) (by decide)
  have hsd2 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) s2 (16 : BitVec 12) (PriceK + 312)
  have hmv2 := mv_spec_gen_within .x5 .x29 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (rCry a1 s1 (rCry a0 s0 (0 : Word))) (PriceK + 316) (by decide)
  have hldA3 := ld_spec_gen_within .x6 .x19 (AB) a2 a3 (24 : BitVec 12) (PriceK + 320) (by decide)
  have hldB3 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s2 s3 (24 : BitVec 12) (PriceK + 324) (by decide)
  have hadd3 := add_spec_gen_within .x28 .x6 .x7 a3 s3 (a2 + s2) (PriceK + 328) (by decide)
  have hsl13 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (a3 + s3) a3 (PriceK + 332) (by decide)
  have hadd23 := add_spec_gen_within .x30 .x28 .x5 (a3 + s3) (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (PriceK + 336) (by decide)
  have hsl23 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (a2 + s2) then (1 : Word) else (0 : Word)) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (a3 + s3) (PriceK + 340) (by decide)
  have hor3 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a3 + s3) a3 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (a3 + s3) then (1 : Word) else (0 : Word)) (PriceK + 344) (by decide)
  have hsd3 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) s3 (24 : BitVec 12) (PriceK + 348)
  have hmv3 := mv_spec_gen_within .x5 .x29 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (PriceK + 352) (by decide)
  have hldA4 := ld_spec_gen_within .x6 .x19 (AB) a3 a4 (32 : BitVec 12) (PriceK + 356) (by decide)
  have hldB4 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s3 s4 (32 : BitVec 12) (PriceK + 360) (by decide)
  have hadd4 := add_spec_gen_within .x28 .x6 .x7 a4 s4 (a3 + s3) (PriceK + 364) (by decide)
  have hsl14 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (a4 + s4) a4 (PriceK + 368) (by decide)
  have hadd24 := add_spec_gen_within .x30 .x28 .x5 (a4 + s4) (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (PriceK + 372) (by decide)
  have hsl24 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (a3 + s3) then (1 : Word) else (0 : Word)) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (a4 + s4) (PriceK + 376) (by decide)
  have hor4 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a4 + s4) a4 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (a4 + s4) then (1 : Word) else (0 : Word)) (PriceK + 380) (by decide)
  have hsd4 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) s4 (32 : BitVec 12) (PriceK + 384)
  have hmv4 := mv_spec_gen_within .x5 .x29 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (PriceK + 388) (by decide)
  have hldA5 := ld_spec_gen_within .x6 .x19 (AB) a4 a5 (40 : BitVec 12) (PriceK + 392) (by decide)
  have hldB5 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s4 s5 (40 : BitVec 12) (PriceK + 396) (by decide)
  have hadd5 := add_spec_gen_within .x28 .x6 .x7 a5 s5 (a4 + s4) (PriceK + 400) (by decide)
  have hsl15 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (a5 + s5) a5 (PriceK + 404) (by decide)
  have hadd25 := add_spec_gen_within .x30 .x28 .x5 (a5 + s5) (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (PriceK + 408) (by decide)
  have hsl25 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (a4 + s4) then (1 : Word) else (0 : Word)) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) (PriceK + 412) (by decide)
  have hor5 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a5 + s5) a5 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word)) (PriceK + 416) (by decide)
  have hsd5 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) s5 (40 : BitVec 12) (PriceK + 420)
  have hmv5 := mv_spec_gen_within .x5 .x29 (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (PriceK + 424) (by decide)
  runBlock hli hldA0 hldB0 hadd0 hsl10 hadd20 hsl20 hor0 hsd0 hmv0 hldA1 hldB1 hadd1 hsl11 hadd21 hsl21 hor1 hsd1 hmv1 hldA2 hldB2 hadd2 hsl12 hadd22 hsl22 hor2 hsd2 hmv2 hldA3 hldB3 hadd3 hsl13 hadd23 hsl23 hor3 hsd3 hmv3 hldA4 hldB4 hadd4 hsl14 hadd24 hsl24 hor4 hsd4 hmv4 hldA5 hldB5 hadd5 hsl15 hadd25 hsl25 hor5 hsd5 hmv5

/-- Carry-out branch at `PriceK+428`: nonzero carry → overflow tail at `+964`. -/
theorem add6_carry_branch (c : Word) :
    cpsBranchWithin 1 (PriceK + 428) priceCode ((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      (PriceK + 964) ((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c ≠ (0 : Word)⌝)
      (PriceK + 432) ((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c = (0 : Word)⌝) := by
  have hleaf := bne_spec_gen_within .x5 .x0 (536 : BitVec 13) c (0 : Word) (PriceK + 428)
  rw [show (PriceK + 428 : Word) + signExtend13 (536 : BitVec 13) = PriceK + 964 from by
      rw [show signExtend13 (536 : BitVec 13) = (536 : Word) from by decide]; decide,
    show (PriceK + 428 : Word) + 4 = PriceK + 432 from by decide] at hleaf
  have hins : amsterdamBlobGasPriceU256_prog[107]'(by decide) =
      .BNE .x5 .x0 (536 : BitVec 13) := by decide
  exact cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 428) amsterdamBlobGasPriceU256_prog 107
      (.BNE .x5 .x0 (536 : BitVec 13)) (by decide) (by decide) hins (by decide)) hleaf

#print axioms price_setup_spec
#print axioms loop_test_or_chain_spec
#print axioms loop_test_beqz_branch
#print axioms loop_test_bgeu_branch

#print axioms add6P_core

@[reducible] def QOVFDIVP (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
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
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))

@[reducible] def QBACKP (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 _v7 _v28 _v29 _v30 _v31 : Word)
    (FR : Assertion) : Assertion :=
  ((.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **       (((.x6 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).1) ** (.x7 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (.x29 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (taylorDW * iVal))) ** (.x30 ↦ᵣ (((PB) + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) ** (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) ** (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).1 p0 (0 : Word) 64).2.2) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).2.2) ** (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).2.2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).2.2) ** (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).2.2) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (divst (taylorDW * iVal) (0 : Word) p5 (0 : Word) 64).1 p4 (0 : Word) 64).1 p3 (0 : Word) 64).1 p2 (0 : Word) 64).1 p1 (0 : Word) 64).2.2)** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
                (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)))

theorem swapdivP_p1 (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
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
        (.x19 ↦ᵣ (AB)) **
        (.x20 ↦ᵣ (PB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR)) := by
  have h1 := mv_spec_gen_within .x5 .x19 (AB) v5 (PriceK + 680) (by decide)
  have h1F : cpsTripleWithin 1 (PriceK + 680) (PriceK + 684) priceCode
      (((.x19 ↦ᵣ (AB)) ** (.x5 ↦ᵣ v5)) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (PB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))
      (((.x19 ↦ᵣ (AB)) ** (.x5 ↦ᵣ (AB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (PB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
  have h2 := mv_spec_gen_within .x19 .x20 (PB) (AB) (PriceK + 684) (by decide)
  have h2F : cpsTripleWithin 1 (PriceK + 684) (PriceK + 688) priceCode
      (((.x20 ↦ᵣ (PB)) ** (.x19 ↦ᵣ (AB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (AB)) **
        (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))
      (((.x20 ↦ᵣ (PB)) ** (.x19 ↦ᵣ (PB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (AB)) **
        (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
      (((.x19 ↦ᵣ (AB)) ** (.x5 ↦ᵣ (AB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x20 ↦ᵣ (PB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))
      (((.x20 ↦ᵣ (PB)) ** (.x19 ↦ᵣ (PB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (AB)) **
        (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
  have h3 := mv_spec_gen_within .x20 .x5 (AB) (PB) (PriceK + 688) (by decide)
  have h3F : cpsTripleWithin 1 (PriceK + 688) (PriceK + 692) priceCode
      (((.x5 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (PB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))
      (((.x5 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (AB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (PB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
      (((.x20 ↦ᵣ (PB)) ** (.x19 ↦ᵣ (PB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (AB)) **
        (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
        FR))
      (((.x5 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (AB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (PB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
  have h4 := mul_spec_gen_within .x5 .x9 .x18 (AB) taylorDW iVal (PriceK + 692)
    (by decide)
  have h4F : cpsTripleWithin 1 (PriceK + 692) (PriceK + 696) priceCode
      (((.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (AB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
      (((.x5 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (AB))) ** ((.x2 ↦ᵣ newSp) **
        (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) **
        (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (PB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
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
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
        (.x19 ↦ᵣ (PB)) **
        (.x20 ↦ᵣ (AB)) **
        (.x21 ↦ᵣ outPtr) **
        (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
        (.x5 ↦ᵣ (taylorDW * iVal)) **
        (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
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
