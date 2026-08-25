/-
Body-window contracts for `amsterdam_blob_gas_price_u256` (#12851 body discharge).

Windows proven here (instruction indices into `amsterdamBlobGasPriceU256_prog`,
which the ABI-shell PR proved equal to `abiFrameProg (-208) 208 priceFrame priceBody`):

* setup   (instrs 9..35,  `PriceK+36  → PriceK+144`): register/buffer initialisation;
* or-test (instrs 36..48, `PriceK+144 → PriceK+196`): the 6-limb acc-zero test chain
  that feeds `taylorLoopInv` into the loop-head dispatch;
* beqz    (instr 49,      `PriceK+196`): acc == 0 branch to the exit tail (`+804`);
* bgeu    (instr 51,      `PriceK+204`): i >= 496 branch to the overflow tail (`+964`).

The remaining windows (add6 / mul6 / swapDiv / exitDiv / tail) are future work; the
assembled `priceBodyContract` discharge consumes them via `TwoExitLoop`.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceAbiShell
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell

set_option maxRecDepth 8000

/-! ## Buffer cell vocabulary -/

/-- Pinned dword cells at `base + signExtend12 o`, right-nested, ending `empAssertion`. -/
private def bufCells : Word → List (BitVec 12 × Word) → Assertion
  | _, [] => empAssertion
  | base, (o, v) :: rest => ((base + signExtend12 o) ↦ₘ v) ** bufCells base rest

/-- `memOwn` cells at `base + signExtend12 o`, right-nested, ending `empAssertion`. -/
private def bufOwns : Word → List (BitVec 12) → Assertion
  | _, [] => empAssertion
  | base, o :: rest => memOwn (base + signExtend12 o) ** bufOwns base rest

private def accOffs : List (BitVec 12) := [64, 72, 80, 88, 96, 104]
private def prodOffs : List (BitVec 12) := [112, 120, 128, 136, 144, 152]
private def sumOffs : List (BitVec 12) := [160, 168, 176, 184, 192, 200]
private def bufOffs18 : List (BitVec 12) := accOffs ++ prodOffs ++ sumOffs

/-! ## The D constant as the emitted LUI+ADDIW composite -/

@[reducible] private def taylorDWHi : Word :=
  (((2853 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64

@[reducible] private def taylorDW : Word :=
  ((taylorDWHi.truncate 32 + (signExtend12 (-1217 : BitVec 12)).truncate 32 :
    BitVec 32).signExtend 64)

private theorem taylorDW_eq : taylorDW = 11684671 := by decide

/-! ## Loop invariant -/

/-- State at the loop head (`PriceK+144`) of the inlined taylor recurrence.
Buffers are pinned; `iVal` is the recurrence index; the saved-frame cells and the
caller-owned registers ride along framed. -/
private def taylorLoopInv (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (aC pC sC : List (BitVec 12 × Word)) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
  (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
  (.x19 ↦ᵣ (newSp + signExtend12 64)) ** (.x20 ↦ᵣ (newSp + signExtend12 112)) **
  (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
  frameSlotsSaved priceFrame newSp vals **
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31) **
  bufCells newSp aC ** bufCells newSp pC ** bufCells newSp sC

/-! ## Setup window (instrs 9..35) -/

/-- Entry-to-loop-head: `mv s0,a0; mv s5,a1; lui s1,0xb25; addiw s1,s1,-1217; li s2,1;
addi s3,sp,64; addi s4,sp,112; addi s6,sp,160; 18x sd zero,off(sp); sd s1,64(sp)`. -/
private theorem price_setup_core (_sp0 newSp excess outPtr : Word) (vals : Reg → Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 : Word) :
    cpsTripleWithin 27 (PriceK + 36) (PriceK + 144) priceCode
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ (vals .x8)) ** (.x9 ↦ᵣ (vals .x9)) ** (.x18 ↦ᵣ (vals .x18)) **
        (.x19 ↦ᵣ (vals .x19)) ** (.x20 ↦ᵣ (vals .x20)) ** (.x21 ↦ᵣ (vals .x21)) **
        (.x22 ↦ᵣ (vals .x22)) **
        frameSlotsSaved priceFrame newSp vals **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31) **
        ((newSp + signExtend12 64) ↦ₘ m0) ** ((newSp + signExtend12 72) ↦ₘ m1) **
        ((newSp + signExtend12 80) ↦ₘ m2) ** ((newSp + signExtend12 88) ↦ₘ m3) **
        ((newSp + signExtend12 96) ↦ₘ m4) ** ((newSp + signExtend12 104) ↦ₘ m5) **
        ((newSp + signExtend12 112) ↦ₘ m6) ** ((newSp + signExtend12 120) ↦ₘ m7) **
        ((newSp + signExtend12 128) ↦ₘ m8) ** ((newSp + signExtend12 136) ↦ₘ m9) **
        ((newSp + signExtend12 144) ↦ₘ m10) ** ((newSp + signExtend12 152) ↦ₘ m11) **
        ((newSp + signExtend12 160) ↦ₘ m12) ** ((newSp + signExtend12 168) ↦ₘ m13) **
        ((newSp + signExtend12 176) ↦ₘ m14) ** ((newSp + signExtend12 184) ↦ₘ m15) **
        ((newSp + signExtend12 192) ↦ₘ m16) ** ((newSp + signExtend12 200) ↦ₘ m17))
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ (1 : Word)) **
        (.x19 ↦ᵣ (newSp + signExtend12 64)) ** (.x20 ↦ᵣ (newSp + signExtend12 112)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        frameSlotsSaved priceFrame newSp vals **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31) **
        ((newSp + signExtend12 64) ↦ₘ taylorDW) ** ((newSp + signExtend12 72) ↦ₘ (0 : Word)) **
        ((newSp + signExtend12 80) ↦ₘ (0 : Word)) ** ((newSp + signExtend12 88) ↦ₘ (0 : Word)) **
        ((newSp + signExtend12 96) ↦ₘ (0 : Word)) ** ((newSp + signExtend12 104) ↦ₘ (0 : Word)) **
        ((newSp + signExtend12 112) ↦ₘ (0 : Word)) ** ((newSp + signExtend12 120) ↦ₘ (0 : Word)) **
        ((newSp + signExtend12 128) ↦ₘ (0 : Word)) ** ((newSp + signExtend12 136) ↦ₘ (0 : Word)) **
        ((newSp + signExtend12 144) ↦ₘ (0 : Word)) ** ((newSp + signExtend12 152) ↦ₘ (0 : Word)) **
        ((newSp + signExtend12 160) ↦ₘ (0 : Word)) ** ((newSp + signExtend12 168) ↦ₘ (0 : Word)) **
        ((newSp + signExtend12 176) ↦ₘ (0 : Word)) ** ((newSp + signExtend12 184) ↦ₘ (0 : Word)) **
        ((newSp + signExtend12 192) ↦ₘ (0 : Word)) ** ((newSp + signExtend12 200) ↦ₘ (0 : Word))) := by
  have hv1 := mv_spec_gen_within .x8 .x10 excess (vals .x8) (PriceK + 36) (by decide)
  have hv2 := mv_spec_gen_within .x21 .x11 outPtr (vals .x21) (PriceK + 40) (by decide)
  have hv3 := lui_spec_gen_within .x9 (vals .x9) (2853 : BitVec 20) (PriceK + 44) (by decide)
  have hv4 := addiw_spec_gen_same_within .x9 taylorDWHi (-1217 : BitVec 12)
    (PriceK + 48) (by decide)
  have hv5 := li_spec_gen_within .x18 (vals .x18) (1 : Word) (PriceK + 52) (by decide)
  have hv6 := addi_spec_gen_within .x19 .x2 (vals .x19) newSp (64 : BitVec 12)
    (PriceK + 56) (by decide)
  have hv7 := addi_spec_gen_within .x20 .x2 (vals .x20) newSp (112 : BitVec 12)
    (PriceK + 60) (by decide)
  have hv8 := addi_spec_gen_within .x22 .x2 (vals .x22) newSp (160 : BitVec 12)
    (PriceK + 64) (by decide)
  have hv9 := sd_x0_spec_gen_within .x2 newSp m0 (64 : BitVec 12) (PriceK + 68)
  have hv10 := sd_x0_spec_gen_within .x2 newSp m1 (72 : BitVec 12) (PriceK + 72)
  have hv11 := sd_x0_spec_gen_within .x2 newSp m2 (80 : BitVec 12) (PriceK + 76)
  have hv12 := sd_x0_spec_gen_within .x2 newSp m3 (88 : BitVec 12) (PriceK + 80)
  have hv13 := sd_x0_spec_gen_within .x2 newSp m4 (96 : BitVec 12) (PriceK + 84)
  have hv14 := sd_x0_spec_gen_within .x2 newSp m5 (104 : BitVec 12) (PriceK + 88)
  have hv15 := sd_x0_spec_gen_within .x2 newSp m6 (112 : BitVec 12) (PriceK + 92)
  have hv16 := sd_x0_spec_gen_within .x2 newSp m7 (120 : BitVec 12) (PriceK + 96)
  have hv17 := sd_x0_spec_gen_within .x2 newSp m8 (128 : BitVec 12) (PriceK + 100)
  have hv18 := sd_x0_spec_gen_within .x2 newSp m9 (136 : BitVec 12) (PriceK + 104)
  have hv19 := sd_x0_spec_gen_within .x2 newSp m10 (144 : BitVec 12) (PriceK + 108)
  have hv20 := sd_x0_spec_gen_within .x2 newSp m11 (152 : BitVec 12) (PriceK + 112)
  have hv21 := sd_x0_spec_gen_within .x2 newSp m12 (160 : BitVec 12) (PriceK + 116)
  have hv22 := sd_x0_spec_gen_within .x2 newSp m13 (168 : BitVec 12) (PriceK + 120)
  have hv23 := sd_x0_spec_gen_within .x2 newSp m14 (176 : BitVec 12) (PriceK + 124)
  have hv24 := sd_x0_spec_gen_within .x2 newSp m15 (184 : BitVec 12) (PriceK + 128)
  have hv25 := sd_x0_spec_gen_within .x2 newSp m16 (192 : BitVec 12) (PriceK + 132)
  have hv26 := sd_x0_spec_gen_within .x2 newSp m17 (200 : BitVec 12) (PriceK + 136)
  have hv27 := sd_spec_gen_within .x2 .x9 newSp taylorDW (0 : Word) (64 : BitVec 12)
    (PriceK + 140)
  runBlock hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16
    hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27
/-- Setup window restated against the shell-level `priceBodyPre` / `taylorLoopInv`
vocabularies (what the assembled body contract consumes). -/
theorem price_setup_spec (sp0 excess outPtr : Word) (vals : Reg → Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 : Word) :
    cpsTripleWithin 27 (PriceK + 36) (PriceK + 144) priceCode
      (priceBodyPre (sp0 + signExtend12 (-208 : BitVec 12)) vals excess outPtr
        (bufCells (sp0 + signExtend12 (-208 : BitVec 12))
          [(64, m0), (72, m1), (80, m2), (88, m3), (96, m4), (104, m5), (112, m6),
            (120, m7), (128, m8), (136, m9), (144, m10), (152, m11), (160, m12),
            (168, m13), (176, m14), (184, m15), (192, m16), (200, m17)]))
      (taylorLoopInv (sp0 + signExtend12 (-208 : BitVec 12)) excess outPtr
        (1 : Word) vals
        [(64, taylorDW), (72, 0), (80, 0), (88, 0), (96, 0), (104, 0)]
        [(112, (0 : Word)), (120, 0), (128, 0), (136, 0), (144, 0), (152, 0)]
        [(160, (0 : Word)), (168, 0), (176, 0), (184, 0), (192, 0), (200, 0)]) := by
  refine cpsTripleWithin_weaken (P := _) (Q := _) ?_ ?_
    (price_setup_core sp0 (sp0 + signExtend12 (-208 : BitVec 12)) excess outPtr vals
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17)
  · intro h hx
    simp only [priceBodyPre, priceFrame, regsAt, frameSlotsSaved, bufCells, regOwns,
      List.foldr_cons, List.foldr_nil, sepConj_emp_right'] at hx ⊢
    xperm_hyp hx
  · intro h hx
    simp only [taylorLoopInv, priceFrame, frameSlotsSaved, bufCells,
      List.foldr_cons, List.foldr_nil, sepConj_emp_right'] at hx ⊢
    xperm_hyp hx

/-! ## Loop-head or-chain (instrs 36..48) -/

/-- `or6` as the exact left-associated chain produced by the six `or t0,t0,t1`s. -/
private def or6 (a0 a1 a2 a3 a4 a5 : Word) : Word :=
  ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5

private theorem or6_eq_chain (a0 a1 a2 a3 a4 a5 : Word) :
    or6 a0 a1 a2 a3 a4 a5 =
      ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5 := rfl

/-- `li t0,0; 6x (ld t1,off(s3); or t0,t0,t1)`. Stated standalone-spelled: `x6` must
enter pinned (no `ld` own-variant exists); the iteration lemma instantiates `v6`.
Acc cells are leaf-exact NESTED `((newSp + se12 64) + se12 off)`; prod/sum cells flat. -/
theorem loop_test_or_chain_spec (newSp excess outPtr iVal v6 : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word) :
    cpsTripleWithin 13 (PriceK + 144) (PriceK + 196) priceCode
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 64)) ** (.x20 ↦ᵣ (newSp + signExtend12 112)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        frameSlotsSaved priceFrame newSp vals **
        (regOwn .x5 ** (.x6 ↦ᵣ v6) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31) **
        (((newSp + signExtend12 64) + signExtend12 0) ↦ₘ a0) **
        (((newSp + signExtend12 64) + signExtend12 8) ↦ₘ a1) **
        (((newSp + signExtend12 64) + signExtend12 16) ↦ₘ a2) **
        (((newSp + signExtend12 64) + signExtend12 24) ↦ₘ a3) **
        (((newSp + signExtend12 64) + signExtend12 32) ↦ₘ a4) **
        (((newSp + signExtend12 64) + signExtend12 40) ↦ₘ a5) **
        ((newSp + signExtend12 112) ↦ₘ p0) ** ((newSp + signExtend12 120) ↦ₘ p1) **
        ((newSp + signExtend12 128) ↦ₘ p2) ** ((newSp + signExtend12 136) ↦ₘ p3) **
        ((newSp + signExtend12 144) ↦ₘ p4) ** ((newSp + signExtend12 152) ↦ₘ p5) **
        ((newSp + signExtend12 160) ↦ₘ s0) ** ((newSp + signExtend12 168) ↦ₘ s1) **
        ((newSp + signExtend12 176) ↦ₘ s2) ** ((newSp + signExtend12 184) ↦ₘ s3) **
        ((newSp + signExtend12 192) ↦ₘ s4) ** ((newSp + signExtend12 200) ↦ₘ s5))
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 64)) ** (.x20 ↦ᵣ (newSp + signExtend12 112)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        frameSlotsSaved priceFrame newSp vals **
        ((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) **
          (.x6 ↦ᵣ a5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31) **
        (((newSp + signExtend12 64) + signExtend12 0) ↦ₘ a0) **
        (((newSp + signExtend12 64) + signExtend12 8) ↦ₘ a1) **
        (((newSp + signExtend12 64) + signExtend12 16) ↦ₘ a2) **
        (((newSp + signExtend12 64) + signExtend12 24) ↦ₘ a3) **
        (((newSp + signExtend12 64) + signExtend12 32) ↦ₘ a4) **
        (((newSp + signExtend12 64) + signExtend12 40) ↦ₘ a5) **
        ((newSp + signExtend12 112) ↦ₘ p0) ** ((newSp + signExtend12 120) ↦ₘ p1) **
        ((newSp + signExtend12 128) ↦ₘ p2) ** ((newSp + signExtend12 136) ↦ₘ p3) **
        ((newSp + signExtend12 144) ↦ₘ p4) ** ((newSp + signExtend12 152) ↦ₘ p5) **
        ((newSp + signExtend12 160) ↦ₘ s0) ** ((newSp + signExtend12 168) ↦ₘ s1) **
        ((newSp + signExtend12 176) ↦ₘ s2) ** ((newSp + signExtend12 184) ↦ₘ s3) **
        ((newSp + signExtend12 192) ↦ₘ s4) ** ((newSp + signExtend12 200) ↦ₘ s5)) := by
  have hli := li_spec_gen_own_within .x5 (0 : Word) (PriceK + 144) (by decide)
  have hld1 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) v6 a0
    (0 : BitVec 12) (PriceK + 148) (by decide)
  have hor1 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (0 : Word) a0 (PriceK + 152) (by decide)
  have hld2 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a0 a1
    (8 : BitVec 12) (PriceK + 156) (by decide)
  have hor2 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((0 : Word) ||| a0) a1
    (PriceK + 160) (by decide)
  have hld3 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a1 a2
    (16 : BitVec 12) (PriceK + 164) (by decide)
  have hor3 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (((0 : Word) ||| a0) ||| a1) a2
    (PriceK + 168) (by decide)
  have hld4 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a2 a3
    (24 : BitVec 12) (PriceK + 172) (by decide)
  have hor4 := or_spec_gen_rd_eq_rs1_within .x5 .x6 ((((0 : Word) ||| a0) ||| a1) ||| a2) a3
    (PriceK + 176) (by decide)
  have hld5 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a3 a4
    (32 : BitVec 12) (PriceK + 180) (by decide)
  have hor5 := or_spec_gen_rd_eq_rs1_within .x5 .x6 (((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) a4
    (PriceK + 184) (by decide)
  have hld6 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a4 a5
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
@[reducible] private def rAdc (x y c : Word) : Word := (x + y) + c

@[reducible] private def rCry (x y c : Word) : Word :=
  (if BitVec.ult (x + y) x then (1 : Word) else (0 : Word)) |||
    (if BitVec.ult ((x + y) + c) (x + y) then (1 : Word) else (0 : Word))

theorem add6_core (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) :
    cpsTripleWithin 55 (PriceK + 208) (PriceK + 428) priceCode
      (        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 64)) ** (.x20 ↦ᵣ (newSp + signExtend12 112)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 64) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 64) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 64) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 64) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 64) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 64) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 112) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 112) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 112) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 112) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 112) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 112) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
        (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ s5))
      (        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
        (.x19 ↦ᵣ (newSp + signExtend12 64)) ** (.x20 ↦ᵣ (newSp + signExtend12 112)) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        (.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) ** (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
        (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) **
        frameSlotsSaved priceFrame newSp vals **
        (((newSp + signExtend12 64) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
        (((newSp + signExtend12 64) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
        (((newSp + signExtend12 64) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
        (((newSp + signExtend12 64) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
        (((newSp + signExtend12 64) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
        (((newSp + signExtend12 64) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
        (((newSp + signExtend12 112) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        (((newSp + signExtend12 112) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        (((newSp + signExtend12 112) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        (((newSp + signExtend12 112) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
        (((newSp + signExtend12 112) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
        (((newSp + signExtend12 112) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) **
        (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
        (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) **
        (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
        (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) **
        (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))) := by
  have hli := li_spec_gen_within .x5 v5 (0 : Word) (PriceK + 208) (by decide)
  have hldA0 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) v6 a0 (0 : BitVec 12) (PriceK + 212) (by decide)
  have hldB0 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) v7 s0 (0 : BitVec 12) (PriceK + 216) (by decide)
  have hadd0 := add_spec_gen_within .x28 .x6 .x7 a0 s0 v28 (PriceK + 220) (by decide)
  have hsl10 := sltu_spec_gen_within .x29 .x28 .x6 v29 (a0 + s0) a0 (PriceK + 224) (by decide)
  have hadd20 := add_spec_gen_within .x30 .x28 .x5 (a0 + s0) (0 : Word) v30 (PriceK + 228) (by decide)
  have hsl20 := sltu_spec_gen_within .x31 .x30 .x28 v31 ((a0 + s0) + (0 : Word)) (a0 + s0) (PriceK + 232) (by decide)
  have hor0 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a0 + s0) a0 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a0 + s0) + (0 : Word)) (a0 + s0) then (1 : Word) else (0 : Word)) (PriceK + 236) (by decide)
  have hsd0 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a0 + s0) + (0 : Word)) s0 (0 : BitVec 12) (PriceK + 240)
  have hmv0 := mv_spec_gen_within .x5 .x29 (rCry a0 s0 (0 : Word)) (0 : Word) (PriceK + 244) (by decide)
  have hldA1 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a0 a1 (8 : BitVec 12) (PriceK + 248) (by decide)
  have hldB1 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s0 s1 (8 : BitVec 12) (PriceK + 252) (by decide)
  have hadd1 := add_spec_gen_within .x28 .x6 .x7 a1 s1 (a0 + s0) (PriceK + 256) (by decide)
  have hsl11 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a0 s0 (0 : Word)) (a1 + s1) a1 (PriceK + 260) (by decide)
  have hadd21 := add_spec_gen_within .x30 .x28 .x5 (a1 + s1) (rCry a0 s0 (0 : Word)) ((a0 + s0) + (0 : Word)) (PriceK + 264) (by decide)
  have hsl21 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a0 + s0) + (0 : Word)) (a0 + s0) then (1 : Word) else (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) (a1 + s1) (PriceK + 268) (by decide)
  have hor1 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a1 + s1) a1 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a1 + s1) + (rCry a0 s0 (0 : Word))) (a1 + s1) then (1 : Word) else (0 : Word)) (PriceK + 272) (by decide)
  have hsd1 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a1 + s1) + (rCry a0 s0 (0 : Word))) s1 (8 : BitVec 12) (PriceK + 276)
  have hmv1 := mv_spec_gen_within .x5 .x29 (rCry a1 s1 (rCry a0 s0 (0 : Word))) (rCry a0 s0 (0 : Word)) (PriceK + 280) (by decide)
  have hldA2 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a1 a2 (16 : BitVec 12) (PriceK + 284) (by decide)
  have hldB2 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s1 s2 (16 : BitVec 12) (PriceK + 288) (by decide)
  have hadd2 := add_spec_gen_within .x28 .x6 .x7 a2 s2 (a1 + s1) (PriceK + 292) (by decide)
  have hsl12 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a1 s1 (rCry a0 s0 (0 : Word))) (a2 + s2) a2 (PriceK + 296) (by decide)
  have hadd22 := add_spec_gen_within .x30 .x28 .x5 (a2 + s2) (rCry a1 s1 (rCry a0 s0 (0 : Word))) ((a1 + s1) + (rCry a0 s0 (0 : Word))) (PriceK + 300) (by decide)
  have hsl22 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a1 + s1) + (rCry a0 s0 (0 : Word))) (a1 + s1) then (1 : Word) else (0 : Word)) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (a2 + s2) (PriceK + 304) (by decide)
  have hor2 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a2 + s2) a2 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (a2 + s2) then (1 : Word) else (0 : Word)) (PriceK + 308) (by decide)
  have hsd2 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) s2 (16 : BitVec 12) (PriceK + 312)
  have hmv2 := mv_spec_gen_within .x5 .x29 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (rCry a1 s1 (rCry a0 s0 (0 : Word))) (PriceK + 316) (by decide)
  have hldA3 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a2 a3 (24 : BitVec 12) (PriceK + 320) (by decide)
  have hldB3 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s2 s3 (24 : BitVec 12) (PriceK + 324) (by decide)
  have hadd3 := add_spec_gen_within .x28 .x6 .x7 a3 s3 (a2 + s2) (PriceK + 328) (by decide)
  have hsl13 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (a3 + s3) a3 (PriceK + 332) (by decide)
  have hadd23 := add_spec_gen_within .x30 .x28 .x5 (a3 + s3) (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (PriceK + 336) (by decide)
  have hsl23 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (a2 + s2) then (1 : Word) else (0 : Word)) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (a3 + s3) (PriceK + 340) (by decide)
  have hor3 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a3 + s3) a3 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (a3 + s3) then (1 : Word) else (0 : Word)) (PriceK + 344) (by decide)
  have hsd3 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) s3 (24 : BitVec 12) (PriceK + 348)
  have hmv3 := mv_spec_gen_within .x5 .x29 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))) (PriceK + 352) (by decide)
  have hldA4 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a3 a4 (32 : BitVec 12) (PriceK + 356) (by decide)
  have hldB4 := ld_spec_gen_within .x7 .x22 (newSp + signExtend12 160) s3 s4 (32 : BitVec 12) (PriceK + 360) (by decide)
  have hadd4 := add_spec_gen_within .x28 .x6 .x7 a4 s4 (a3 + s3) (PriceK + 364) (by decide)
  have hsl14 := sltu_spec_gen_within .x29 .x28 .x6 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (a4 + s4) a4 (PriceK + 368) (by decide)
  have hadd24 := add_spec_gen_within .x30 .x28 .x5 (a4 + s4) (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (PriceK + 372) (by decide)
  have hsl24 := sltu_spec_gen_within .x31 .x30 .x28 (if BitVec.ult ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (a3 + s3) then (1 : Word) else (0 : Word)) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (a4 + s4) (PriceK + 376) (by decide)
  have hor4 := or_spec_gen_rd_eq_rs1_within .x29 .x31 (if BitVec.ult (a4 + s4) a4 then (1 : Word) else (0 : Word)) (if BitVec.ult ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (a4 + s4) then (1 : Word) else (0 : Word)) (PriceK + 380) (by decide)
  have hsd4 := sd_spec_gen_within .x22 .x30 (newSp + signExtend12 160) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) s4 (32 : BitVec 12) (PriceK + 384)
  have hmv4 := mv_spec_gen_within .x5 .x29 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) (PriceK + 388) (by decide)
  have hldA5 := ld_spec_gen_within .x6 .x19 (newSp + signExtend12 64) a4 a5 (40 : BitVec 12) (PriceK + 392) (by decide)
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

#print axioms add6_core
#print axioms add6_carry_branch