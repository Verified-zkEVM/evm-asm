/- Back-edge adapter for the K70 Taylor round (#12851). -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Spec

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody3Spec
open EvmAsm.Codegen.AmsterdamBlobGasPrice

set_option maxRecDepth 8000

private theorem backedgeScratch_to_owns
    (v5 v6 v7 v28 v29 v30 v31 : Word) (R : Assertion) :
    ∀ h,
      ((.x5 ↦ᵣ v5) ** ((.x6 ↦ᵣ v6) ** ((.x7 ↦ᵣ v7) **
        ((.x28 ↦ᵣ v28) ** ((.x29 ↦ᵣ v29) **
          ((.x30 ↦ᵣ v30) ** ((.x31 ↦ᵣ v31) ** R))))))) h →
      ((regOwn .x5) ** ((regOwn .x6) ** ((regOwn .x7) **
        ((regOwn .x28) ** ((regOwn .x29) **
          ((regOwn .x30) ** ((regOwn .x31) ** R))))))) h := by
  intro h hh
  exact sepConj_mono (regIs_to_regOwn .x5 v5)
    (sepConj_mono (regIs_to_regOwn .x6 v6)
      (sepConj_mono (regIs_to_regOwn .x7 v7)
        (sepConj_mono (regIs_to_regOwn .x28 v28)
          (sepConj_mono (regIs_to_regOwn .x29 v29)
            (sepConj_mono (regIs_to_regOwn .x30 v30)
              (sepConj_mono (regIs_to_regOwn .x31 v31)
                (fun _ h' => h'))))))) h hh

@[reducible] def taylorRoundBackedgeDivState
    (iVal excess a0 a1 a2 a3 a4 a5 : Word) : Word × Word × Word :=
  let z0 := divst (taylorDW * iVal) (0 : Word) (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (0 : Word) 64
  let z1 := divst (taylorDW * iVal) z0.1 (roundP4 a0 a1 a2 a3 a4 excess)
    (0 : Word) 64
  let z2 := divst (taylorDW * iVal) z1.1 (roundP3 a0 a1 a2 a3 excess)
    (0 : Word) 64
  let z3 := divst (taylorDW * iVal) z2.1 (roundP2 a0 a1 a2 excess)
    (0 : Word) 64
  let z4 := divst (taylorDW * iVal) z3.1 (roundP1 a0 a1 excess)
    (0 : Word) 64
  let z5 := divst (taylorDW * iVal) z4.1 (roundP0 a0 excess)
    (0 : Word) 64
  z5

private theorem signExtend12_zero_backedge :
    signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

@[reducible] private def backedgeFixedPost
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) **
  (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
  (.x18 ↦ᵣ (iVal + signExtend12 (1 : BitVec 12))) **
  (.x19 ↦ᵣ PB) ** (.x20 ↦ᵣ AB) ** (.x21 ↦ᵣ outPtr) **
  (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
  frameSlotsSaved priceFrame newSp vals

@[reducible] private def backedgeScratchPost
    (iVal excess PB : Word) (a0 a1 a2 a3 a4 a5 : Word) : Assertion :=
  (.x5 ↦ᵣ (taylorDW * iVal)) **
  (.x6 ↦ᵣ (taylorRoundBackedgeDivState iVal excess a0 a1 a2 a3 a4 a5).1) **
  (.x7 ↦ᵣ (taylorRoundBackedgeDivState iVal excess a0 a1 a2 a3 a4 a5).2.1) **
  (.x28 ↦ᵣ (taylorRoundBackedgeDivState iVal excess a0 a1 a2 a3 a4 a5).2.2) **
  (.x29 ↦ᵣ (0 : Word)) **
  (.x30 ↦ᵣ ((PB + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))) **
  (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12)))

@[reducible] private def backedgeOwnedScratchPost : Assertion :=
  regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 **
    (regOwn .x28 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31))))))

@[reducible] private def backedgeMemoryPost
    (newSp AB PB iVal excess : Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  cellsOf (PB + signExtend12 (0 : BitVec 12))
      (taylorRoundBackedgeQuotient iVal excess a0 a1 a2 a3 a4 a5) **
  cellsOf (AB + signExtend12 (0 : BitVec 12)) [a0, a1, a2, a3, a4, a5] **
  cellsOf (newSp + signExtend12 (160 : BitVec 12) + signExtend12 (0 : BitVec 12))
      (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) ** FR

@[reducible] private def backedgeConcretePost
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  backedgeFixedPost newSp excess outPtr iVal AB PB vals **
  (backedgeScratchPost iVal excess PB a0 a1 a2 a3 a4 a5 **
    (backedgeMemoryPost newSp AB PB iVal excess
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR ** (.x0 ↦ᵣ (0 : Word))))

private theorem backedge_post_to_concrete
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (AB PB : Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) :
    ∀ h,
      taylorRoundBackedgePost newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR h →
      backedgeConcretePost newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR h := by
  intro h hh
  simp only [taylorRoundBackedgePost, roundQBACK, QBACKP,
    EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.QBACKP,
    backedgeConcretePost, backedgeFixedPost, backedgeScratchPost,
    backedgeMemoryPost, taylorRoundBackedgeDivState,
    taylorRoundBackedgeQuotient, taylorRoundBackedgeSum,
    AmsterdamBlobGasPriceDivisionBridge.divstSix, cellsOf_six,
    signExtend12_zero_backedge, signExtend12_8,
    signExtend12_16, signExtend12_24, signExtend12_32, signExtend12_40,
    EvmAsm.Rv64.AddrNorm.word_add_zero] at hh ⊢
  xperm_hyp hh

@[reducible] private def backedgeOwnedPost
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
  (FR : Assertion) : Assertion :=
  backedgeFixedPost newSp excess outPtr iVal AB PB vals **
  (backedgeOwnedScratchPost **
    (backedgeMemoryPost newSp AB PB iVal excess
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR **
      (.x0 ↦ᵣ (0 : Word))))

private theorem backedge_scratch_to_owned
    (iVal excess PB : Word) (a0 a1 a2 a3 a4 a5 : Word)
    (R : Assertion) :
    ∀ h,
      (backedgeScratchPost iVal excess PB a0 a1 a2 a3 a4 a5 ** R) h →
      (backedgeOwnedScratchPost ** R) h := by
  intro h hh
  simp only [backedgeScratchPost, backedgeOwnedScratchPost, sepConj_assoc'] at hh ⊢
  exact backedgeScratch_to_owns
    (taylorDW * iVal)
    (taylorRoundBackedgeDivState iVal excess a0 a1 a2 a3 a4 a5).1
    (taylorRoundBackedgeDivState iVal excess a0 a1 a2 a3 a4 a5).2.1
    (taylorRoundBackedgeDivState iVal excess a0 a1 a2 a3 a4 a5).2.2
    (0 : Word)
    ((PB + signExtend12 (0 : BitVec 12)) + signExtend12 (-8 : BitVec 12))
    (lcnt 5 + signExtend12 (-1 : BitVec 12)) R h hh

private theorem backedge_concrete_to_owned
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (AB PB : Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) :
    ∀ h,
      backedgeConcretePost newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR h →
      backedgeOwnedPost newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR h := by
  intro h hh
  simp only [backedgeConcretePost, backedgeOwnedPost] at hh ⊢
  exact sepConj_mono_right
    (backedge_scratch_to_owned iVal excess PB a0 a1 a2 a3 a4 a5
      (backedgeMemoryPost newSp AB PB iVal excess
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR ** (.x0 ↦ᵣ (0 : Word)))) h hh

theorem taylor_round_backedge_to_parity
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) :
    ∀ h,
      taylorRoundBackedgePost newSp excess outPtr iVal
        (parityBuffer j evenBase oddBase)
        (parityBuffer j oddBase evenBase) vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR h →
      (taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
        (iVal + signExtend12 (1 : BitVec 12)) evenBase oddBase
        (taylorRoundBackedgeQuotient iVal excess a0 a1 a2 a3 a4 a5)
        [a0, a1, a2, a3, a4, a5]
      (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR **
        (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hh
  have hc := backedge_post_to_concrete newSp excess outPtr iVal vals
    (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase)
    a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR h hh
  have ho := backedge_concrete_to_owned newSp excess outPtr iVal vals
    (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase)
    a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR h hc
  simp only [backedgeOwnedPost, backedgeFixedPost, backedgeMemoryPost,
    taylorLoopInvParityAt, taylorRoundBackedgeQuotient,
    taylorRoundBackedgeSum, AmsterdamBlobGasPriceDivisionBridge.divstSix,
    cellsOf_six, signExtend12_zero_backedge,
    EvmAsm.Rv64.AddrNorm.word_add_zero] at ho ⊢
  rw [parityBuffer_succ_swap, parityBuffer_succ_swap'] at ⊢
  xperm_hyp ho

#print axioms taylor_round_backedge_to_parity

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
