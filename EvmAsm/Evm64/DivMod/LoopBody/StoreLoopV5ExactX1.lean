/-
  EvmAsm.Evm64.DivMod.LoopBody.StoreLoopV5ExactX1

  Exact-x1 variants of the v5 store-loop loop-body bricks: frame `.x1 ↦ᵣ raVal`
  onto `divK_store_loop_{j0,jgt0}_v5_spec_within_noNop` (StoreLoopV5).  Mirror of
  `divK_store_loop_{j0,jgt0}_v4_spec_within_noNop_exact_x1` (StoreLoop).  Needed
  by the v5 n=2 call-path loop bodies that thread the concrete caller return
  address through the store-loop exit / loop-back.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.StoreLoopV5

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Store q[0] + loop exit at j=0 over `sharedDivModCodeNoNop_v5`, with exact
    caller-framed `x1` carried through. -/
theorem divK_store_loop_j0_v5_spec_within_noNop_exact_x1
    (sp qHat v5Old v7Old qOld raVal : Word)
    (base : Word) :
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    let j' := (0 : Word) + signExtend12 4095
    cpsTripleWithin 6 (base + storeLoopOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (((.x9 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
        (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (qAddr ↦ₘ qOld)) ** (.x1 ↦ᵣ raVal))
      (((.x9 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
        (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) **
        (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qHat)) ** (.x1 ↦ᵣ raVal)) := by
  intro qAddr j'
  have hStore := divK_store_loop_j0_v5_spec_within_noNop sp qHat v5Old v7Old qOld base
  dsimp only [] at hStore
  exact cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) hStore

/-- Store q[j] + loop back at j>0 over `sharedDivModCodeNoNop_v5`, with exact
    caller-framed `x1` carried through. -/
theorem divK_store_loop_jgt0_v5_spec_within_noNop_exact_x1
    (sp j qHat v5Old v7Old qOld raVal : Word)
    (base : Word)
    (hj_pos : BitVec.slt (j + signExtend12 4095) 0 = false) :
    let jX8 := j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - jX8
    let j' := j + signExtend12 4095
    cpsTripleWithin 6 (base + storeLoopOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v5 base)
      (((.x9 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
        (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (qAddr ↦ₘ qOld)) ** (.x1 ↦ᵣ raVal))
      (((.x9 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
        (.x5 ↦ᵣ jX8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        (qAddr ↦ₘ qHat)) ** (.x1 ↦ᵣ raVal)) := by
  intro jX8 qAddr j'
  have hStore := divK_store_loop_jgt0_v5_spec_within_noNop sp j qHat v5Old v7Old qOld base hj_pos
  dsimp only [] at hStore
  exact cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) hStore

end EvmAsm.Evm64
