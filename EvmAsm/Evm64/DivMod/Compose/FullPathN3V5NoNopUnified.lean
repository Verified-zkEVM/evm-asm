/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnified

  v5/no-NOP n=3 unified two-iteration loop dispatch over `divCode_noNop_v5`:
  `divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry`
  — `by_cases` on the two per-iteration borrow flags selecting among the four
  combos (#7517 call_call/call_max, #7518 max_max/max_call) and exposing the
  unified post `loopN3UnifiedPostV5NoX1`.  Mirror of the v4 analog
  (`FullPathN3V4NoNopMaxCall` :447); the `iterN3V5`-shaped `_selectedCarryR1`
  sibling (v4 :578) is deferred, and the LEGACY `Carry2NzAll` surface (v4 :298) is intentionally NOT
  ported — it is the FALSE universal-carry placeholder; the v5 lane discharges
  the selected per-branch carry from shape instead.  The v5 call branches consume
  the non-irreducible `loopBodyN3CallAddbackCarry2NzV5` (defeq to the combos'
  inline carry); the max branches keep the shared `isAddbackCarry2NzN3Max`.
  Bead `evm-asm-wbc4i.9.3.3.2.4`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallCombos
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopMaxCombos
public import EvmAsm.Evm64.DivMod.Spec.N3V5DigitStepIter

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unified n=3 v5 no-`x1` loop postcondition (4-case on the two borrow flags).
    V5 mirror of `loopN3UnifiedPostV4NoX1` with the `divKTrialCallV5*` trial
    outputs. -/
@[irreducible]
def loopN3UnifiedPostV5NoX1 (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  match bltu_1, bltu_0 with
  | false, false =>
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
      u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratchUn0) **
    (sp + signExtend12 3936 ↦ₘ scratchMem) **
    ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
     (qAddr1 ↦ₘ r1.1))
  | false, true =>
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    loopIterPostN3CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
      (divKTrialCallV5DLo v2)
      (divKTrialCallV5Un0 r1.2.2.1)
      (divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 v2 scratchMem)
      v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
     (qAddr1 ↦ₘ r1.1))
  | true, false =>
    let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
      u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v2) **
    (sp + signExtend12 3952 ↦ₘ (divKTrialCallV5DLo v2)) **
    (sp + signExtend12 3944 ↦ₘ (divKTrialCallV5Un0 u2)) **
    (sp + signExtend12 3936 ↦ₘ (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)) **
    ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
     (qAddr1 ↦ₘ r1.1))
  | true, true =>
    let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    loopIterPostN3CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
      (divKTrialCallV5DLo v2)
      (divKTrialCallV5Un0 r1.2.2.1)
      (divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 v2
        (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem))
      v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
     (qAddr1 ↦ₘ r1.1))

/-- n=3 v5 call-iteration second-addback carry obligation (non-irreducible:
    definitionally the inline carry form the v5 call combos consume).  V5 mirror
    of `loopBodyN3CallAddbackCarry2NzV4`. -/
def loopBodyN3CallAddbackCarry2NzV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV5QHat u3 u2 v2
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
  carry = 0 →
    addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0

/-- Selected-carry n=3 v5 unified loop dispatch: callers supply only the carry
    fact selected by each concrete branch (no false universal `Carry2NzAll`). -/
theorem divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      else
        isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_j0 :
      match bltu_1 with
      | false =>
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      | true =>
        let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_1 <;> cases bltu_0
  · have hb1 : ¬BitVec.ult u3 v2 := by rw [← hbltu_1]; decide
    have hb0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; rw [← hbltu_0]; decide
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV5NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_max_max_from_source_exact_loopIterScratch_v5_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : ¬BitVec.ult u3 v2 := by rw [← hbltu_1]; decide
    have hb0 : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; exact hbltu_0.symm
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV5NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_max_call_from_source_exact_loopIterScratch_v5_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : BitVec.ult u3 v2 := hbltu_1.symm
    have hb0 :
        ¬BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; rw [← hbltu_0]; decide
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV5NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_call_max_from_source_exact_loopIterScratch_v5_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : BitVec.ult u3 v2 := hbltu_1.symm
    have hb0 :
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; exact hbltu_0.symm
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        unfold loopN3UnifiedPostV5NoX1
        simp only at hp ⊢
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      (divK_loop_n3_call_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)

end EvmAsm.Evm64
