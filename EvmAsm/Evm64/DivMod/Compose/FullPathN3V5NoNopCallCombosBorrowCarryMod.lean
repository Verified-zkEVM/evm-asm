/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallCombosBorrowCarryMod

  Borrow-dispatched call-first n=3 v5 two-iteration loop combos: the j=1 first
  call iteration from the loop source and the call×call full path, each taking the
  per-iteration second-addback carry only CONDITIONALLY on that iteration's
  runtime mulsub borrow.  Thin variants of `divK_loop_n3_call_{j1_from_source,call}_..._v5_noNop`
  (FullPathN3V5NoNopCallCombos) composing the borrowCarry exact-jN bodies (#7529)
  through the same version-agnostic source-pre / j1→j0 bridges.  The guarded carry
  hypotheses match the `loopN3SelectedBorrowCarryV5` bundle obligations (#7526),
  discharged from shape in #7527.  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallExactBorrowCarryMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- First n=3 call iteration (j=1) from the loop source, carry required only on
    the runtime borrow branch. -/
theorem divK_loop_n3_call_j1_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_borrow :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
      (let qHat := divKTrialCallV5QHat u3 u2 v2
       let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
       let c3 := ms.2.2.2.2
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
       let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
       carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0)) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV5QHat u3 u2 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 u2)
        (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))) := by
  have J1 := divK_loop_body_n3_call_j1_exact_loopIterScratch_v5_noNop_modCode_borrowCarry sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_borrow
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_weaken
    (loopN3PreWithScratchV4NoX1_to_call_j1_pre
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem)
    (fun h hp => hp)
    J1f

/-- Full n=3 call×call path from the loop source, carry required only on each
    iteration's runtime borrow branch. -/
theorem divK_loop_n3_call_call_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u3 v2)
    (hcarry2_borrow_1 :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
      (let qHat := divKTrialCallV5QHat u3 u2 v2
       let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
       let c3 := ms.2.2.2.2
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
       let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
       carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0))
    (hbltu_0 :
      BitVec.ult
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2_borrow_0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
          v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      (let qHat := divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2
       let ms := mulsubN4 qHat v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1
       let c3 := ms.2.2.2.2
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
       let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (r1.2.2.2.2.1 - c3) v0 v1 v2 v3
       carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0)) :
    let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (234 + 234) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 r1.2.2.1)
        (divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 v2
          (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem))
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_n3_call_j1_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_1 hcarry2_borrow_1
  subst r1
  subst uBase1
  subst qAddr1
  have J0 := divK_loop_body_n3_call_j0_exact_loopIterScratch_v5_noNop_modCode_borrowCarry sp base
    (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal
    (base + div128CallRetOff) v2 (divKTrialCallV5DLo v2)
    (divKTrialCallV5Un0 u2) (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
    halign hbltu_0 hcarry2_borrow_0
  have J0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN3CallScratchNoX1_j1_to_call_j0_pre
      sp base (divKTrialCallV5QHat u3 u2 v2) (divKTrialCallV5DLo v2)
      (divKTrialCallV5Un0 u2) (divKTrialCallV5ScratchOut u3 u2 v2 scratchMem)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q0Old raVal)
    J1 J0f

end EvmAsm.Evm64
