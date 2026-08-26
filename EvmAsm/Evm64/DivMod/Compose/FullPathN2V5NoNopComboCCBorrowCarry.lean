/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCBorrowCarry

  Borrow-dispatched variant of the n=2 call×call two-digit prefix
  (FullPathN2V5NoNopComboCC): each call digit's carry2nz is required only
  conditionally on that digit's runtime borrow.  Chains the j=2 source
  borrowCarry (#7434) with the j=1 body borrowCarry (#7433) via the same
  cross-digit pre-bridge.  The conditional hypotheses are dischargeable from
  shape via `callAddbackCarry2NzV5_of_borrow_n2` (#7431).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopSourceBorrowCarry
public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallIterBorrowCarry

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=2 call×call prefix, carry2nz required only on each digit's
    runtime-borrow branch. -/
theorem divK_loop_n2_call_call_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u2 v1)
    (hcarry2_borrow_2 :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3) →
      callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      BitVec.ult
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2_borrow_1 :
      let r2 := iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r2.2.2.2.2.1
        (mulsubN4_c3 (divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1)
          v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1) →
      callAddbackCarry2NzV5 v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) :
    let r2 := iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let qHat1 := divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1
    let dLo1 := divKTrialCallV5DLo v1
    let divUn01 := divKTrialCallV5Un0 r2.2.1
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (234 + 234) (base + loopBodyOff) (base + loopBodyOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        qHat1 dLo1 divUn01 scratch1
        v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
          (qAddr2 ↦ₘ r2.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) := by
  intro r2 qHat1 dLo1 divUn01 scratch2 scratch1 uBase2 qAddr2 uBase0 qAddr0
  have J2 := divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_2 hcarry2_borrow_2
  subst r2
  subst qHat1
  subst dLo1
  subst divUn01
  subst scratch2
  subst scratch1
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_call_j1_exact_loopIterScratch_v5_noNop_borrowCarry sp base
    (2 : Word)
    ((2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q1Old raVal
    (base + div128CallRetOff) v1 (divKTrialCallV5DLo v1)
    (divKTrialCallV5Un0 u1) (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
    halign hbltu_1 hcarry2_borrow_1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2CallScratchNoX1_j2_to_call_j1_pre
      sp base (divKTrialCallV5QHat u2 u1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 u1) (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal)
    J2 J1f

end EvmAsm.Evm64
