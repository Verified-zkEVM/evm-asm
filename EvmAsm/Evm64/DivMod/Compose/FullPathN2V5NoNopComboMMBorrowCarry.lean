/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMBorrowCarry

  Borrow-dispatched variant of the n=2 max×max two-digit prefix
  (FullPathN2V5NoNopCombo2:212): each max digit's `isAddbackCarry2NzN2Max` is
  required only conditionally on that digit's runtime borrow.  Chains the j=2 max
  source borrowCarry (#7439) with the j=1 max body borrowCarry (#7438).  Mirror
  of the call×call prefix borrowCarry (#7435) with max digits.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxSourceBorrowCarry
public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxIterBorrowCarry

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=2 max×max prefix, carry required only on each digit's
    runtime-borrow branch. -/
theorem divK_loop_n2_max_max_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hcarry2_borrow_2 :
      BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r2.2.2.1 v1)
    (hcarry2_borrow_1 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r2.2.2.2.2.1
        (mulsubN4_c3 (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) :
    let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 152) (base + loopBodyOff) (base + loopBodyOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
          (qAddr2 ↦ₘ r2.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) := by
  intro r2 uBase2 qAddr2 uBase0 qAddr0
  have J2 := divK_loop_n2_max_j2_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_2 hcarry2_borrow_2
  subst r2
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_max_j1_exact_loopIterScratch_v5_noNop_borrowCarry sp base
    (2 : Word)
    ((2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    hbltu_1 hcarry2_borrow_1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2MaxScratchX1_j2_to_max_j1_pre
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal)
    J2 J1f

end EvmAsm.Evm64
